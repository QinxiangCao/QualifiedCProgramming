From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.undef_full d_pre (k_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  (Int64Array.seg d_pre 0 (j + 1 ) (app (initialized) ((cons (4557430888798830399) ((@nil Z))))) )
  **  (Int64Array.undef_seg d_pre (j + 1 ) (k_pre + 1 ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 j initialized )
  **  (Int64Array.undef_seg d_pre j (k_pre + 1 ) )
|--
  “ (4557430888798830399 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 4557430888798830399) ”
.

Definition solver_safety_wit_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 j initialized )
  **  (Int64Array.undef_seg d_pre j (k_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 j initialized )
  **  (Int64Array.undef_seg d_pre j (k_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  ((( &( "mind" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "off" ) )) # Int64  |-> (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0))
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  ((( &( "off" ) )) # Int64  |->_)
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mind" ) )) # Int64  |-> 0)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "off" ) )) # Int64  |-> (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0))
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((INT64_MIN) <= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
.

Definition solver_safety_wit_12 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "candB" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((mind + off ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (mind + off )) ”
.

Definition solver_safety_wit_13 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
).

Definition solver_safety_wit_13_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |->_)
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((INT64_MIN) <= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
.

Definition solver_safety_wit_14 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "candB" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((mind + off ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (mind + off )) ”
.

Definition solver_safety_wit_15 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ (4557430888798830399 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 4557430888798830399) ”
.

Definition solver_safety_wit_16 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (4557430888798830399 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 4557430888798830399) ”
.

Definition solver_safety_wit_17 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
).

Definition solver_safety_wit_17_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
.

Definition solver_safety_wit_18 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ (((Znth (Znth i prog 0) dp 0) + off ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (Znth i prog 0) dp 0) + off )) ”
.

Definition solver_safety_wit_19 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
.

Definition solver_safety_wit_20 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "viaHot" ) )) # Int64  |->_)
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (((Znth (Znth i prog 0) dp 0) + off ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (Znth i prog 0) dp 0) + off )) ”
.

Definition solver_safety_wit_21 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
).

Definition solver_safety_wit_21_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_21_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
.

Definition solver_safety_wit_22 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
).

Definition solver_safety_wit_22_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_22_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
.

Definition solver_safety_wit_23 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
).

Definition solver_safety_wit_23_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_23_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
.

Definition solver_safety_wit_24 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
).

Definition solver_safety_wit_24_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
.

Definition solver_safety_wit_25 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
).

Definition solver_safety_wit_25_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
.

Definition solver_safety_wit_26 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
).

Definition solver_safety_wit_26_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((INT64_MIN) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
.

Definition solver_safety_wit_27 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
.

Definition solver_safety_wit_28 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
).

Definition solver_safety_wit_28_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_28_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> (((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
.

Definition solver_safety_wit_29 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
).

Definition solver_safety_wit_29_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_29_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
.

Definition solver_safety_wit_30 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
.

Definition solver_safety_wit_31 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
).

Definition solver_safety_wit_31_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_31_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
|--
  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
.

Definition solver_safety_wit_32 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "ny" ) )) # Int64  |->_)
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  ((( &( "candB" ) )) # Int64  |-> ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "costA" ) )) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (IntArray.full a_pre n_pre prog )
  **  ((( &( "y" ) )) # Int  |-> (Znth (i - 1 ) prog 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth i prog 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
.

Definition solver_safety_wit_33 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "costA" ) )) # Int64  |-> costA)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  ((( &( "candB" ) )) # Int64  |-> candB)
  **  ((( &( "ny" ) )) # Int64  |-> ny)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ False ”
.

Definition solver_safety_wit_34 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "costA" ) )) # Int64  |-> costA)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  ((( &( "candB" ) )) # Int64  |-> candB)
  **  ((( &( "ny" ) )) # Int64  |-> ny)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ False ”
.

Definition solver_safety_wit_35 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> ny)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH45 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH46 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> ny)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_37 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_38 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_39 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH45 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH46 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH44 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_41 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_42 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH44 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_43 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_44 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "cold" ) )) # Ptr  |-> cold_pre)
  **  ((( &( "hot" ) )) # Ptr  |-> hot_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "off" ) )) # Int64  |-> off)
  **  ((( &( "mind" ) )) # Int64  |-> mind)
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((mind + off ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (mind + off )) ”
.

Definition solver_entail_wit_1 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.undef_full d_pre (k_pre + 1 ) )
|--
  EX (initialized: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (k_pre + 1 )) ”
  &&  “ ((Zlength (initialized)) = 0) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < 0)) -> ((Znth q_3 initialized 0) = 4557430888798830399)) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 0 initialized )
  **  (Int64Array.undef_seg d_pre 0 (k_pre + 1 ) )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < 0)) -> ((Znth q_3 (@nil Z) 0) = 4557430888798830399)) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 < 0)) -> ((Znth q_3 (@nil Z) 0) = 4557430888798830399))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i prog 0)) /\ ((Znth i prog 0) <= k_pre)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs 0)) /\ ((Znth i_2 hot_costs 0) <= (Znth i_2 cold_costs 0))) /\ ((Znth i_2 cold_costs 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_2 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized_2: (@list Z)) (j: Z) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized_2)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized_2 0) = 4557430888798830399))),
  (Int64Array.seg d_pre 0 (j + 1 ) (app (initialized_2) ((cons (4557430888798830399) ((@nil Z))))) )
  **  (Int64Array.undef_seg d_pre (j + 1 ) (k_pre + 1 ) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (initialized: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (k_pre + 1 )) ”
  &&  “ ((Zlength (initialized)) = (j + 1 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < (j + 1 ))) -> ((Znth q_3 initialized 0) = 4557430888798830399)) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 (j + 1 ) initialized )
  **  (Int64Array.undef_seg d_pre (j + 1 ) (k_pre + 1 ) )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (initialized_2: (@list Z)) (j: Z) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized_2)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized_2 0) = 4557430888798830399))),
  TT && emp 
|--
  “ ((Zlength ((app (initialized_2) ((cons (4557430888798830399) ((@nil Z))))))) = (j + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (initialized_2: (@list Z)) (j: Z) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized_2)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized_2 0) = 4557430888798830399))),
  ((Zlength ((app (initialized_2) ((cons (4557430888798830399) ((@nil Z))))))) = (j + 1 ))
.

Definition solver_entail_wit_3 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 < j)) -> ((Znth q_6 initialized 0) = 4557430888798830399))),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (1 <= (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) <= (1 * 1000000000 )) ”
  &&  “ (((-1) * 1000000000 ) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (1 <= (0 + (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((0 + (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) ) <= (1 * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-1) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (1 * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs 1 dp (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) 0 ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 < j)) -> ((Znth q_6 initialized 0) = 4557430888798830399))),
  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (1 <= (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) <= (1 * 1000000000 )) ”
  &&  “ (((-1) * 1000000000 ) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (1 <= (0 + (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((0 + (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) ) <= (1 * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-1) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (1 * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs 1 dp (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0) 0 ) ”
  &&  (Int64Array.full d_pre (k_pre + 1 ) dp )
).

Definition solver_entail_wit_4_1 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  EX (dp_2: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp_2)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp_2 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= (i * 1000000000 ))))) ”
  &&  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp_2 0) < 4557430888798830399) -> ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (((Znth (Znth i prog 0) dp_2 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth (Znth i prog 0) dp_2 0) < 4557430888798830399) ”
  &&  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) = (((Znth (Znth i prog 0) dp_2 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) = ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp_2 ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ) ”
  &&  “ (((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp_2 0)) /\ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp_2)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) )) ”
  &&  “ (((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp_2 0)) /\ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp_2)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  TT && emp 
|--
  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ) ”
  &&  “ ((i + 1 ) <= (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0)) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ))
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )
.

Definition solver_entail_wit_4_1_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((i + 1 ) <= (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ))
.

Definition solver_entail_wit_4_1_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 ))
.

Definition solver_entail_wit_4_1_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))
.

Definition solver_entail_wit_4_1_split_goal_6 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 ))
.

Definition solver_entail_wit_4_1_split_goal_7 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ))
.

Definition solver_entail_wit_4_1_split_goal_8 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000)
.

Definition solver_entail_wit_4_1_split_goal_9 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
.

Definition solver_entail_wit_4_1_split_goal_10 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_4_1_split_goal_11 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_4_2 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  EX (dp_2: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp_2)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp_2 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= (i * 1000000000 ))))) ”
  &&  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp_2 0) < 4557430888798830399) -> ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (((Znth (Znth i prog 0) dp_2 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth (Znth i prog 0) dp_2 0) < 4557430888798830399) ”
  &&  “ ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) = (((Znth (Znth i prog 0) dp_2 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) = ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp_2 ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ) ”
  &&  “ (((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp_2 0)) /\ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp_2)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) )) ”
  &&  “ (((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp_2 0)) /\ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp_2)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  TT && emp 
|--
  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  “ (((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ) ”
  &&  “ ((i + 1 ) <= (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ))
.

Definition solver_entail_wit_4_2_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) ))
.

Definition solver_entail_wit_4_2_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )
.

Definition solver_entail_wit_4_2_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((i + 1 ) <= (((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ))
.

Definition solver_entail_wit_4_2_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 ))
.

Definition solver_entail_wit_4_2_split_goal_6 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (((-(i + 1 )) * 1000000000 ) <= ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ))
.

Definition solver_entail_wit_4_2_split_goal_7 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))
.

Definition solver_entail_wit_4_2_split_goal_8 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 ))
.

Definition solver_entail_wit_4_2_split_goal_9 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))
.

Definition solver_entail_wit_4_2_split_goal_10 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000)
.

Definition solver_entail_wit_4_2_split_goal_11 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
.

Definition solver_entail_wit_4_2_split_goal_12 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_4_2_split_goal_13 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) < ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp 0)) /\ ((Znth q_6 dp 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_4_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp_2: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp_2 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp_2 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp_2 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
  ||
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
.

Definition solver_entail_wit_4_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp_2: (@list Z)) (i: Z) (PreH1 : ((((Znth (Znth i prog 0) dp_2 0) + off ) + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) >= ((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ))) (PreH2 : ((Znth (Znth i prog 0) dp_2 0) < 4557430888798830399)) (PreH3 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH13 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH17 : ((Znth 0 dp_2 0) = 0)) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000 ))) (PreH20 : (((-i) * 1000000000 ) <= mind)) (PreH21 : (mind <= 0)) (PreH22 : (i <= (mind + off ))) (PreH23 : ((mind + off ) <= (i * 1000000000 ))) (PreH24 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
  ||
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
.

Definition solver_entail_wit_4_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp_2 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH12 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp_2 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
  ||
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
.

Definition solver_entail_wit_4_6 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp_2 0) >= 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH12 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp_2 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
  ||
  (EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i prog 0) = (Znth i prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= (Znth i prog 0)) ”
  &&  “ ((Znth i prog 0) <= k_pre) ”
  &&  “ (1 <= (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (i - 1 ) prog 0) <= k_pre) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) = (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0)) ”
  &&  “ ((Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ (((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) )) ”
  &&  “ ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= ((mind + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth (Znth i prog 0) dp 0) < 4557430888798830399) -> (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) <= (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) = (((Znth (Znth i prog 0) dp 0) + ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (Znth ((Znth i prog 0)) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) = (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) + (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind ) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) (((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) )) ”
  &&  “ ((((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) < (Znth (Znth (i - 1 ) prog 0) dp 0)) /\ ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth ((Znth (i - 1 ) prog 0)) ((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) )) (dp)) (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  “ (((((mind + off ) + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) - (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) ) >= (Znth (Znth (i - 1 ) prog 0) dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp (off + (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0) ) mind )) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp ))
.

Definition solver_entail_wit_5_1 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp_2)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ (ny <= 0) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off ny ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ ((Znth 0 (replace_Znth (x) ((candB - off )) (dp_2)) 0) = 0) ”
  &&  “ ((Zlength ((replace_Znth (x) ((candB - off )) (dp_2)))) = (k_pre + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_1_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Znth 0 (replace_Znth (x) ((candB - off )) (dp_2)) 0) = 0)
.

Definition solver_entail_wit_5_1_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Zlength ((replace_Znth (x) ((candB - off )) (dp_2)))) = (k_pre + 1 ))
.

Definition solver_entail_wit_5_1_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_1_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_2 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp_2)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ (ny <= 0) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off ny ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ ((Znth 0 (replace_Znth (y) ((candB - off )) (dp_2)) 0) = 0) ”
  &&  “ ((Zlength ((replace_Znth (y) ((candB - off )) (dp_2)))) = (k_pre + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_2_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Znth 0 (replace_Znth (y) ((candB - off )) (dp_2)) 0) = 0)
.

Definition solver_entail_wit_5_2_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Zlength ((replace_Znth (y) ((candB - off )) (dp_2)))) = (k_pre + 1 ))
.

Definition solver_entail_wit_5_2_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_2_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_3 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp_2)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ ((Znth 0 (replace_Znth (x) ((candB - off )) (dp_2)) 0) = 0) ”
  &&  “ ((Zlength ((replace_Znth (x) ((candB - off )) (dp_2)))) = (k_pre + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_3_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_3_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Znth 0 (replace_Znth (x) ((candB - off )) (dp_2)) 0) = 0)
.

Definition solver_entail_wit_5_3_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Zlength ((replace_Znth (x) ((candB - off )) (dp_2)))) = (k_pre + 1 ))
.

Definition solver_entail_wit_5_3_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_3_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_4 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp_2)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ ((Znth 0 (replace_Znth (y) ((candB - off )) (dp_2)) 0) = 0) ”
  &&  “ ((Zlength ((replace_Znth (y) ((candB - off )) (dp_2)))) = (k_pre + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_4_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_4_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Znth 0 (replace_Znth (y) ((candB - off )) (dp_2)) 0) = 0)
.

Definition solver_entail_wit_5_4_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Zlength ((replace_Znth (y) ((candB - off )) (dp_2)))) = (k_pre + 1 ))
.

Definition solver_entail_wit_5_4_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_4_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_5 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) (replace_Znth (y) (ny) (dp_2)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ ((Znth 0 (replace_Znth (y) ((candB - off )) (dp_2)) 0) = 0) ”
  &&  “ ((Zlength ((replace_Znth (y) ((candB - off )) (dp_2)))) = (k_pre + 1 )) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_5_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0)) /\ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_5_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Znth 0 (replace_Znth (y) ((candB - off )) (dp_2)) 0) = 0)
.

Definition solver_entail_wit_5_5_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  ((Zlength ((replace_Znth (y) ((candB - off )) (dp_2)))) = (k_pre + 1 ))
.

Definition solver_entail_wit_5_5_split_goal_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_5_split_goal_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH11 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog 0))) (PreH15 : (y = (Znth (i - 1 ) prog 0))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x <> y)) (PreH21 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH25 : ((Znth 0 dp_2 0) = 0)) (PreH26 : (i <= (off - costA ))) (PreH27 : ((off - costA ) <= (i * 1000000000 ))) (PreH28 : ((i + 1 ) <= off)) (PreH29 : (off <= ((i + 1 ) * 1000000000 ))) (PreH30 : (((-i) * 1000000000 ) <= mind)) (PreH31 : (mind <= 0)) (PreH32 : (i <= (mind + (off - costA ) ))) (PreH33 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH34 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH35 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH37 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH39 : (ny = (candB - off ))) (PreH40 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH41 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH42 : ((i + 1 ) <= (ny + off ))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH45 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH46 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_6 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_6_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_6_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_6_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_7 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_7_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_7_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_7_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_8 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_8_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_8_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_8_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH44 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_entail_wit_5_9 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp_2 )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  EX (dp: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ ((i + 1 ) <= (mind + off )) ”
  &&  “ ((mind + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  TT && emp 
|--
  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 ))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_9_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 0) = 4557430888798830399) \/ ((((-(i + 1 )) * 1000000000 ) <= (Znth q_3 dp_2 0)) /\ ((Znth q_3 dp_2 0) <= ((i + 1 ) * 1000000000 )))))
.

Definition solver_entail_wit_5_9_split_goal_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))
.

Definition solver_entail_wit_5_9_split_goal_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (dp_2: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny >= (Znth y dp_2 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog 0)) /\ ((Znth q_4 prog 0) <= k_pre)))) (PreH10 : forall (q_5: Z), (((0 <= q_5) /\ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs 0)) /\ ((Znth q_5 hot_costs 0) <= (Znth q_5 cold_costs 0))) /\ ((Znth q_5 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp_2 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_6: Z), (((0 <= q_6) /\ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_6 dp_2 0)) /\ ((Znth q_6 dp_2 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp_2 0) < 4557430888798830399) -> (candB <= (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp_2 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp_2 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off ny ))) (PreH44 : (((ny < (Znth y dp_2 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp_2)) off mind ))) (PreH45 : ((ny >= (Znth y dp_2 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp_2 off mind ))),
  forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))
.

Definition solver_return_wit_1 :=
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (Spec prog cold_costs hot_costs (mind + off ) ) ”
  &&  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full_shape d_pre (k_pre + 1 ) )
) \/
(
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (Spec prog cold_costs hot_costs (mind + off ) ) ”
  &&  (Int64Array.full_shape d_pre (k_pre + 1 ) )
).

Definition solver_return_wit_1_split_goal_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (Spec prog cold_costs hot_costs (mind + off ) ) ”
.

Definition solver_return_wit_1_split_goal_spatial :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (n_pre: Z) (k_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  (Int64Array.full_shape d_pre (k_pre + 1 ) )
.

Definition solver_partial_solve_wit_1 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 j initialized )
  **  (Int64Array.undef_seg d_pre j (k_pre + 1 ) )
|--
  “ (j <= k_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ ((Zlength (initialized)) = j) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399)) ”
  &&  (((d_pre + (j * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg d_pre (j + 1 ) (k_pre + 1 ) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 j initialized )
.

Definition solver_partial_solve_wit_2 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.seg d_pre 0 j initialized )
  **  (Int64Array.undef_seg d_pre j (k_pre + 1 ) )
|--
  “ (j > k_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ ((Zlength (initialized)) = j) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399)) ”
  &&  (((d_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i d_pre 0 0 j initialized )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_3 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (j > k_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ ((Zlength (initialized)) = j) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399)) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 prog 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre prog )
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_4 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (initialized: (@list Z)) (j: Z) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (0 <= j)) (PreH12 : (j <= (k_pre + 1 ))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (j > k_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (k_pre + 1 )) ”
  &&  “ ((Zlength (initialized)) = j) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 < j)) -> ((Znth q_3 initialized 0) = 4557430888798830399)) ”
  &&  (((cold_pre + ((Znth 0 prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth 0 prog 0) (cons (0) (cold_costs)) 0))
  **  (Int64Array.missing_i cold_pre (Znth 0 prog 0) 0 (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full d_pre j (replace_Znth (0) (0) (initialized)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_5 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((a_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) prog 0))
  **  (IntArray.missing_i a_pre (i - 1 ) 0 n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
.

Definition solver_partial_solve_wit_6 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH14 : ((Znth 0 dp 0) = 0)) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000 ))) (PreH17 : (((-i) * 1000000000 ) <= mind)) (PreH18 : (mind <= 0)) (PreH19 : (i <= (mind + off ))) (PreH20 : ((mind + off ) <= (i * 1000000000 ))) (PreH21 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i prog 0))
  **  (IntArray.missing_i a_pre i 0 n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
.

Definition solver_partial_solve_wit_7 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((hot_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (Int64Array.missing_i hot_pre (Znth i prog 0) 0 (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
.

Definition solver_partial_solve_wit_8 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((cold_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (Int64Array.missing_i cold_pre (Znth i prog 0) 0 (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
.

Definition solver_partial_solve_wit_9 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((cold_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (Int64Array.missing_i cold_pre (Znth i prog 0) 0 (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
.

Definition solver_partial_solve_wit_10 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((cold_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (cold_costs)) 0))
  **  (Int64Array.missing_i cold_pre (Znth i prog 0) 0 (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
.

Definition solver_partial_solve_wit_11 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((d_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) dp 0))
  **  (Int64Array.missing_i d_pre (Znth i prog 0) 0 (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
.

Definition solver_partial_solve_wit_12 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH15 : ((Znth 0 dp 0) = 0)) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000 ))) (PreH18 : (((-i) * 1000000000 ) <= mind)) (PreH19 : (mind <= 0)) (PreH20 : (i <= (mind + off ))) (PreH21 : ((mind + off ) <= (i * 1000000000 ))) (PreH22 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((d_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) dp 0))
  **  (Int64Array.missing_i d_pre (Znth i prog 0) 0 (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_13 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((d_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) dp 0))
  **  (Int64Array.missing_i d_pre (Znth i prog 0) 0 (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
.

Definition solver_partial_solve_wit_14 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) = (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (IntArray.full a_pre n_pre prog )
|--
  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ ((Znth i prog 0) = (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((hot_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (Int64Array.missing_i hot_pre (Znth i prog 0) 0 (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
.

Definition solver_partial_solve_wit_15 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((d_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) dp 0))
  **  (Int64Array.missing_i d_pre (Znth i prog 0) 0 (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_16 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (mind: Z) (off: Z) (dp: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i prog 0) dp 0) < 4557430888798830399)) (PreH2 : ((Znth i prog 0) <> (Znth (i - 1 ) prog 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH16 : ((Znth 0 dp 0) = 0)) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000 ))) (PreH19 : (((-i) * 1000000000 ) <= mind)) (PreH20 : (mind <= 0)) (PreH21 : (i <= (mind + off ))) (PreH22 : ((mind + off ) <= (i * 1000000000 ))) (PreH23 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind )),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ ((Znth (Znth i prog 0) dp 0) < 4557430888798830399) ”
  &&  “ ((Znth i prog 0) <> (Znth (i - 1 ) prog 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= off) ”
  &&  “ (off <= (i * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + off )) ”
  &&  “ ((mind + off ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind ) ”
  &&  (((hot_pre + ((Znth i prog 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i prog 0) (cons (0) (hot_costs)) 0))
  **  (Int64Array.missing_i hot_pre (Znth i prog 0) 0 (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (IntArray.full a_pre n_pre prog )
.

Definition solver_partial_solve_wit_17 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog 0))) (PreH13 : (y = (Znth (i - 1 ) prog 0))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x = y)) (PreH19 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH23 : ((Znth 0 dp 0) = 0)) (PreH24 : (i <= (off - costA ))) (PreH25 : ((off - costA ) <= (i * 1000000000 ))) (PreH26 : ((i + 1 ) <= off)) (PreH27 : (off <= ((i + 1 ) * 1000000000 ))) (PreH28 : (((-i) * 1000000000 ) <= mind)) (PreH29 : (mind <= 0)) (PreH30 : (i <= (mind + (off - costA ) ))) (PreH31 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH32 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH33 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH34 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH35 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (ny = (candB - off ))) (PreH37 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH38 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH39 : ((i + 1 ) <= (ny + off ))) (PreH40 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH41 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH43 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x = y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |-> (Znth y dp 0))
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_18 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog 0))) (PreH13 : (y = (Znth (i - 1 ) prog 0))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x = y)) (PreH19 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH23 : ((Znth 0 dp 0) = 0)) (PreH24 : (i <= (off - costA ))) (PreH25 : ((off - costA ) <= (i * 1000000000 ))) (PreH26 : ((i + 1 ) <= off)) (PreH27 : (off <= ((i + 1 ) * 1000000000 ))) (PreH28 : (((-i) * 1000000000 ) <= mind)) (PreH29 : (mind <= 0)) (PreH30 : (i <= (mind + (off - costA ) ))) (PreH31 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH32 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH33 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH34 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH35 : ((Znth x dp 0) < 4557430888798830399)) (PreH36 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH44 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x = y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth x dp 0) < 4557430888798830399) ”
  &&  “ (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |-> (Znth y dp 0))
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_19 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog 0))) (PreH13 : (y = (Znth (i - 1 ) prog 0))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x <> y)) (PreH19 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH23 : ((Znth 0 dp 0) = 0)) (PreH24 : (i <= (off - costA ))) (PreH25 : ((off - costA ) <= (i * 1000000000 ))) (PreH26 : ((i + 1 ) <= off)) (PreH27 : (off <= ((i + 1 ) * 1000000000 ))) (PreH28 : (((-i) * 1000000000 ) <= mind)) (PreH29 : (mind <= 0)) (PreH30 : (i <= (mind + (off - costA ) ))) (PreH31 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH32 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH33 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH34 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH35 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH36 : (ny = (candB - off ))) (PreH37 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH38 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH39 : ((i + 1 ) <= (ny + off ))) (PreH40 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH41 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH43 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x <> y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |-> (Znth y dp 0))
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_20 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog 0))) (PreH13 : (y = (Znth (i - 1 ) prog 0))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x <> y)) (PreH19 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH23 : ((Znth 0 dp 0) = 0)) (PreH24 : (i <= (off - costA ))) (PreH25 : ((off - costA ) <= (i * 1000000000 ))) (PreH26 : ((i + 1 ) <= off)) (PreH27 : (off <= ((i + 1 ) * 1000000000 ))) (PreH28 : (((-i) * 1000000000 ) <= mind)) (PreH29 : (mind <= 0)) (PreH30 : (i <= (mind + (off - costA ) ))) (PreH31 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH32 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH33 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH34 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH35 : ((Znth x dp 0) < 4557430888798830399)) (PreH36 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH44 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
  **  (Int64Array.full d_pre (k_pre + 1 ) dp )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x <> y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth x dp 0) < 4557430888798830399) ”
  &&  “ (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |-> (Znth y dp 0))
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_21 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) ((cons (0) (hot_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH44 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (ny < (Znth y dp 0)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x = y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (hot_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_22 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH37 : (ny = (candB - off ))) (PreH38 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH39 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH40 : ((i + 1 ) <= (ny + off ))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH42 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH44 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (ny < (Znth y dp 0)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x <> y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ (candB = ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Definition solver_partial_solve_wit_23 :=
forall (hot_costs: (@list Z)) (cold_costs: (@list Z)) (prog: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (cold_pre: Z) (hot_pre: Z) (d_pre: Z) (dp: (@list Z)) (i: Z) (x: Z) (y: Z) (costA: Z) (off: Z) (mind: Z) (candB: Z) (ny: Z) (PreH1 : (ny < (Znth y dp 0))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre)))) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog 0))) (PreH14 : (y = (Znth (i - 1 ) prog 0))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x <> y)) (PreH20 : (costA = (Znth (x) ((cons (0) (cold_costs))) (0)))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1 ))) (PreH24 : ((Znth 0 dp 0) = 0)) (PreH25 : (i <= (off - costA ))) (PreH26 : ((off - costA ) <= (i * 1000000000 ))) (PreH27 : ((i + 1 ) <= off)) (PreH28 : (off <= ((i + 1 ) * 1000000000 ))) (PreH29 : (((-i) * 1000000000 ) <= mind)) (PreH30 : (mind <= 0)) (PreH31 : (i <= (mind + (off - costA ) ))) (PreH32 : ((mind + (off - costA ) ) <= (i * 1000000000 ))) (PreH33 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 )))))) (PreH34 : (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) ))) (PreH35 : (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )))) (PreH36 : ((Znth x dp 0) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) (PreH38 : (ny = (candB - off ))) (PreH39 : (((-(i + 1 )) * 1000000000 ) <= ny)) (PreH40 : ((ny + off ) <= ((i + 1 ) * 1000000000 ))) (PreH41 : ((i + 1 ) <= (ny + off ))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind )) (PreH43 : (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny ))) (PreH44 : (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind ))) (PreH45 : ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind ))),
  (Int64Array.full d_pre (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
|--
  “ (ny < (Znth y dp 0)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 300000) ”
  &&  “ (n_pre = (Zlength (prog))) ”
  &&  “ (k_pre = (Zlength (cold_costs))) ”
  &&  “ (k_pre = (Zlength (hot_costs))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < n_pre)) -> ((1 <= (Znth q prog 0)) /\ ((Znth q prog 0) <= k_pre))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs 0)) /\ ((Znth q_2 hot_costs 0) <= (Znth q_2 cold_costs 0))) /\ ((Znth q_2 cold_costs 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i prog 0)) ”
  &&  “ (y = (Znth (i - 1 ) prog 0)) ”
  &&  “ (1 <= x) ”
  &&  “ (x <= k_pre) ”
  &&  “ (1 <= y) ”
  &&  “ (y <= k_pre) ”
  &&  “ (x <> y) ”
  &&  “ (costA = (Znth (x) ((cons (0) (cold_costs))) (0))) ”
  &&  “ (1 <= costA) ”
  &&  “ (costA <= 1000000000) ”
  &&  “ ((Zlength (dp)) = (k_pre + 1 )) ”
  &&  “ ((Znth 0 dp 0) = 0) ”
  &&  “ (i <= (off - costA )) ”
  &&  “ ((off - costA ) <= (i * 1000000000 )) ”
  &&  “ ((i + 1 ) <= off) ”
  &&  “ (off <= ((i + 1 ) * 1000000000 )) ”
  &&  “ (((-i) * 1000000000 ) <= mind) ”
  &&  “ (mind <= 0) ”
  &&  “ (i <= (mind + (off - costA ) )) ”
  &&  “ ((mind + (off - costA ) ) <= (i * 1000000000 )) ”
  &&  “ forall (q_3: Z), (((0 <= q_3) /\ (q_3 <= k_pre)) -> (((Znth q_3 dp 0) = 4557430888798830399) \/ ((((-i) * 1000000000 ) <= (Znth q_3 dp 0)) /\ ((Znth q_3 dp 0) <= (i * 1000000000 ))))) ”
  &&  “ (candB <= ((mind + (off - costA ) ) + (Znth (x) ((cons (0) (cold_costs))) (0)) )) ”
  &&  “ (((Znth x dp 0) < 4557430888798830399) -> (candB <= (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) ))) ”
  &&  “ ((Znth x dp 0) < 4557430888798830399) ”
  &&  “ (candB = (((Znth x dp 0) + (off - costA ) ) + (Znth (x) ((cons (0) (hot_costs))) (0)) )) ”
  &&  “ (ny = (candB - off )) ”
  &&  “ (((-(i + 1 )) * 1000000000 ) <= ny) ”
  &&  “ ((ny + off ) <= ((i + 1 ) * 1000000000 )) ”
  &&  “ ((i + 1 ) <= (ny + off )) ”
  &&  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA ) mind ) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off ny )) ”
  &&  “ (((ny < (Znth y dp 0)) /\ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) (replace_Znth (y) (ny) (dp)) off mind )) ”
  &&  “ ((ny >= (Znth y dp 0)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1 ) dp off mind )) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i d_pre y 0 (k_pre + 1 ) dp )
  **  (IntArray.full a_pre n_pre prog )
  **  (Int64Array.full cold_pre (k_pre + 1 ) (cons (0) (cold_costs)) )
  **  (Int64Array.full hot_pre (k_pre + 1 ) (cons (0) (hot_costs)) )
.

Module Type VC_Correct.


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
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Axiom proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5.
Axiom proof_of_solver_entail_wit_4_6 : solver_entail_wit_4_6.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Axiom proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Axiom proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6.
Axiom proof_of_solver_entail_wit_5_7 : solver_entail_wit_5_7.
Axiom proof_of_solver_entail_wit_5_8 : solver_entail_wit_5_8.
Axiom proof_of_solver_entail_wit_5_9 : solver_entail_wit_5_9.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
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

End VC_Correct.
