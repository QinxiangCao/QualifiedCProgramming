From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P008_26A_almost_prime_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)),
  ((( &( "p" ) )) # Int  |->_)
  **  (IntArray.full ( &( "ndiv" ) ) 3005 (repeat_Z (0) (3005)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (p: Z) (PreH1 : (p <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= (n_pre + 1 ))) (PreH6 : ((Zlength (counts)) = 3005)) (PreH7 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 (replace_Znth (m) (((Znth m counts 0) + 1 )) (counts)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "m" ) )) # Int  |-> m)
|--
  “ ((m + p ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (m + p )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "m" ) )) # Int  |-> m)
|--
  “ (((Znth m counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth m counts 0) + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ ((p + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (p: Z) (PreH1 : ((Znth p counts 0) <> 0)) (PreH2 : (p <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (2 <= p)) (PreH6 : (p <= (n_pre + 1 ))) (PreH7 : ((Zlength (counts)) = 3005)) (PreH8 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ ((p + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (counts: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)) (PreH3 : ((Zlength (counts)) = 3005)) (PreH4 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (counts: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)) (PreH3 : ((Zlength (counts)) = 3005)) (PreH4 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (1 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= (v - 1 ))) (PreH8 : (Spec (v - 1 ) cnt )) (PreH9 : ((Zlength (counts)) = 3005)) (PreH10 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_10 :=
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts 0) = 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ ((cnt + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts 0) = 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  “ ((v + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts 0) <> 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ ((v + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)),
  (IntArray.full ( &( "ndiv" ) ) 3005 (repeat_Z (0) (3005)) )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= (n_pre + 1 )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (2 - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < 2)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < 2)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps ))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)),
  TT && emp 
|--
  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x (repeat_Z (0) (3005)) 0)) /\ ((Znth x (repeat_Z (0) (3005)) 0) <= (2 - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x (repeat_Z (0) (3005)) 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < 2)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < 2)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps ))))) ”
  &&  “ ((Zlength ((repeat_Z (0) (3005)))) = 3005) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)),
  forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x (repeat_Z (0) (3005)) 0)) /\ ((Znth x (repeat_Z (0) (3005)) 0) <= (2 - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x (repeat_Z (0) (3005)) 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < 2)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < 2)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps )))))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)),
  ((Zlength ((repeat_Z (0) (3005)))) = 3005)
.

Definition solver_entail_wit_2 :=
(
forall (n_pre: Z) (ps_2: (@list Z)) (k_3: Z) (k_4: Z) (counts_2: (@list Z)) (p: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (PreH1 : ((Znth p counts_2 0) = 0)) (PreH2 : (p <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (2 <= p)) (PreH6 : (p <= (n_pre + 1 ))) (PreH7 : ((Zlength (counts_2)) = 3005)) (PreH8 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 2 ))) /\ exists (ps_2: (@list Z)), (((((Zlength (ps_2)) = (Znth x_2 counts_2 0)) /\ (NoDup ps_2 )) /\ forall (q_3: Z), ((In q_3 ps_2 ) -> ((((2 <= q_3) /\ (q_3 < p)) /\ forall (a_4: Z), forall (b_4: Z), (((2 <= a_4) /\ (q_3 = (a_4 * b_4 ))) -> (q_3 <= a_4))) /\ exists (k_3: Z), ((1 <= k_3) /\ (x_2 = (q_3 * k_3 )))))) /\ forall (q_4: Z), (((((2 <= q_4) /\ (q_4 < p)) /\ forall (a_5: Z), forall (b_5: Z), (((2 <= a_5) /\ (q_4 = (a_5 * b_5 ))) -> (q_4 <= a_5))) /\ exists (k_4: Z), ((1 <= k_4) /\ (x_2 = (q_4 * k_4 )))) -> (In q_4 ps_2 )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)) (t: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= n_pre) ”
  &&  “ forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a)) ”
  &&  “ (p <= p) ”
  &&  “ (p <= (n_pre + p )) ”
  &&  “ (1 <= t) ”
  &&  “ (p = (p * t )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < p)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < p)))) -> (In q_2 ps ))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (ps_2: (@list Z)) (k_3: Z) (k_4: Z) (counts_2: (@list Z)) (p: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (PreH1 : ((Znth p counts_2 0) = 0)) (PreH2 : (p <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (2 <= p)) (PreH6 : (p <= (n_pre + 1 ))) (PreH7 : ((Zlength (counts_2)) = 3005)) (PreH8 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 2 ))) /\ exists (ps_2: (@list Z)), (((((Zlength (ps_2)) = (Znth x_2 counts_2 0)) /\ (NoDup ps_2 )) /\ forall (q_3: Z), ((In q_3 ps_2 ) -> ((((2 <= q_3) /\ (q_3 < p)) /\ forall (a_4: Z), forall (b_4: Z), (((2 <= a_4) /\ (q_3 = (a_4 * b_4 ))) -> (q_3 <= a_4))) /\ exists (k_3: Z), ((1 <= k_3) /\ (x_2 = (q_3 * k_3 )))))) /\ forall (q_4: Z), (((((2 <= q_4) /\ (q_4 < p)) /\ forall (a_5: Z), forall (b_5: Z), (((2 <= a_5) /\ (q_4 = (a_5 * b_5 ))) -> (q_4 <= a_5))) /\ exists (k_4: Z), ((1 <= k_4) /\ (x_2 = (q_4 * k_4 )))) -> (In q_4 ps_2 )))))),
  TT && emp 
|--
  EX (t: Z),
  “ forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a)) ”
  &&  “ (p <= p) ”
  &&  “ (p <= (n_pre + p )) ”
  &&  “ (1 <= t) ”
  &&  “ (p = (p * t )) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < p)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < p)))) -> (In q_2 ps ))))) ”
  &&  emp
).

Definition solver_entail_wit_3 :=
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts_2: (@list Z)) (t_2: Z) (m: Z) (p: Z) (PreH1 : (m <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t_2)) (PreH10 : (m = (p * t_2 ))) (PreH11 : ((Zlength (counts_2)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 (replace_Znth (m) (((Znth m counts_2 0) + 1 )) (counts_2)) )
|--
  EX (counts: (@list Z)) (t: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= n_pre) ”
  &&  “ forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a)) ”
  &&  “ (p <= (m + p )) ”
  &&  “ ((m + p ) <= (n_pre + p )) ”
  &&  “ (1 <= t) ”
  &&  “ ((m + p ) = (p * t )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < (m + p ))))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < (m + p ))))) -> (In q_2 ps ))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts_2: (@list Z)) (t_2: Z) (m: Z) (p: Z) (PreH1 : (m <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t_2)) (PreH10 : (m = (p * t_2 ))) (PreH11 : ((Zlength (counts_2)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  TT && emp 
|--
  EX (t: Z),
  “ (p <= ((p * t_2 ) + p )) ”
  &&  “ (((p * t_2 ) + p ) <= (n_pre + p )) ”
  &&  “ (1 <= t) ”
  &&  “ (((p * t_2 ) + p ) = (p * t )) ”
  &&  “ ((Zlength ((replace_Znth ((p * t_2 )) (((Znth (p * t_2 ) counts_2 0) + 1 )) (counts_2)))) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x (replace_Znth ((p * t_2 )) (((Znth (p * t_2 ) counts_2 0) + 1 )) (counts_2)) 0)) /\ ((Znth x (replace_Znth ((p * t_2 )) (((Znth (p * t_2 ) counts_2 0) + 1 )) (counts_2)) 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x (replace_Znth ((p * t_2 )) (((Znth (p * t_2 ) counts_2 0) + 1 )) (counts_2)) 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < ((p * t_2 ) + p ))))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < ((p * t_2 ) + p ))))) -> (In q_2 ps ))))) ”
  &&  emp
).

Definition solver_entail_wit_4 :=
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts_2: (@list Z)) (p: Z) (PreH1 : (p > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= (n_pre + 1 ))) (PreH6 : ((Zlength (counts_2)) = 3005)) (PreH7 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x_2 counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x_2 = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x_2 = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts_2: (@list Z)) (p: Z) (PreH1 : (p > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= (n_pre + 1 ))) (PreH6 : ((Zlength (counts_2)) = 3005)) (PreH7 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x_2 counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x_2 = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x_2 = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  TT && emp 
|--
  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts_2: (@list Z)) (p: Z) (PreH1 : (p > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= (n_pre + 1 ))) (PreH6 : ((Zlength (counts_2)) = 3005)) (PreH7 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x_2 counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x_2 = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x_2 = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))
.

Definition solver_entail_wit_5_1 :=
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (ps_2: (@list Z)) (k_3: Z) (k_4: Z) (counts_2: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (p = (a_3 * b_3 ))) -> (p <= a_3))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts_2)) = 3005)) (PreH12 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 1 ))) /\ exists (ps_2: (@list Z)), (((((Zlength (ps_2)) = (Znth x_2 counts_2 0)) /\ (NoDup ps_2 )) /\ forall (q_3: Z), ((In q_3 ps_2 ) -> ((((2 <= q_3) /\ forall (a_4: Z), forall (b_4: Z), (((2 <= a_4) /\ (q_3 = (a_4 * b_4 ))) -> (q_3 <= a_4))) /\ exists (k_3: Z), ((1 <= k_3) /\ (x_2 = (q_3 * k_3 )))) /\ ((q_3 < p) \/ ((q_3 = p) /\ (x_2 < m)))))) /\ forall (q_4: Z), (((((2 <= q_4) /\ forall (a_5: Z), forall (b_5: Z), (((2 <= a_5) /\ (q_4 = (a_5 * b_5 ))) -> (q_4 <= a_5))) /\ exists (k_4: Z), ((1 <= k_4) /\ (x_2 = (q_4 * k_4 )))) /\ ((q_4 < p) \/ ((q_4 = p) /\ (x_2 < m)))) -> (In q_4 ps_2 )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= ((p + 1 ) - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < (p + 1 ))) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < (p + 1 ))) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps ))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (ps_2: (@list Z)) (k_3: Z) (k_4: Z) (counts_2: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (p = (a_3 * b_3 ))) -> (p <= a_3))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts_2)) = 3005)) (PreH12 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 1 ))) /\ exists (ps_2: (@list Z)), (((((Zlength (ps_2)) = (Znth x_2 counts_2 0)) /\ (NoDup ps_2 )) /\ forall (q_3: Z), ((In q_3 ps_2 ) -> ((((2 <= q_3) /\ forall (a_4: Z), forall (b_4: Z), (((2 <= a_4) /\ (q_3 = (a_4 * b_4 ))) -> (q_3 <= a_4))) /\ exists (k_3: Z), ((1 <= k_3) /\ (x_2 = (q_3 * k_3 )))) /\ ((q_3 < p) \/ ((q_3 = p) /\ (x_2 < m)))))) /\ forall (q_4: Z), (((((2 <= q_4) /\ forall (a_5: Z), forall (b_5: Z), (((2 <= a_5) /\ (q_4 = (a_5 * b_5 ))) -> (q_4 <= a_5))) /\ exists (k_4: Z), ((1 <= k_4) /\ (x_2 = (q_4 * k_4 )))) /\ ((q_4 < p) \/ ((q_4 = p) /\ (x_2 < m)))) -> (In q_4 ps_2 )))))),
  TT && emp 
|--
  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= ((p + 1 ) - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < (p + 1 ))) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < (p + 1 ))) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps ))))) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (ps_2: (@list Z)) (k_3: Z) (k_4: Z) (counts_2: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (p = (a_3 * b_3 ))) -> (p <= a_3))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts_2)) = 3005)) (PreH12 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (p - 1 ))) /\ exists (ps_2: (@list Z)), (((((Zlength (ps_2)) = (Znth x_2 counts_2 0)) /\ (NoDup ps_2 )) /\ forall (q_3: Z), ((In q_3 ps_2 ) -> ((((2 <= q_3) /\ forall (a_4: Z), forall (b_4: Z), (((2 <= a_4) /\ (q_3 = (a_4 * b_4 ))) -> (q_3 <= a_4))) /\ exists (k_3: Z), ((1 <= k_3) /\ (x_2 = (q_3 * k_3 )))) /\ ((q_3 < p) \/ ((q_3 = p) /\ (x_2 < m)))))) /\ forall (q_4: Z), (((((2 <= q_4) /\ forall (a_5: Z), forall (b_5: Z), (((2 <= a_5) /\ (q_4 = (a_5 * b_5 ))) -> (q_4 <= a_5))) /\ exists (k_4: Z), ((1 <= k_4) /\ (x_2 = (q_4 * k_4 )))) /\ ((q_4 < p) \/ ((q_4 = p) /\ (x_2 < m)))) -> (In q_4 ps_2 )))))),
  forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= ((p + 1 ) - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < (p + 1 ))) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < (p + 1 ))) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps )))))
.

Definition solver_entail_wit_5_2 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts_2: (@list Z)) (p: Z) (PreH1 : ((Znth p counts_2 0) <> 0)) (PreH2 : (p <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (2 <= p)) (PreH6 : (p <= (n_pre + 1 ))) (PreH7 : ((Zlength (counts_2)) = 3005)) (PreH8 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts_2 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= ((p + 1 ) - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < (p + 1 ))) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < (p + 1 ))) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps ))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
.

Definition solver_entail_wit_6 :=
(
forall (n_pre: Z) (counts_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)) (PreH3 : ((Zlength (counts_2)) = 3005)) (PreH4 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x_2 counts_2 0) = 2) /\ (AlmostPrime x_2 )) \/ (((Znth x_2 counts_2 0) <> 2) /\ ~((AlmostPrime x_2 ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (1 - 1 )) ”
  &&  “ (Spec (1 - 1 ) 0 ) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (counts_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)) (PreH3 : ((Zlength (counts_2)) = 3005)) (PreH4 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x_2 counts_2 0) = 2) /\ (AlmostPrime x_2 )) \/ (((Znth x_2 counts_2 0) <> 2) /\ ~((AlmostPrime x_2 ))))))),
  TT && emp 
|--
  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  “ (Spec (1 - 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (n_pre: Z) (counts_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)) (PreH3 : ((Zlength (counts_2)) = 3005)) (PreH4 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x_2 counts_2 0) = 2) /\ (AlmostPrime x_2 )) \/ (((Znth x_2 counts_2 0) <> 2) /\ ~((AlmostPrime x_2 ))))))),
  forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (n_pre: Z) (counts_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 3000)) (PreH3 : ((Zlength (counts_2)) = 3005)) (PreH4 : forall (x_2: Z), (((1 <= x_2) /\ (x_2 <= n_pre)) -> (((0 <= (Znth x_2 counts_2 0)) /\ ((Znth x_2 counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x_2 counts_2 0) = 2) /\ (AlmostPrime x_2 )) \/ (((Znth x_2 counts_2 0) <> 2) /\ ~((AlmostPrime x_2 ))))))),
  (Spec (1 - 1 ) 0 )
.

Definition solver_entail_wit_7_1 :=
(
forall (n_pre: Z) (counts_2: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts_2 0) = 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts_2)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (1 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= (cnt + 1 )) ”
  &&  “ ((cnt + 1 ) <= ((v + 1 ) - 1 )) ”
  &&  “ (Spec ((v + 1 ) - 1 ) (cnt + 1 ) ) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (counts_2: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts_2 0) = 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts_2)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))),
  TT && emp 
|--
  “ (Spec ((v + 1 ) - 1 ) (cnt + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 :=
forall (n_pre: Z) (counts_2: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts_2 0) = 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts_2)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (Spec ((v + 1 ) - 1 ) (cnt + 1 ) )
.

Definition solver_entail_wit_7_2 :=
(
forall (n_pre: Z) (counts_2: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts_2 0) <> 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts_2)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (1 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= cnt) ”
  &&  “ (cnt <= ((v + 1 ) - 1 )) ”
  &&  “ (Spec ((v + 1 ) - 1 ) cnt ) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
) \/
(
forall (n_pre: Z) (counts_2: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts_2 0) <> 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts_2)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))),
  TT && emp 
|--
  “ (Spec ((v + 1 ) - 1 ) cnt ) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 :=
forall (n_pre: Z) (counts_2: (@list Z)) (cnt: Z) (v: Z) (PreH1 : ((Znth v counts_2 0) <> 2)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 3000)) (PreH5 : (1 <= v)) (PreH6 : (v <= (n_pre + 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= (v - 1 ))) (PreH9 : (Spec (v - 1 ) cnt )) (PreH10 : ((Zlength (counts_2)) = 3005)) (PreH11 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts_2 0)) /\ ((Znth x counts_2 0) <= (n_pre - 1 ))) /\ ((((Znth x counts_2 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts_2 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (Spec ((v + 1 ) - 1 ) cnt )
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (1 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= (v - 1 ))) (PreH8 : (Spec (v - 1 ) cnt )) (PreH9 : ((Zlength (counts)) = 3005)) (PreH10 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  TT && emp 
|--
  “ (Spec n_pre cnt ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (1 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= (v - 1 ))) (PreH8 : (Spec (v - 1 ) cnt )) (PreH9 : ((Zlength (counts)) = 3005)) (PreH10 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  TT && emp 
|--
  “ (Spec n_pre cnt ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (1 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= (v - 1 ))) (PreH8 : (Spec (v - 1 ) cnt )) (PreH9 : ((Zlength (counts)) = 3005)) (PreH10 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (Spec n_pre cnt )
.

Definition solver_partial_solve_wit_1 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (p: Z) (PreH1 : (p <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= (n_pre + 1 ))) (PreH6 : ((Zlength (counts)) = 3005)) (PreH7 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ (p <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= (n_pre + 1 )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 2 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ (q < p)) /\ forall (a: Z), forall (b: Z), (((2 <= a) /\ (q = (a * b ))) -> (q <= a))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ (q_2 < p)) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q_2 = (a_2 * b_2 ))) -> (q_2 <= a_2))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) -> (In q_2 ps ))))) ”
  &&  (((( &( "ndiv" ) ) + (p * sizeof(INT)))) # Int  |-> (Znth p counts 0))
  **  (IntArray.missing_i ( &( "ndiv" ) ) p 0 3005 counts )
.

Definition solver_partial_solve_wit_2 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ (m <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= n_pre) ”
  &&  “ forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a)) ”
  &&  “ (p <= m) ”
  &&  “ (m <= (n_pre + p )) ”
  &&  “ (1 <= t) ”
  &&  “ (m = (p * t )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps ))))) ”
  &&  (((( &( "ndiv" ) ) + (m * sizeof(INT)))) # Int  |-> (Znth m counts 0))
  **  (IntArray.missing_i ( &( "ndiv" ) ) m 0 3005 counts )
.

Definition solver_partial_solve_wit_3 :=
forall (n_pre: Z) (ps: (@list Z)) (k: Z) (k_2: Z) (counts: (@list Z)) (t: Z) (m: Z) (p: Z) (PreH1 : (m <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (2 <= p)) (PreH5 : (p <= n_pre)) (PreH6 : forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a))) (PreH7 : (p <= m)) (PreH8 : (m <= (n_pre + p ))) (PreH9 : (1 <= t)) (PreH10 : (m = (p * t ))) (PreH11 : ((Zlength (counts)) = 3005)) (PreH12 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps )))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ (m <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= n_pre) ”
  &&  “ forall (a: Z), forall (b: Z), (((2 <= a) /\ (p = (a * b ))) -> (p <= a)) ”
  &&  “ (p <= m) ”
  &&  “ (m <= (n_pre + p )) ”
  &&  “ (1 <= t) ”
  &&  “ (m = (p * t )) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (p - 1 ))) /\ exists (ps: (@list Z)), (((((Zlength (ps)) = (Znth x counts 0)) /\ (NoDup ps )) /\ forall (q: Z), ((In q ps ) -> ((((2 <= q) /\ forall (a_2: Z), forall (b_2: Z), (((2 <= a_2) /\ (q = (a_2 * b_2 ))) -> (q <= a_2))) /\ exists (k: Z), ((1 <= k) /\ (x = (q * k )))) /\ ((q < p) \/ ((q = p) /\ (x < m)))))) /\ forall (q_2: Z), (((((2 <= q_2) /\ forall (a_3: Z), forall (b_3: Z), (((2 <= a_3) /\ (q_2 = (a_3 * b_3 ))) -> (q_2 <= a_3))) /\ exists (k_2: Z), ((1 <= k_2) /\ (x = (q_2 * k_2 )))) /\ ((q_2 < p) \/ ((q_2 = p) /\ (x < m)))) -> (In q_2 ps ))))) ”
  &&  (((( &( "ndiv" ) ) + (m * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "ndiv" ) ) m 0 3005 counts )
.

Definition solver_partial_solve_wit_4 :=
forall (n_pre: Z) (counts: (@list Z)) (cnt: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 3000)) (PreH4 : (1 <= v)) (PreH5 : (v <= (n_pre + 1 ))) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= (v - 1 ))) (PreH8 : (Spec (v - 1 ) cnt )) (PreH9 : ((Zlength (counts)) = 3005)) (PreH10 : forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x ))))))),
  (IntArray.full ( &( "ndiv" ) ) 3005 counts )
|--
  “ (v <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 3000) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= (n_pre + 1 )) ”
  &&  “ (0 <= cnt) ”
  &&  “ (cnt <= (v - 1 )) ”
  &&  “ (Spec (v - 1 ) cnt ) ”
  &&  “ ((Zlength (counts)) = 3005) ”
  &&  “ forall (x: Z), (((1 <= x) /\ (x <= n_pre)) -> (((0 <= (Znth x counts 0)) /\ ((Znth x counts 0) <= (n_pre - 1 ))) /\ ((((Znth x counts 0) = 2) /\ (AlmostPrime x )) \/ (((Znth x counts 0) <> 2) /\ ~((AlmostPrime x )))))) ”
  &&  (((( &( "ndiv" ) ) + (v * sizeof(INT)))) # Int  |-> (Znth v counts 0))
  **  (IntArray.missing_i ( &( "ndiv" ) ) v 0 3005 counts )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
