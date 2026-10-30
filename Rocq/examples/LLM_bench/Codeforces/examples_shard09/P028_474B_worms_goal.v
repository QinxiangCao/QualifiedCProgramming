From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P028_474B_worms_lib.
Local Open Scope sac.

(*----- Function locate_pile -----*)

Definition locate_pile_safety_wit_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (pile_sizes)))) (PreH4 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= (Znth n_pre prefix 0))) (PreH8 : (PrefixSums pile_sizes prefix )),
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition locate_pile_safety_wit_2 :=
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((lo + ((hi - lo ) ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (lo + ((hi - lo ) ÷ 2 ) )) ”
) \/
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((lo + ((hi - lo ) ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (lo + ((hi - lo ) ÷ 2 ) )) ”
).

Definition locate_pile_safety_wit_2_split_goal_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((lo + ((hi - lo ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition locate_pile_safety_wit_2_split_goal_2 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((INT_MIN) <= (lo + ((hi - lo ) ÷ 2 ) )) ”
.

Definition locate_pile_safety_wit_3 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (((hi - lo ) <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition locate_pile_safety_wit_4 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((hi - lo ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (hi - lo )) ”
.

Definition locate_pile_safety_wit_5 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition locate_pile_safety_wit_6 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0) < q_pre)) (PreH2 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH3 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH4 : (q_pre <= INT64_MAX)) (PreH5 : (q_pre >= INT64_MIN)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (lo < hi)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (pile_sizes)))) (PreH12 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH14 : (PrefixSums pile_sizes prefix )) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= (Znth n_pre prefix 0))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= hi)) (PreH19 : (hi <= n_pre)) (PreH20 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH21 : (q_pre <= (Znth hi prefix 0))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "mid" ) )) # Int  |-> (lo + ((hi - lo ) ÷ 2 ) ))
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
|--
  “ (((lo + ((hi - lo ) ÷ 2 ) ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((lo + ((hi - lo ) ÷ 2 ) ) + 1 )) ”
.

Definition locate_pile_safety_wit_7 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0) < q_pre)) (PreH2 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH3 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH4 : (q_pre <= INT64_MAX)) (PreH5 : (q_pre >= INT64_MIN)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (lo < hi)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (pile_sizes)))) (PreH12 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH14 : (PrefixSums pile_sizes prefix )) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= (Znth n_pre prefix 0))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= hi)) (PreH19 : (hi <= n_pre)) (PreH20 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH21 : (q_pre <= (Znth hi prefix 0))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "mid" ) )) # Int  |-> (lo + ((hi - lo ) ÷ 2 ) ))
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition locate_pile_entail_wit_1 :=
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (pile_sizes)))) (PreH4 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= (Znth n_pre prefix 0))) (PreH8 : (PrefixSums pile_sizes prefix )),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= (Znth n_pre prefix 0)) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ ((Znth (1 - 1 ) prefix 0) < q_pre) ”
  &&  “ (q_pre <= (Znth n_pre prefix 0)) ”
  &&  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (pile_sizes)))) (PreH4 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= (Znth n_pre prefix 0))) (PreH8 : (PrefixSums pile_sizes prefix )),
  TT && emp 
|--
  “ ((Znth (1 - 1 ) prefix 0) < q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  emp
).

Definition locate_pile_entail_wit_1_split_goal_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (pile_sizes)))) (PreH4 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= (Znth n_pre prefix 0))) (PreH8 : (PrefixSums pile_sizes prefix )),
  ((Znth (1 - 1 ) prefix 0) < q_pre)
.

Definition locate_pile_entail_wit_1_split_goal_2 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (pile_sizes)))) (PreH4 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= (Znth n_pre prefix 0))) (PreH8 : (PrefixSums pile_sizes prefix )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))
.

Definition locate_pile_entail_wit_2 :=
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  ((( &( "mid" ) )) # Int  |-> (lo + ((hi - lo ) ÷ 2 ) ))
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (lo <= (lo + ((hi - lo ) ÷ 2 ) )) ”
  &&  “ ((lo + ((hi - lo ) ÷ 2 ) ) < hi) ”
  &&  “ (q_pre <= INT64_MAX) ”
  &&  “ (q_pre >= INT64_MIN) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (lo < hi) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= (Znth n_pre prefix 0)) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= hi) ”
  &&  “ (hi <= n_pre) ”
  &&  “ ((Znth (lo - 1 ) prefix 0) < q_pre) ”
  &&  “ (q_pre <= (Znth hi prefix 0)) ”
  &&  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "mid" ) )) # Int  |-> (lo + ((hi - lo ) ÷ 2 ) ))
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int64  |-> q_pre)
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (q_pre <= INT64_MAX)) (PreH2 : (q_pre >= INT64_MIN)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((lo + ((hi - lo ) ÷ 2 ) ) <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + ((hi - lo ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH17 : (PrefixSums pile_sizes prefix )) (PreH18 : (1 <= q_pre)) (PreH19 : (q_pre <= (Znth n_pre prefix 0))) (PreH20 : (1 <= lo)) (PreH21 : (lo <= hi)) (PreH22 : (hi <= n_pre)) (PreH23 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH24 : (q_pre <= (Znth hi prefix 0))),
  TT && emp 
|--
  “ ((lo + ((hi - lo ) ÷ 2 ) ) < hi) ”
  &&  “ (lo <= (lo + ((hi - lo ) ÷ 2 ) )) ”
  &&  emp
).

Definition locate_pile_entail_wit_2_split_goal_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (q_pre <= INT64_MAX)) (PreH2 : (q_pre >= INT64_MIN)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((lo + ((hi - lo ) ÷ 2 ) ) <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + ((hi - lo ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH17 : (PrefixSums pile_sizes prefix )) (PreH18 : (1 <= q_pre)) (PreH19 : (q_pre <= (Znth n_pre prefix 0))) (PreH20 : (1 <= lo)) (PreH21 : (lo <= hi)) (PreH22 : (hi <= n_pre)) (PreH23 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH24 : (q_pre <= (Znth hi prefix 0))),
  ((lo + ((hi - lo ) ÷ 2 ) ) < hi)
.

Definition locate_pile_entail_wit_2_split_goal_2 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (q_pre <= INT64_MAX)) (PreH2 : (q_pre >= INT64_MIN)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((lo + ((hi - lo ) ÷ 2 ) ) <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + ((hi - lo ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH17 : (PrefixSums pile_sizes prefix )) (PreH18 : (1 <= q_pre)) (PreH19 : (q_pre <= (Znth n_pre prefix 0))) (PreH20 : (1 <= lo)) (PreH21 : (lo <= hi)) (PreH22 : (hi <= n_pre)) (PreH23 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH24 : (q_pre <= (Znth hi prefix 0))),
  (lo <= (lo + ((hi - lo ) ÷ 2 ) ))
.

Definition locate_pile_entail_wit_3_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0) >= q_pre)) (PreH2 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH3 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH4 : (q_pre <= INT64_MAX)) (PreH5 : (q_pre >= INT64_MIN)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (lo < hi)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (pile_sizes)))) (PreH12 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH14 : (PrefixSums pile_sizes prefix )) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= (Znth n_pre prefix 0))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= hi)) (PreH19 : (hi <= n_pre)) (PreH20 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH21 : (q_pre <= (Znth hi prefix 0))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= (Znth n_pre prefix 0)) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (lo + ((hi - lo ) ÷ 2 ) )) ”
  &&  “ ((lo + ((hi - lo ) ÷ 2 ) ) <= n_pre) ”
  &&  “ ((Znth (lo - 1 ) prefix 0) < q_pre) ”
  &&  “ (q_pre <= (Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0)) ”
  &&  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
.

Definition locate_pile_entail_wit_3_2 :=
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0) < q_pre)) (PreH2 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH3 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH4 : (q_pre <= INT64_MAX)) (PreH5 : (q_pre >= INT64_MIN)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (lo < hi)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (pile_sizes)))) (PreH12 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH14 : (PrefixSums pile_sizes prefix )) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= (Znth n_pre prefix 0))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= hi)) (PreH19 : (hi <= n_pre)) (PreH20 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH21 : (q_pre <= (Znth hi prefix 0))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= (Znth n_pre prefix 0)) ”
  &&  “ (1 <= ((lo + ((hi - lo ) ÷ 2 ) ) + 1 )) ”
  &&  “ (((lo + ((hi - lo ) ÷ 2 ) ) + 1 ) <= hi) ”
  &&  “ (hi <= n_pre) ”
  &&  “ ((Znth (((lo + ((hi - lo ) ÷ 2 ) ) + 1 ) - 1 ) prefix 0) < q_pre) ”
  &&  “ (q_pre <= (Znth hi prefix 0)) ”
  &&  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0) < q_pre)) (PreH2 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH3 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH4 : (q_pre <= INT64_MAX)) (PreH5 : (q_pre >= INT64_MIN)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (lo < hi)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (pile_sizes)))) (PreH12 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH14 : (PrefixSums pile_sizes prefix )) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= (Znth n_pre prefix 0))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= hi)) (PreH19 : (hi <= n_pre)) (PreH20 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH21 : (q_pre <= (Znth hi prefix 0))),
  TT && emp 
|--
  “ ((Znth (((lo + ((hi - lo ) ÷ 2 ) ) + 1 ) - 1 ) prefix 0) < q_pre) ”
  &&  emp
).

Definition locate_pile_entail_wit_3_2_split_goal_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0) < q_pre)) (PreH2 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH3 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH4 : (q_pre <= INT64_MAX)) (PreH5 : (q_pre >= INT64_MIN)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (lo < hi)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (pile_sizes)))) (PreH12 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH14 : (PrefixSums pile_sizes prefix )) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= (Znth n_pre prefix 0))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= hi)) (PreH19 : (hi <= n_pre)) (PreH20 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH21 : (q_pre <= (Znth hi prefix 0))),
  ((Znth (((lo + ((hi - lo ) ÷ 2 ) ) + 1 ) - 1 ) prefix 0) < q_pre)
.

Definition locate_pile_return_wit_1 :=
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (PileIndex pile_sizes q_pre lo ) ”
  &&  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  TT && emp 
|--
  “ (PileIndex pile_sizes q_pre lo ) ”
  &&  emp
).

Definition locate_pile_return_wit_1_split_goal_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (pile_sizes)))) (PreH5 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : (PrefixSums pile_sizes prefix )) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= (Znth n_pre prefix 0))) (PreH10 : (1 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= n_pre)) (PreH13 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH14 : (q_pre <= (Znth hi prefix 0))),
  (PileIndex pile_sizes q_pre lo )
.

Definition locate_pile_partial_solve_wit_1 :=
forall (prefix: (@list Z)) (pile_sizes: (@list Z)) (pre_pre: Z) (n_pre: Z) (q_pre: Z) (hi: Z) (lo: Z) (PreH1 : (lo <= (lo + ((hi - lo ) ÷ 2 ) ))) (PreH2 : ((lo + ((hi - lo ) ÷ 2 ) ) < hi)) (PreH3 : (q_pre <= INT64_MAX)) (PreH4 : (q_pre >= INT64_MIN)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (lo < hi)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (pile_sizes)))) (PreH11 : ((Zlength (prefix)) = (n_pre + 1 ))) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH13 : (PrefixSums pile_sizes prefix )) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= (Znth n_pre prefix 0))) (PreH16 : (1 <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= n_pre)) (PreH19 : ((Znth (lo - 1 ) prefix 0) < q_pre)) (PreH20 : (q_pre <= (Znth hi prefix 0))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (lo <= (lo + ((hi - lo ) ÷ 2 ) )) ”
  &&  “ ((lo + ((hi - lo ) ÷ 2 ) ) < hi) ”
  &&  “ (q_pre <= INT64_MAX) ”
  &&  “ (q_pre >= INT64_MIN) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (lo < hi) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= (Znth n_pre prefix 0)) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= hi) ”
  &&  “ (hi <= n_pre) ”
  &&  “ ((Znth (lo - 1 ) prefix 0) < q_pre) ”
  &&  “ (q_pre <= (Znth hi prefix 0)) ”
  &&  (((pre_pre + ((lo + ((hi - lo ) ÷ 2 ) ) * sizeof(INT64)))) # Int64  |-> (Znth (lo + ((hi - lo ) ÷ 2 ) ) prefix 0))
  **  (Int64Array.missing_i pre_pre (lo + ((hi - lo ) ÷ 2 ) ) 0 (n_pre + 1 ) prefix )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (old_pre0: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))),
  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (old_pre0: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))),
  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSumsPrefix pile_sizes (cons (0) ((@nil Z))) )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 1 (cons (0) ((@nil Z))) )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) )) ”
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) )) ”
).

Definition solver_safety_wit_6_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) )) ”
.

Definition solver_safety_wit_7 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix_next)) = (i + 2 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix_next )),
  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 2 ) prefix_next )
  **  (Int64Array.seg_shape pre_pre (i + 2 ) (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result_next)) = (i + 1 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (i + 1 ))) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_next 0) ))),
  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 (i + 1 ) result_next )
  **  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i pile_sizes 0)) /\ ((Znth i pile_sizes 0) <= 1000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> (1 <= (Znth i_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
|--
  EX (old_pre0: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
.

Definition solver_entail_wit_2 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSumsPrefix pile_sizes (cons (0) ((@nil Z))) ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 1 (cons (0) ((@nil Z))) )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH9 : (Pre pile_sizes worm_queries )) (PreH10 : (n_pre = (Zlength (pile_sizes)))) (PreH11 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ (PrefixSumsPrefix pile_sizes (cons (0) ((@nil Z))) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 1 (cons (0) ((@nil Z))) )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH9 : (Pre pile_sizes worm_queries )) (PreH10 : (n_pre = (Zlength (pile_sizes)))) (PreH11 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ (PrefixSumsPrefix pile_sizes (cons (0) ((@nil Z))) ) ”
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH9 : (Pre pile_sizes worm_queries )) (PreH10 : (n_pre = (Zlength (pile_sizes)))) (PreH11 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH9 : (Pre pile_sizes worm_queries )) (PreH10 : (n_pre = (Zlength (pile_sizes)))) (PreH11 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
.

Definition solver_entail_wit_2_split_goal_spatial :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH9 : (Pre pile_sizes worm_queries )) (PreH10 : (n_pre = (Zlength (pile_sizes)))) (PreH11 : (m_pre = (Zlength (worm_queries)))),
  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
|--
  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 1 (cons (0) ((@nil Z))) )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
.

Definition solver_entail_wit_3 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSumsPrefix pile_sizes (cons (0) ((@nil Z))) )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 1 (cons (0) ((@nil Z))) )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
|--
  EX (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (0 + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (0 + 1 ) prefix )
  **  (Int64Array.seg_shape pre_pre (0 + 1 ) (n_pre + 1 ) )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSumsPrefix pile_sizes (cons (0) ((@nil Z))) )),
  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 1 (cons (0) ((@nil Z))) )
|--
  EX (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (prefix)) = (0 + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (0 + 1 ) prefix )
).

Definition solver_entail_wit_4 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix_2 )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  EX (old_next: Z) (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
.

Definition solver_entail_wit_4_split_goal_spatial :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full_shape out_pre m_pre )
|--
  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
.

Definition solver_entail_wit_5 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) )) ((app (prefix) ((cons (old_next) ((@nil Z))))))) )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  EX (prefix_next: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (prefix_next)) = (i + 2 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix_next ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 2 ) prefix_next )
  **  (Int64Array.seg_shape pre_pre (i + 2 ) (n_pre + 1 ) )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) prefix 0) + (Znth i pile_sizes 0) )) ((app (prefix) ((cons (old_next) ((@nil Z))))))) )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  EX (prefix_next: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (prefix_next)) = (i + 2 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix_next ) ”
  &&  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 2 ) prefix_next )
  **  (Int64Array.seg_shape pre_pre (i + 2 ) (n_pre + 1 ) )
).

Definition solver_entail_wit_6 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix_next)) = (i + 2 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix_next )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 2 ) prefix_next )
  **  (Int64Array.seg_shape pre_pre (i + 2 ) (n_pre + 1 ) )
|--
  EX (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (prefix)) = ((i + 1 ) + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) prefix )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix_next)) = (i + 2 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix_next )),
  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 2 ) prefix_next )
|--
  EX (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (prefix)) = ((i + 1 ) + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) prefix )
).

Definition solver_entail_wit_7 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix_2 )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  EX (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  TT && emp 
|--
  “ (PrefixSums pile_sizes prefix_2 ) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (prefix_2)) = (i + 1 ))) (PreH14 : (PrefixSumsPrefix pile_sizes prefix_2 )),
  (PrefixSums pile_sizes prefix_2 )
.

Definition solver_entail_wit_8 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (result: (@list Z)) (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ ((Zlength (result)) = 0) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < 0)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) )) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 0 result )
  **  (IntArray.seg_shape out_pre 0 m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < 0)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j (@nil Z) 0) )) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  (IntArray.seg_shape out_pre 0 m_pre )
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < 0)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j (@nil Z) 0) )) ”
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full_shape out_pre m_pre )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
.

Definition solver_entail_wit_8_split_goal_4 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full_shape out_pre m_pre )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
.

Definition solver_entail_wit_8_split_goal_spatial :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )),
  (IntArray.full_shape out_pre m_pre )
|--
  (IntArray.seg_shape out_pre 0 m_pre )
.

Definition solver_entail_wit_9 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (result_2: (@list Z)) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_2 0) ))),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 i result_2 )
  **  (IntArray.seg_shape out_pre i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (old_out: Z) (result: (@list Z)) (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < m_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) )) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 i result )
  **  (((out_pre + (i * sizeof(INT)))) # Int  |-> old_out)
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_2 0) ))),
  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_2 0) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  (IntArray.missing_i_shape out_pre i i m_pre )
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_2 0) ))),
  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_2 0) )) ”
.

Definition solver_entail_wit_9_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_2 0) ))),
  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
.

Definition solver_entail_wit_9_split_goal_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_2 0) ))),
  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
.

Definition solver_entail_wit_9_split_goal_spatial :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_2 0) ))),
  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
|--
  (IntArray.missing_i_shape out_pre i i m_pre )
.

Definition solver_entail_wit_10 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (retval: Z) (PreH1 : (PileIndex pile_sizes (Znth i worm_queries 0) retval )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < m_pre)) (PreH14 : ((Zlength (result)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result 0) ))),
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (result) ((cons (old_out) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
|--
  EX (result_next: (@list Z)) (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < m_pre) ”
  &&  “ ((Zlength (result_next)) = (i + 1 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (i + 1 ))) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_next 0) )) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 (i + 1 ) result_next )
  **  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (out_pre: Z) (prefix_2: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (retval: Z) (PreH1 : (PileIndex pile_sizes (Znth i worm_queries 0) retval )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < m_pre)) (PreH14 : ((Zlength (result)) = i)) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < i)) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result 0) ))),
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (result) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
|--
  EX (result_next: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix_2 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < m_pre) ”
  &&  “ ((Zlength (result_next)) = (i + 1 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (i + 1 ))) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_next 0) )) ”
  &&  (IntArray.seg out_pre 0 (i + 1 ) result_next )
  **  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
).

Definition solver_entail_wit_11 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix_2: (@list Z)) (result_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result_next)) = (i + 1 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (i + 1 ))) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_next 0) ))),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 (i + 1 ) result_next )
  **  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix_2 )
|--
  EX (result: (@list Z)) (prefix: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ ((Zlength (result)) = (i + 1 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (i + 1 ))) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) )) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 (i + 1 ) result )
  **  (IntArray.seg_shape out_pre (i + 1 ) m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (prefix_2: (@list Z)) (result_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result_next)) = (i + 1 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (i + 1 ))) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_next 0) ))),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < (i + 1 ))) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_next 0) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (prefix_2: (@list Z)) (result_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result_next)) = (i + 1 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (i + 1 ))) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_next 0) ))),
  forall (j: Z), (((0 <= j) /\ (j < (i + 1 ))) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_next 0) ))
.

Definition solver_entail_wit_11_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (prefix_2: (@list Z)) (result_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result_next)) = (i + 1 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (i + 1 ))) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_next 0) ))),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))
.

Definition solver_entail_wit_11_split_goal_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (prefix_2: (@list Z)) (result_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 pile_sizes 0)) /\ ((Znth k_3 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < m_pre)) -> (1 <= (Znth k_4 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix_2 )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result_next)) = (i + 1 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (i + 1 ))) -> (PileIndex pile_sizes (Znth j_2 worm_queries 0) (Znth j_2 result_next 0) ))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))
.

Definition solver_return_wit_1 :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (result_2: (@list Z)) (i: Z) (prefix: (@list Z)) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_2 0) ))),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 i result_2 )
  **  (IntArray.seg_shape out_pre i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  EX (result: (@list Z)),
  “ (Spec pile_sizes worm_queries result ) ”
  &&  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full out_pre m_pre result )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (pre_pre: Z) (result_2: (@list Z)) (i: Z) (prefix: (@list Z)) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_2 0) ))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (Spec pile_sizes worm_queries result_2 ) ”
  &&  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
).

Definition solver_return_wit_1_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (pre_pre: Z) (result_2: (@list Z)) (i: Z) (prefix: (@list Z)) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_2 0) ))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (Spec pile_sizes worm_queries result_2 ) ”
.

Definition solver_return_wit_1_split_goal_spatial :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (n_pre: Z) (m_pre: Z) (pre_pre: Z) (result_2: (@list Z)) (i: Z) (prefix: (@list Z)) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : ((Zlength (result_2)) = i)) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result_2 0) ))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) prefix )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) prefix 0))
  **  (Int64Array.missing_i pre_pre i 0 (i + 1 ) prefix )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (((piles_pre + (i * sizeof(INT)))) # Int  |-> (Znth i pile_sizes 0))
  **  (IntArray.missing_i piles_pre i 0 n_pre pile_sizes )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (prefix)) = (i + 1 ))) (PreH13 : (PrefixSumsPrefix pile_sizes prefix )),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (prefix)) = (i + 1 )) ”
  &&  “ (PrefixSumsPrefix pile_sizes prefix ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (prefix) ((cons (old_next) ((@nil Z))))) )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full_shape out_pre m_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_4 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result)) = i)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.full piles_pre n_pre pile_sizes )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.seg out_pre 0 i result )
  **  (((out_pre + (i * sizeof(INT)))) # Int  |-> old_out)
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < m_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) )) ”
  &&  (((queries_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i worm_queries 0))
  **  (Int64Array.missing_i queries_pre i 0 m_pre worm_queries )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.seg out_pre 0 i result )
  **  (((out_pre + (i * sizeof(INT)))) # Int  |-> old_out)
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
.

Definition solver_partial_solve_wit_5_pure :=
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result)) = i)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (1 <= (Znth i worm_queries 0)) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ ((Znth i worm_queries 0) <= (Znth n_pre prefix 0)) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
) \/
(
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0)))) (PreH13 : (Pre pile_sizes worm_queries )) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : (m_pre = (Zlength (worm_queries)))) (PreH16 : (PrefixSums pile_sizes prefix )) (PreH17 : (0 <= i)) (PreH18 : (i < m_pre)) (PreH19 : ((Zlength (result)) = i)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ ((Znth i worm_queries 0) <= (Znth n_pre prefix 0)) ”
).

Definition solver_partial_solve_wit_5_pure_split_goal_1 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0)))) (PreH13 : (Pre pile_sizes worm_queries )) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : (m_pre = (Zlength (worm_queries)))) (PreH16 : (PrefixSums pile_sizes prefix )) (PreH17 : (0 <= i)) (PreH18 : (i < m_pre)) (PreH19 : ((Zlength (result)) = i)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
.

Definition solver_partial_solve_wit_5_pure_split_goal_2 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0)))) (PreH13 : (Pre pile_sizes worm_queries )) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : (m_pre = (Zlength (worm_queries)))) (PreH16 : (PrefixSums pile_sizes prefix )) (PreH17 : (0 <= i)) (PreH18 : (i < m_pre)) (PreH19 : ((Zlength (result)) = i)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
.

Definition solver_partial_solve_wit_5_pure_split_goal_3 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0)))) (PreH13 : (Pre pile_sizes worm_queries )) (PreH14 : (n_pre = (Zlength (pile_sizes)))) (PreH15 : (m_pre = (Zlength (worm_queries)))) (PreH16 : (PrefixSums pile_sizes prefix )) (PreH17 : (0 <= i)) (PreH18 : (i < m_pre)) (PreH19 : ((Zlength (result)) = i)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  ((( &( "piles" ) )) # Ptr  |-> piles_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ ((Znth i worm_queries 0) <= (Znth n_pre prefix 0)) ”
.

Definition solver_partial_solve_wit_5_aux :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0)))) (PreH7 : (Pre pile_sizes worm_queries )) (PreH8 : (n_pre = (Zlength (pile_sizes)))) (PreH9 : (m_pre = (Zlength (worm_queries)))) (PreH10 : (PrefixSums pile_sizes prefix )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : ((Zlength (result)) = i)) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (1 <= (Znth i worm_queries 0)) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ ((Znth i worm_queries 0) <= (Znth n_pre prefix 0)) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ ((Zlength (prefix)) = (n_pre + 1 )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 pile_sizes 0)) /\ ((Znth k_2 pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < m_pre)) -> (1 <= (Znth k_3 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < m_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) )) ”
  &&  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6 :=
forall (worm_queries: (@list Z)) (pile_sizes: (@list Z)) (piles_pre: Z) (n_pre: Z) (queries_pre: Z) (m_pre: Z) (out_pre: Z) (pre_pre: Z) (prefix: (@list Z)) (result: (@list Z)) (old_out: Z) (i: Z) (retval: Z) (PreH1 : (PileIndex pile_sizes (Znth i worm_queries 0) retval )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0)))) (PreH8 : (Pre pile_sizes worm_queries )) (PreH9 : (n_pre = (Zlength (pile_sizes)))) (PreH10 : (m_pre = (Zlength (worm_queries)))) (PreH11 : (PrefixSums pile_sizes prefix )) (PreH12 : (0 <= i)) (PreH13 : (i < m_pre)) (PreH14 : ((Zlength (result)) = i)) (PreH15 : forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) ))),
  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (IntArray.seg out_pre 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
|--
  “ (PileIndex pile_sizes (Znth i worm_queries 0) retval ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k pile_sizes 0)) /\ ((Znth k pile_sizes 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> (1 <= (Znth k_2 worm_queries 0))) ”
  &&  “ (Pre pile_sizes worm_queries ) ”
  &&  “ (n_pre = (Zlength (pile_sizes))) ”
  &&  “ (m_pre = (Zlength (worm_queries))) ”
  &&  “ (PrefixSums pile_sizes prefix ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < m_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < i)) -> (PileIndex pile_sizes (Znth j worm_queries 0) (Znth j result 0) )) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i out_pre i 0 (i + 1 ) (app (result) ((cons (old_out) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) prefix )
  **  (Int64Array.full queries_pre m_pre worm_queries )
  **  (IntArray.full piles_pre n_pre pile_sizes )
  **  (IntArray.missing_i_shape out_pre i i m_pre )
.

Module Type VC_Correct.


Axiom proof_of_locate_pile_safety_wit_1 : locate_pile_safety_wit_1.
Axiom proof_of_locate_pile_safety_wit_2 : locate_pile_safety_wit_2.
Axiom proof_of_locate_pile_safety_wit_3 : locate_pile_safety_wit_3.
Axiom proof_of_locate_pile_safety_wit_4 : locate_pile_safety_wit_4.
Axiom proof_of_locate_pile_safety_wit_5 : locate_pile_safety_wit_5.
Axiom proof_of_locate_pile_safety_wit_6 : locate_pile_safety_wit_6.
Axiom proof_of_locate_pile_safety_wit_7 : locate_pile_safety_wit_7.
Axiom proof_of_locate_pile_entail_wit_1 : locate_pile_entail_wit_1.
Axiom proof_of_locate_pile_entail_wit_2 : locate_pile_entail_wit_2.
Axiom proof_of_locate_pile_entail_wit_3_1 : locate_pile_entail_wit_3_1.
Axiom proof_of_locate_pile_entail_wit_3_2 : locate_pile_entail_wit_3_2.
Axiom proof_of_locate_pile_return_wit_1 : locate_pile_return_wit_1.
Axiom proof_of_locate_pile_partial_solve_wit_1 : locate_pile_partial_solve_wit_1.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.

End VC_Correct.
