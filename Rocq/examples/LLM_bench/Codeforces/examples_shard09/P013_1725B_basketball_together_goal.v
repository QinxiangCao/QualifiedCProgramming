From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P013_1725B_basketball_together_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  ((( &( "wins" ) )) # Int  |->_)
  **  (IntArray.full p_pre n_pre l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  ((( &( "used" ) )) # Int64  |->_)
  **  ((( &( "wins" ) )) # Int  |-> 0)
  **  (IntArray.full p_pre n_pre l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "used" ) )) # Int64  |-> 0)
  **  ((( &( "wins" ) )) # Int  |-> 0)
  **  (IntArray.full p_pre n_pre l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ (((d_pre ÷ (Znth i sorted 0) ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((d_pre ÷ (Znth i sorted 0) ) + 1 )) ”
) \/
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ (((d_pre ÷ (Znth i sorted 0) ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((d_pre ÷ (Znth i sorted 0) ) + 1 )) ”
).

Definition solver_safety_wit_4_split_goal_1 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ (((d_pre ÷ (Znth i sorted 0) ) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((INT64_MIN) <= ((d_pre ÷ (Znth i sorted 0) ) + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((d_pre <> (INT64_MIN)) \/ ((Znth i sorted 0) <> (-1))) ”
  &&  “ ((Znth i sorted 0) <> 0) ”
.

Definition solver_safety_wit_6 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |-> ((d_pre ÷ (Znth i sorted 0) ) + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) )) ”
) \/
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |-> ((d_pre ÷ (Znth i sorted 0) ) + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |-> ((d_pre ÷ (Znth i sorted 0) ) + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |-> ((d_pre ÷ (Znth i sorted 0) ) + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((INT64_MIN) <= (used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) )) ”
.

Definition solver_safety_wit_8 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |-> ((d_pre ÷ (Znth i sorted 0) ) + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> wins)
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((wins + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (wins + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "need" ) )) # Int64  |-> ((d_pre ÷ (Znth i sorted 0) ) + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> (wins + 1 ))
  **  ((( &( "used" ) )) # Int64  |-> used)
|--
  “ ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) )) ”
.

Definition solver_safety_wit_10 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "wins" ) )) # Int  |-> (wins + 1 ))
  **  ((( &( "used" ) )) # Int64  |-> (used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  (IntArray.full p_pre n_pre l1 )
|--
  EX (sorted: (@list Z)),
  “ (1 <= d_pre) ”
  &&  “ (d_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000))) ”
  &&  “ (Permutation powers sorted ) ”
  &&  “ (mono_noninc sorted ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (BasketballGreedyPrefix sorted d_pre 0 0 ) ”
  &&  (IntArray.full p_pre n_pre sorted )
) \/
(
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  TT && emp 
|--
  “ (BasketballGreedyPrefix l1 d_pre 0 0 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k l1 0)) /\ ((Znth k l1 0) <= 1000000000))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  (BasketballGreedyPrefix l1 d_pre 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k l1 0)) /\ ((Znth k l1 0) <= 1000000000)))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation powers l1 )) (PreH2 : (mono_noninc l1 )) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (powers)))),
  ((Zlength (l1)) = n_pre)
.

Definition solver_entail_wit_2 :=
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) > n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
|--
  EX (sorted_2: (@list Z)),
  “ (1 <= d_pre) ”
  &&  “ (d_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (sorted_2)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 1000000000))) ”
  &&  “ (Permutation powers sorted_2 ) ”
  &&  “ (mono_noninc sorted_2 ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (wins = i) ”
  &&  “ (0 <= used) ”
  &&  “ (used <= n_pre) ”
  &&  “ (((d_pre ÷ (Znth i sorted 0) ) + 1 ) = ((d_pre ÷ (Znth (i) (sorted_2) (0)) ) + 1 )) ”
  &&  “ ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) > n_pre) ”
  &&  “ (BasketballGreedyPrefix sorted_2 d_pre i used ) ”
  &&  “ (Spec d_pre powers wins ) ”
  &&  (IntArray.full p_pre n_pre sorted_2 )
) \/
(
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) > n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  TT && emp 
|--
  “ (Spec d_pre powers wins ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) > n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  (Spec d_pre powers wins )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted 0) ) + 1 ) ) > n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted )) (PreH10 : (mono_noninc sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))
.

Definition solver_entail_wit_3 :=
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted_2)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted_2 )) (PreH10 : (mono_noninc sorted_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted_2 d_pre i used )),
  (IntArray.full p_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)),
  “ (1 <= d_pre) ”
  &&  “ (d_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000))) ”
  &&  “ (Permutation powers sorted ) ”
  &&  “ (mono_noninc sorted ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((wins + 1 ) = (i + 1 )) ”
  &&  “ (0 <= (used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) )) ”
  &&  “ ((used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) ) <= n_pre) ”
  &&  “ (BasketballGreedyPrefix sorted d_pre (i + 1 ) (used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) ) ) ”
  &&  (IntArray.full p_pre n_pre sorted )
) \/
(
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted_2)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted_2 )) (PreH10 : (mono_noninc sorted_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted_2 d_pre i used )),
  TT && emp 
|--
  “ (BasketballGreedyPrefix sorted_2 d_pre (wins + 1 ) (used + ((d_pre ÷ (Znth wins sorted_2 0) ) + 1 ) ) ) ”
  &&  “ (0 <= (used + ((d_pre ÷ (Znth wins sorted_2 0) ) + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted_2)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted_2 )) (PreH10 : (mono_noninc sorted_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted_2 d_pre i used )),
  (BasketballGreedyPrefix sorted_2 d_pre (wins + 1 ) (used + ((d_pre ÷ (Znth wins sorted_2 0) ) + 1 ) ) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((used + ((d_pre ÷ (Znth i sorted_2 0) ) + 1 ) ) <= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= d_pre)) (PreH4 : (d_pre <= 1000000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (sorted_2)) = n_pre)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 1000000000)))) (PreH9 : (Permutation powers sorted_2 )) (PreH10 : (mono_noninc sorted_2 )) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (wins = i)) (PreH14 : (0 <= used)) (PreH15 : (used <= n_pre)) (PreH16 : (BasketballGreedyPrefix sorted_2 d_pre i used )),
  (0 <= (used + ((d_pre ÷ (Znth wins sorted_2 0) ) + 1 ) ))
.

Definition solver_return_wit_1 :=
(
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
|--
  EX (p_after: (@list Z)),
  “ (Spec d_pre powers wins ) ”
  &&  “ (Permutation powers p_after ) ”
  &&  (IntArray.full p_pre n_pre p_after )
) \/
(
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  TT && emp 
|--
  “ (Spec d_pre powers wins ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (powers: (@list Z)) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (Spec d_pre powers wins )
.

Definition solver_return_wit_2 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (sorted: (@list Z)) (i: Z) (wins: Z) (used: Z) (need: Z) (PreH1 : (1 <= d_pre)) (PreH2 : (d_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH7 : (Permutation powers sorted )) (PreH8 : (mono_noninc sorted )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (wins = i)) (PreH12 : (0 <= used)) (PreH13 : (used <= n_pre)) (PreH14 : (need = ((d_pre ÷ (Znth (i) (sorted) (0)) ) + 1 ))) (PreH15 : ((used + need ) > n_pre)) (PreH16 : (BasketballGreedyPrefix sorted d_pre i used )) (PreH17 : (Spec d_pre powers wins )),
  (IntArray.full p_pre n_pre sorted )
|--
  EX (p_after: (@list Z)),
  “ (Spec d_pre powers wins ) ”
  &&  “ (Permutation powers p_after ) ”
  &&  (IntArray.full p_pre n_pre p_after )
.

Definition solver_partial_solve_wit_1_pure :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (1 <= d_pre)) (PreH2 : (d_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (powers)))),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  (IntArray.full p_pre n_pre powers )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (1 <= d_pre)) (PreH2 : (d_pre <= 1000000000)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (powers)))),
  (IntArray.full p_pre n_pre powers )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= d_pre) ”
  &&  “ (d_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i powers 0)) /\ ((Znth i powers 0) <= 1000000000))) ”
  &&  “ (n_pre = (Zlength (powers))) ”
  &&  (IntArray.full p_pre n_pre powers )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 :=
forall (powers: (@list Z)) (p_pre: Z) (n_pre: Z) (d_pre: Z) (used: Z) (wins: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= d_pre)) (PreH3 : (d_pre <= 1000000000)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000)))) (PreH8 : (Permutation powers sorted )) (PreH9 : (mono_noninc sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (wins = i)) (PreH13 : (0 <= used)) (PreH14 : (used <= n_pre)) (PreH15 : (BasketballGreedyPrefix sorted d_pre i used )),
  (IntArray.full p_pre n_pre sorted )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= d_pre) ”
  &&  “ (d_pre <= 1000000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 1000000000))) ”
  &&  “ (Permutation powers sorted ) ”
  &&  “ (mono_noninc sorted ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (wins = i) ”
  &&  “ (0 <= used) ”
  &&  “ (used <= n_pre) ”
  &&  “ (BasketballGreedyPrefix sorted d_pre i used ) ”
  &&  (((p_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i p_pre i 0 n_pre sorted )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
