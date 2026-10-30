From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "mn" ) )) # Int  |-> 101)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "mn" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (101 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 101) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "mn" ) )) # Int  |-> 101)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "mn" ) )) # Int  |-> mn)
|--
  “ ((sum + (Znth i values 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sum + (Znth i values 0) )) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i values 0) ))
  **  ((( &( "mn" ) )) # Int  |-> (Znth i values 0))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i values 0) ))
  **  ((( &( "mn" ) )) # Int  |-> mn)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> sum)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (((Znth i values 0) <> (INT_MIN)) \/ (x <> (-1))) ”
  &&  “ (x <> 0) ”
.

Definition solver_safety_wit_10 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) )) ”
).

Definition solver_safety_wit_10_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((INT_MIN) <= ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) )) ”
.

Definition solver_safety_wit_11 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((mn * x ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mn * x )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((mn * x ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mn * x )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((mn * x ) <= INT_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((INT_MIN) <= (mn * x )) ”
.

Definition solver_safety_wit_12 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) )) ”
).

Definition solver_safety_wit_12_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((INT_MIN) <= (((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) )) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (((Znth i values 0) <> (INT_MIN)) \/ (x <> (-1))) ”
  &&  “ (x <> 0) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (((sum - (Znth i values 0) ) - mn ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((sum - (Znth i values 0) ) - mn )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((sum - (Znth i values 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sum - (Znth i values 0) )) ”
.

Definition solver_safety_wit_16 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ))
|--
  “ ((x + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x + 1 )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ))
|--
  “ ((x + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x + 1 )) ”
).

Definition solver_safety_wit_16_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ))
|--
  “ ((x + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_16_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ))
|--
  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition solver_safety_wit_17 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((x + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x + 1 )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((x + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x + 1 )) ”
).

Definition solver_safety_wit_17_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((x + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition solver_safety_wit_18 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((x + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x + 1 )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((x + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x + 1 )) ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((x + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x > (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (100 * 0 )) ”
  &&  “ (1 <= 101) ”
  &&  “ (101 <= 101) ”
  &&  “ (PrefixSummary values 0 0 101 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ (PrefixSummary values 0 0 101 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  (PrefixSummary values 0 0 101 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))
.

Definition solver_entail_wit_2_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (sum + (Znth i values 0) )) ”
  &&  “ ((sum + (Znth i values 0) ) <= (100 * (i + 1 ) )) ”
  &&  “ (1 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 101) ”
  &&  “ (PrefixSummary values (i + 1 ) (sum + (Znth i values 0) ) (Znth i values 0) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  TT && emp 
|--
  “ (PrefixSummary values (i + 1 ) (sum + (Znth i values 0) ) (Znth i values 0) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (PrefixSummary values (i + 1 ) (sum + (Znth i values 0) ) (Znth i values 0) )
.

Definition solver_entail_wit_2_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (sum + (Znth i values 0) )) ”
  &&  “ ((sum + (Znth i values 0) ) <= (100 * (i + 1 ) )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 101) ”
  &&  “ (PrefixSummary values (i + 1 ) (sum + (Znth i values 0) ) mn ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  TT && emp 
|--
  “ (PrefixSummary values (i + 1 ) (sum + (Znth i values 0) ) mn ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (PrefixSummary values (i + 1 ) (sum + (Znth i values 0) ) mn )
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= sum) ”
  &&  “ (SearchMinimum values sum mn 0 2 sum ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  TT && emp 
|--
  “ (SearchMinimum values sum mn 0 2 sum ) ”
  &&  “ (mn <= 100) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (SearchMinimum values sum mn 0 2 sum )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (mn <= 100)
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (PrefixSummary values n_pre sum mn )
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))
.

Definition solver_entail_wit_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i 2 answer ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  TT && emp 
|--
  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))
.

Definition solver_entail_wit_5_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= (x + 1 )) ”
  &&  “ ((x + 1 ) <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) )) ”
  &&  “ (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) <= sum) ”
  &&  “ (SearchMinimum values sum mn i (x + 1 ) ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  TT && emp 
|--
  “ (SearchMinimum values sum mn i (x + 1 ) ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) ) ”
  &&  “ (0 <= ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) )) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (SearchMinimum values sum mn i (x + 1 ) ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) )
.

Definition solver_entail_wit_5_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) < answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (0 <= ((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ))
.

Definition solver_entail_wit_5_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= (x + 1 )) ”
  &&  “ ((x + 1 ) <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i (x + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  TT && emp 
|--
  “ (SearchMinimum values sum mn i (x + 1 ) answer ) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (((((sum - (Znth i values 0) ) - mn ) + ((Znth i values 0) ÷ x ) ) + (mn * x ) ) >= answer)) (PreH2 : (x <= (Znth i values 0))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn )) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * n_pre ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values 0) + 1 ))) (PreH16 : (0 <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer )) (PreH19 : (((Znth i values 0) % ( x ) ) = 0)),
  (SearchMinimum values sum mn i (x + 1 ) answer )
.

Definition solver_entail_wit_5_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= (x + 1 )) ”
  &&  “ ((x + 1 ) <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i (x + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  TT && emp 
|--
  “ (SearchMinimum values sum mn i (x + 1 ) answer ) ”
  &&  emp
).

Definition solver_entail_wit_5_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) <> 0)),
  (SearchMinimum values sum mn i (x + 1 ) answer )
.

Definition solver_entail_wit_6 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x > (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn (i + 1 ) 2 answer ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x > (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  TT && emp 
|--
  “ (SearchMinimum values sum mn (i + 1 ) 2 answer ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x > (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  (SearchMinimum values sum mn (i + 1 ) 2 answer )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x > (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values answer ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  TT && emp 
|--
  “ (Spec values answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer )),
  (Spec values answer )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * i )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 101) ”
  &&  “ (PrefixSummary values i sum mn ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (100 * i ))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * i )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 101) ”
  &&  “ (PrefixSummary values i sum mn ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (mn: Z) (sum: Z) (i: Z) (PreH1 : ((Znth i values 0) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (100 * i ))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn )),
  (IntArray.full a_pre n_pre values )
|--
  “ ((Znth i values 0) < mn) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * i )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 101) ”
  &&  “ (PrefixSummary values i sum mn ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (PrefixSummary values n_pre sum mn )) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (100 * n_pre ))) (PreH8 : (1 <= mn)) (PreH9 : (mn <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= x)) (PreH13 : (x <= ((Znth i values 0) + 1 ))) (PreH14 : (0 <= answer)) (PreH15 : (answer <= sum)) (PreH16 : (SearchMinimum values sum mn i x answer )),
  (IntArray.full a_pre n_pre values )
|--
  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= x) ”
  &&  “ (x <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i x answer ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )),
  (IntArray.full a_pre n_pre values )
|--
  “ (x <= (Znth i values 0)) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= x) ”
  &&  “ (x <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i x answer ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
|--
  “ (x <= (Znth i values 0)) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= x) ”
  &&  “ (x <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i x answer ) ”
  &&  “ (((Znth i values 0) % ( x ) ) = 0) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (x: Z) (i: Z) (sum: Z) (mn: Z) (PreH1 : (x <= (Znth i values 0))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn )) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (100 * n_pre ))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values 0) + 1 ))) (PreH15 : (0 <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer )) (PreH18 : (((Znth i values 0) % ( x ) ) = 0)),
  (IntArray.full a_pre n_pre values )
|--
  “ (x <= (Znth i values 0)) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 50000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 100))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (PrefixSummary values n_pre sum mn ) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (100 * n_pre )) ”
  &&  “ (1 <= mn) ”
  &&  “ (mn <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= x) ”
  &&  “ (x <= ((Znth i values 0) + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= sum) ”
  &&  “ (SearchMinimum values sum mn i x answer ) ”
  &&  “ (((Znth i values 0) % ( x ) ) = 0) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
