From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P050_440B_balancer_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))),
  ((( &( "sum" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> (sum + (Znth i values 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
|--
  “ ((sum + (Znth i values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (sum + (Znth i values 0) )) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "balance" ) )) # Int64  |-> 0)
  **  ((( &( "target" ) )) # Int64  |-> (sum ÷ n_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((( &( "balance" ) )) # Int64  |->_)
  **  ((( &( "target" ) )) # Int64  |-> (sum ÷ n_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((( &( "target" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((sum <> (INT64_MIN)) \/ (n_pre <> (-1))) ”
  &&  “ (n_pre <> 0) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "balance" ) )) # Int64  |-> 0)
  **  ((( &( "target" ) )) # Int64  |-> (sum ÷ n_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (values)) = n_pre)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (Pre values )) (PreH6 : (sum = (ListLib.sum (values)))) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (1000000000 * n_pre ))) (PreH9 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH10 : (0 <= target)) (PreH11 : (target <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (balance = (PrefixImbalance (values) (i)))) (PreH15 : (((-1000000000) * i ) <= balance)) (PreH16 : (balance <= (1000000000 * i ))) (PreH17 : (answer = (PrefixTransportCost (values) (i)))) (PreH18 : (0 <= answer)) (PreH19 : (answer <= ((1000000000 * i ) * i ))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> balance)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (values)) = n_pre)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (Pre values )) (PreH6 : (sum = (ListLib.sum (values)))) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (1000000000 * n_pre ))) (PreH9 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH10 : (0 <= target)) (PreH11 : (target <= 1000000000)) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (balance = (PrefixImbalance (values) (i)))) (PreH15 : (((-1000000000) * i ) <= balance)) (PreH16 : (balance <= (1000000000 * i ))) (PreH17 : (answer = (PrefixTransportCost (values) (i)))) (PreH18 : (0 <= answer)) (PreH19 : (answer <= ((1000000000 * i ) * i ))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> balance)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> balance)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((balance + ((Znth i values 0) - target ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (balance + ((Znth i values 0) - target ) )) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> balance)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ (((Znth i values 0) - target ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i values 0) - target )) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> (balance + ((Znth i values 0) - target ) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((answer + (balance + ((Znth i values 0) - target ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (answer + (balance + ((Znth i values 0) - target ) ) )) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> (balance + ((Znth i values 0) - target ) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((answer + (-(balance + ((Znth i values 0) - target ) )) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (answer + (-(balance + ((Znth i values 0) - target ) )) )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> (balance + ((Znth i values 0) - target ) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((balance + ((Znth i values 0) - target ) ) <> (INT64_MIN)) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> (balance + ((Znth i values 0) - target ) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> (balance + ((Znth i values 0) - target ) ))
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (-(balance + ((Znth i values 0) - target ) )) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "target" ) )) # Int64  |-> target)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "balance" ) )) # Int64  |-> (balance + ((Znth i values 0) - target ) ))
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (balance + ((Znth i values 0) - target ) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 = (ListLib.sum ((sublist (0) (0) (values))))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (1000000000 * 0 )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ (0 = (ListLib.sum ((sublist (0) (0) (values))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))),
  (0 = (ListLib.sum ((sublist (0) (0) (values)))))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((0 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((sum + (Znth i values 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (values))))) ”
  &&  “ (0 <= (sum + (Znth i values 0) )) ”
  &&  “ ((sum + (Znth i values 0) ) <= (1000000000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  TT && emp 
|--
  “ ((sum + (Znth i values 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (values))))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((sum + (Znth i values 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (values)))))
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (sum = (ListLib.sum (values))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (1000000000 * n_pre )) ”
  &&  “ ((sum ÷ n_pre ) = ((ListLib.sum (values)) ÷ n_pre )) ”
  &&  “ (0 <= (sum ÷ n_pre )) ”
  &&  “ ((sum ÷ n_pre ) <= 1000000000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ (0 = (PrefixImbalance (values) (0))) ”
  &&  “ (((-1000000000) * 0 ) <= 0) ”
  &&  “ (0 <= (1000000000 * 0 )) ”
  &&  “ (0 = (PrefixTransportCost (values) (0))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((1000000000 * 0 ) * 0 )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  TT && emp 
|--
  “ (0 = (PrefixTransportCost (values) (0))) ”
  &&  “ (0 = (PrefixImbalance (values) (0))) ”
  &&  “ ((sum ÷ n_pre ) <= 1000000000) ”
  &&  “ (0 <= (sum ÷ n_pre )) ”
  &&  “ ((sum ÷ n_pre ) = ((ListLib.sum (values)) ÷ n_pre )) ”
  &&  “ (sum = (ListLib.sum (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (0 = (PrefixTransportCost (values) (0)))
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (0 = (PrefixImbalance (values) (0)))
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((sum ÷ n_pre ) <= 1000000000)
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (0 <= (sum ÷ n_pre ))
.

Definition solver_entail_wit_3_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  ((sum ÷ n_pre ) = ((ListLib.sum (values)) ÷ n_pre ))
.

Definition solver_entail_wit_3_split_goal_6 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (sum = (ListLib.sum (values)))
.

Definition solver_entail_wit_3_split_goal_7 :=
forall (values: (@list Z)) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_4_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (sum = (ListLib.sum (values))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (1000000000 * n_pre )) ”
  &&  “ (target = ((ListLib.sum (values)) ÷ n_pre )) ”
  &&  “ (0 <= target) ”
  &&  “ (target <= 1000000000) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ ((balance + ((Znth i values 0) - target ) ) = (PrefixImbalance (values) ((i + 1 )))) ”
  &&  “ (((-1000000000) * (i + 1 ) ) <= (balance + ((Znth i values 0) - target ) )) ”
  &&  “ ((balance + ((Znth i values 0) - target ) ) <= (1000000000 * (i + 1 ) )) ”
  &&  “ ((answer + (-(balance + ((Znth i values 0) - target ) )) ) = (PrefixTransportCost (values) ((i + 1 )))) ”
  &&  “ (0 <= (answer + (-(balance + ((Znth i values 0) - target ) )) )) ”
  &&  “ ((answer + (-(balance + ((Znth i values 0) - target ) )) ) <= ((1000000000 * (i + 1 ) ) * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  TT && emp 
|--
  “ ((answer + (-(balance + ((Znth i values 0) - target ) )) ) <= ((1000000000 * (i + 1 ) ) * (i + 1 ) )) ”
  &&  “ ((answer + (-(balance + ((Znth i values 0) - target ) )) ) = (PrefixTransportCost (values) ((i + 1 )))) ”
  &&  “ (((-1000000000) * (i + 1 ) ) <= (balance + ((Znth i values 0) - target ) )) ”
  &&  “ ((balance + ((Znth i values 0) - target ) ) = (PrefixImbalance (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  ((answer + (-(balance + ((Znth i values 0) - target ) )) ) <= ((1000000000 * (i + 1 ) ) * (i + 1 ) ))
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  ((answer + (-(balance + ((Znth i values 0) - target ) )) ) = (PrefixTransportCost (values) ((i + 1 ))))
.

Definition solver_entail_wit_4_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (((-1000000000) * (i + 1 ) ) <= (balance + ((Znth i values 0) - target ) ))
.

Definition solver_entail_wit_4_1_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) < 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  ((balance + ((Znth i values 0) - target ) ) = (PrefixImbalance (values) ((i + 1 ))))
.

Definition solver_entail_wit_4_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (sum = (ListLib.sum (values))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (1000000000 * n_pre )) ”
  &&  “ (target = ((ListLib.sum (values)) ÷ n_pre )) ”
  &&  “ (0 <= target) ”
  &&  “ (target <= 1000000000) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ ((balance + ((Znth i values 0) - target ) ) = (PrefixImbalance (values) ((i + 1 )))) ”
  &&  “ (((-1000000000) * (i + 1 ) ) <= (balance + ((Znth i values 0) - target ) )) ”
  &&  “ ((balance + ((Znth i values 0) - target ) ) <= (1000000000 * (i + 1 ) )) ”
  &&  “ ((answer + (balance + ((Znth i values 0) - target ) ) ) = (PrefixTransportCost (values) ((i + 1 )))) ”
  &&  “ (0 <= (answer + (balance + ((Znth i values 0) - target ) ) )) ”
  &&  “ ((answer + (balance + ((Znth i values 0) - target ) ) ) <= ((1000000000 * (i + 1 ) ) * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  TT && emp 
|--
  “ ((answer + (balance + ((Znth i values 0) - target ) ) ) <= ((1000000000 * (i + 1 ) ) * (i + 1 ) )) ”
  &&  “ ((answer + (balance + ((Znth i values 0) - target ) ) ) = (PrefixTransportCost (values) ((i + 1 )))) ”
  &&  “ ((balance + ((Znth i values 0) - target ) ) = (PrefixImbalance (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  ((answer + (balance + ((Znth i values 0) - target ) ) ) <= ((1000000000 * (i + 1 ) ) * (i + 1 ) ))
.

Definition solver_entail_wit_4_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  ((answer + (balance + ((Znth i values 0) - target ) ) ) = (PrefixTransportCost (values) ((i + 1 ))))
.

Definition solver_entail_wit_4_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((balance + ((Znth i values 0) - target ) ) >= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (Pre values )) (PreH8 : (sum = (ListLib.sum (values)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= (1000000000 * n_pre ))) (PreH11 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH12 : (0 <= target)) (PreH13 : (target <= 1000000000)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (balance = (PrefixImbalance (values) (i)))) (PreH17 : (((-1000000000) * i ) <= balance)) (PreH18 : (balance <= (1000000000 * i ))) (PreH19 : (answer = (PrefixTransportCost (values) (i)))) (PreH20 : (0 <= answer)) (PreH21 : (answer <= ((1000000000 * i ) * i ))),
  ((balance + ((Znth i values 0) - target ) ) = (PrefixImbalance (values) ((i + 1 ))))
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (Spec values answer ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  TT && emp 
|--
  “ (Spec values answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  (Spec values answer )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (sum: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (sum = (ListLib.sum ((sublist (0) (i) (values)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= (1000000000 * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (sum = (ListLib.sum ((sublist (0) (i) (values))))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (1000000000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (answer: Z) (balance: Z) (i: Z) (target: Z) (sum: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (Pre values )) (PreH7 : (sum = (ListLib.sum (values)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= (1000000000 * n_pre ))) (PreH10 : (target = ((ListLib.sum (values)) ÷ n_pre ))) (PreH11 : (0 <= target)) (PreH12 : (target <= 1000000000)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (balance = (PrefixImbalance (values) (i)))) (PreH16 : (((-1000000000) * i ) <= balance)) (PreH17 : (balance <= (1000000000 * i ))) (PreH18 : (answer = (PrefixTransportCost (values) (i)))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((1000000000 * i ) * i ))),
  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 50000) ”
  &&  “ ((Zlength (values)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (Pre values ) ”
  &&  “ (sum = (ListLib.sum (values))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= (1000000000 * n_pre )) ”
  &&  “ (target = ((ListLib.sum (values)) ÷ n_pre )) ”
  &&  “ (0 <= target) ”
  &&  “ (target <= 1000000000) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (balance = (PrefixImbalance (values) (i))) ”
  &&  “ (((-1000000000) * i ) <= balance) ”
  &&  “ (balance <= (1000000000 * i )) ”
  &&  “ (answer = (PrefixTransportCost (values) (i))) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((1000000000 * i ) * i )) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
