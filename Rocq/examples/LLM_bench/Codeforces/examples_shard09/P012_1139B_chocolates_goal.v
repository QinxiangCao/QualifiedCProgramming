From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "prev" ) )) # Int64  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "prev" ) )) # Int64  |-> 0)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "prev" ) )) # Int64  |-> 0)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((-1) <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= total)) (PreH8 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH9 : (0 <= prev)) (PreH10 : (prev <= 1000000000)) (PreH11 : (SuffixDominantState values (i + 1 ) total prev )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH10 : (0 <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1 ) total prev )),
  ((( &( "take" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH10 : (0 <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1 ) total prev )),
  ((( &( "take" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i <> (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  ((( &( "take" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((prev - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (prev - 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i <> (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  ((( &( "take" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) > (Znth i values 0))) (PreH2 : (i <> (n_pre - 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH12 : (0 <= prev)) (PreH13 : (prev <= 1000000000)) (PreH14 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) <= (Znth i values 0))) (PreH2 : (i <> (n_pre - 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH12 : (0 <= prev)) (PreH13 : (prev <= 1000000000)) (PreH14 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (prev - 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) < 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) < 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (prev - 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i = (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ ((total + (Znth i values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (Znth i values 0) )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) < 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ ((total + 0 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + 0 )) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) < 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ ((total + 0 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + 0 )) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) >= 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ ((total + (Znth i values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (Znth i values 0) )) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) >= 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "take" ) )) # Int64  |-> (prev - 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "prev" ) )) # Int64  |-> prev)
|--
  “ ((total + (prev - 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (prev - 1 ) )) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i = (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + (Znth i values 0) ))
  **  ((( &( "prev" ) )) # Int64  |-> (Znth i values 0))
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) < 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + 0 ))
  **  ((( &( "prev" ) )) # Int64  |-> 0)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) < 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + 0 ))
  **  ((( &( "prev" ) )) # Int64  |-> 0)
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) >= 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + (Znth i values 0) ))
  **  ((( &( "prev" ) )) # Int64  |-> (Znth i values 0))
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) >= 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + (prev - 1 ) ))
  **  ((( &( "prev" ) )) # Int64  |-> (prev - 1 ))
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (((n_pre - (n_pre - 1 ) ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1000000000) ”
  &&  “ (SuffixDominantState values ((n_pre - 1 ) + 1 ) 0 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ (SuffixDominantState values ((n_pre - 1 ) + 1 ) 0 0 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  (SuffixDominantState values ((n_pre - 1 ) + 1 ) 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_2_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i = (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (0 <= (total + (Znth i values 0) )) ”
  &&  “ ((total + (Znth i values 0) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + (Znth i values 0) ) (Znth i values 0) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i = (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  TT && emp 
|--
  “ (SuffixDominantState values (((n_pre - 1 ) - 1 ) + 1 ) (total + (Znth (n_pre - 1 ) values 0) ) (Znth (n_pre - 1 ) values 0) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i = (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  (SuffixDominantState values (((n_pre - 1 ) - 1 ) + 1 ) (total + (Znth (n_pre - 1 ) values 0) ) (Znth (n_pre - 1 ) values 0) )
.

Definition solver_entail_wit_2_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) < 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (0 <= (total + 0 )) ”
  &&  “ ((total + 0 ) <= (((n_pre - (i - 1 ) ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1000000000) ”
  &&  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + 0 ) 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) < 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + 0 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) < 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (SuffixDominantState values ((i - 1 ) + 1 ) (total + 0 ) 0 )
.

Definition solver_entail_wit_2_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) < 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (0 <= (total + 0 )) ”
  &&  “ ((total + 0 ) <= (((n_pre - (i - 1 ) ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1000000000) ”
  &&  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + 0 ) 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) < 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + 0 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) < 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (SuffixDominantState values ((i - 1 ) + 1 ) (total + 0 ) 0 )
.

Definition solver_entail_wit_2_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) >= 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (0 <= (total + (Znth i values 0) )) ”
  &&  “ ((total + (Znth i values 0) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + (Znth i values 0) ) (Znth i values 0) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) >= 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + (Znth i values 0) ) (Znth i values 0) ) ”
  &&  emp
).

Definition solver_entail_wit_2_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((Znth i values 0) >= 0)) (PreH2 : ((prev - 1 ) > (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (SuffixDominantState values ((i - 1 ) + 1 ) (total + (Znth i values 0) ) (Znth i values 0) )
.

Definition solver_entail_wit_2_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) >= 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < n_pre) ”
  &&  “ (0 <= (total + (prev - 1 ) )) ”
  &&  “ ((total + (prev - 1 ) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= (prev - 1 )) ”
  &&  “ ((prev - 1 ) <= 1000000000) ”
  &&  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + (prev - 1 ) ) (prev - 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) >= 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1 ) + 1 ) (total + (prev - 1 ) ) (prev - 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) >= 0)) (PreH2 : ((prev - 1 ) <= (Znth i values 0))) (PreH3 : (i <> (n_pre - 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH13 : (0 <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1 ) total prev )),
  (SuffixDominantState values ((i - 1 ) + 1 ) (total + (prev - 1 ) ) (prev - 1 ) )
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH10 : (0 <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values total ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH10 : (0 <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1 ) total prev )),
  TT && emp 
|--
  “ (Spec values total ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH10 : (0 <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1 ) total prev )),
  (Spec values total )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i = (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (i = (n_pre - 1 )) ”
  &&  “ (i >= 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (((n_pre - i ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= prev) ”
  &&  “ (prev <= 1000000000) ”
  &&  “ (SuffixDominantState values (i + 1 ) total prev ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : (i <> (n_pre - 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH11 : (0 <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ (i <> (n_pre - 1 )) ”
  &&  “ (i >= 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (((n_pre - i ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= prev) ”
  &&  “ (prev <= 1000000000) ”
  &&  “ (SuffixDominantState values (i + 1 ) total prev ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prev: Z) (total: Z) (i: Z) (PreH1 : ((prev - 1 ) > (Znth i values 0))) (PreH2 : (i <> (n_pre - 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= (((n_pre - i ) - 1 ) * 1000000000 ))) (PreH12 : (0 <= prev)) (PreH13 : (prev <= 1000000000)) (PreH14 : (SuffixDominantState values (i + 1 ) total prev )),
  (IntArray.full a_pre n_pre values )
|--
  “ ((prev - 1 ) > (Znth i values 0)) ”
  &&  “ (i <> (n_pre - 1 )) ”
  &&  “ (i >= 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (((n_pre - i ) - 1 ) * 1000000000 )) ”
  &&  “ (0 <= prev) ”
  &&  “ (prev <= 1000000000) ”
  &&  “ (SuffixDominantState values (i + 1 ) total prev ) ”
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
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Axiom proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
