From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P068_1416C_xor_inverse_lib.
Local Open Scope sac.

(*----- Function solve -----*)

Definition solve_safety_wit_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= n_total)) (PreH4 : (n_total <= 300000)) (PreH5 : ((-1) <= bit_pre)) (PreH6 : (bit_pre < 30)) (PreH7 : ((Zlength (before)) = n_total)) (PreH8 : ((Zlength (scratch)) = n_total)) (PreH9 : ((Zlength (cost_before)) = 30)) (PreH10 : (0 <= capacity)) (PreH11 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH12 : (CostBound cost_before capacity )) (PreH13 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH14 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (bit_pre >= 0)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : ((-1) <= bit_pre)) (PreH7 : (bit_pre < 30)) (PreH8 : ((Zlength (before)) = n_total)) (PreH9 : ((Zlength (scratch)) = n_total)) (PreH10 : ((Zlength (cost_before)) = 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : (CostBound cost_before capacity )) (PreH14 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  “ ((r_pre - l_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r_pre - l_pre )) ”
.

Definition solve_safety_wit_3 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (bit_pre >= 0)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : ((-1) <= bit_pre)) (PreH7 : (bit_pre < 30)) (PreH8 : ((Zlength (before)) = n_total)) (PreH9 : ((Zlength (scratch)) = n_total)) (PreH10 : ((Zlength (cost_before)) = 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : (CostBound cost_before capacity )) (PreH14 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH15 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_4 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) > 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  ((( &( "ones" ) )) # Int64  |->_)
  **  ((( &( "zeros" ) )) # Int64  |-> 0)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_5 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) > 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  ((( &( "zeros" ) )) # Int64  |->_)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_6 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (0 <= (Znth i before 0)) ”
  &&  “ (bit_pre <= 31) ”
  &&  “ (0 <= bit_pre) ”
.

Definition solve_safety_wit_7 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_8 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_9 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros )) ”
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros )) ”
).

Definition solve_safety_wit_9_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ) <= INT64_MAX) ”
.

Definition solve_safety_wit_9_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ ((INT64_MIN) <= ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros )) ”
.

Definition solve_safety_wit_10 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ ((ones + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (ones + 1 )) ”
.

Definition solve_safety_wit_11 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_12 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_13 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones )) ”
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones )) ”
).

Definition solve_safety_wit_13_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ) <= INT64_MAX) ”
.

Definition solve_safety_wit_13_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ ((INT64_MIN) <= ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones )) ”
.

Definition solve_safety_wit_14 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ ((zeros + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (zeros + 1 )) ”
.

Definition solve_safety_wit_15 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_16 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> (ones + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_17 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> (ones + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) + zeros ))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_18 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> (zeros + 1 ))
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_19 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "zeros" ) )) # Int64  |-> (zeros + 1 ))
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) + ones ))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_20 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current)) = n_total)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= (Znth i before 0)) ”
  &&  “ (bit_pre <= 31) ”
  &&  “ (0 <= bit_pre) ”
.

Definition solve_safety_wit_21 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current)) = n_total)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_22 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current)) = n_total)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_23 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((p + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solve_safety_wit_24 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_25 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> (p + 1 ))
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_26 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> (p + 1 ))
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_27 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_28 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_29 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= (Znth i before 0)) ”
  &&  “ (bit_pre <= 31) ”
  &&  “ (0 <= bit_pre) ”
.

Definition solve_safety_wit_30 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_31 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((p + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solve_safety_wit_32 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_33 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "p" ) )) # Int  |-> (p + 1 ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_34 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "p" ) )) # Int  |-> (p + 1 ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_35 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_36 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_37 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))) (current: (@list Z)) (partitioned: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (value: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= i)) (PreH3 : (i < r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (l_pre <= mid)) (PreH7 : (mid <= r_pre)) (PreH8 : (mid = (l_pre + zeros ))) (PreH9 : (p = r_pre)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((-1) <= (bit_pre - 1 ))) (PreH15 : ((bit_pre - 1 ) < 30)) (PreH16 : ((Zlength (before)) = n_total)) (PreH17 : ((Zlength (current)) = n_total)) (PreH18 : ((Zlength (scratch_current)) = n_total)) (PreH19 : (mid <= (Zlength (current)))) (PreH20 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH21 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH22 : ((Zlength (counted_costs)) = 30)) (PreH23 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0))))) (PreH24 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH26 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH27 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH28 : ((Znth i scratch_current __default__App_option_Z) = (Some (value)))) (PreH29 : (value = (Znth (i - l_pre ) partitioned 0))) (PreH30 : (0 <= value)) (PreH31 : (value <= 1000000000)) (PreH32 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH33 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH34 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH35 : (PartitionCopyBack before current partitioned l_pre r_pre i )),
  (IntArray.full a_p (Zlength (current)) (replace_Znth (i) (value) (current)) )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_38 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))) (current: (@list Z)) (partitioned: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (value: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= i)) (PreH3 : (i < r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (l_pre <= mid)) (PreH7 : (mid <= r_pre)) (PreH8 : (mid = (l_pre + zeros ))) (PreH9 : (p = r_pre)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((-1) <= (bit_pre - 1 ))) (PreH15 : ((bit_pre - 1 ) < 30)) (PreH16 : ((Zlength (before)) = n_total)) (PreH17 : ((Zlength (current)) = n_total)) (PreH18 : ((Zlength (scratch_current)) = n_total)) (PreH19 : (mid <= (Zlength (current)))) (PreH20 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH21 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH22 : ((Zlength (counted_costs)) = 30)) (PreH23 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0))))) (PreH24 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH26 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH27 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH28 : ((Znth i scratch_current __default__App_option_Z) = (Some (value)))) (PreH29 : (value = (Znth (i - l_pre ) partitioned 0))) (PreH30 : (0 <= value)) (PreH31 : (value <= 1000000000)) (PreH32 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH33 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH34 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH35 : (PartitionCopyBack before current partitioned l_pre r_pre i )),
  (IntArray.full a_p (Zlength (current)) (replace_Znth (i) (value) (current)) )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_39 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i: Z) __default__App_option_Z __default__List_Z (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= r_pre)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (before)) = n_total)) (PreH18 : ((Zlength (current)) = n_total)) (PreH19 : ((Zlength (scratch_current)) = n_total)) (PreH20 : (mid <= (Zlength (current)))) (PreH21 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH22 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH23 : ((Zlength (counted_costs)) = 30)) (PreH24 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0))))) (PreH25 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH27 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH28 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH29 : ((i < r_pre) -> ((((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i - l_pre ) partitioned 0))) /\ ((Znth (i - l_pre ) partitioned 0) <= 1000000000)))) (PreH30 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH31 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH32 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH33 : (PartitionCopyBack before current partitioned l_pre r_pre i )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((bit_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (bit_pre - 1 )) ”
.

Definition solve_safety_wit_40 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i: Z) __default__App_option_Z __default__List_Z (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= r_pre)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (before)) = n_total)) (PreH18 : ((Zlength (current)) = n_total)) (PreH19 : ((Zlength (scratch_current)) = n_total)) (PreH20 : (mid <= (Zlength (current)))) (PreH21 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH22 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH23 : ((Zlength (counted_costs)) = 30)) (PreH24 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0))))) (PreH25 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH27 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH28 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH29 : ((i < r_pre) -> ((((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i - l_pre ) partitioned 0))) /\ ((Znth (i - l_pre ) partitioned 0) <= 1000000000)))) (PreH30 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH31 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH32 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH33 : (PartitionCopyBack before current partitioned l_pre r_pre i )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_41 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= mid)) (PreH3 : (mid <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (mid = (l_pre + zeros ))) (PreH7 : (p = r_pre)) (PreH8 : (0 <= bit_pre)) (PreH9 : (bit_pre < 30)) (PreH10 : (0 <= capacity)) (PreH11 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH12 : ((-1) <= (bit_pre - 1 ))) (PreH13 : ((bit_pre - 1 ) < 30)) (PreH14 : ((Zlength (partition_before)) = n_total)) (PreH15 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH16 : ((Zlength (partition_scratch)) = n_total)) (PreH17 : ((Zlength (first_after)) = n_total)) (PreH18 : ((Zlength (first_scratch)) = n_total)) (PreH19 : ((Zlength (first_cost)) = 30)) (PreH20 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0))))) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH22 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH23 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH24 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH25 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH26 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH27 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ ((bit_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (bit_pre - 1 )) ”
.

Definition solve_safety_wit_42 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= mid)) (PreH3 : (mid <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (mid = (l_pre + zeros ))) (PreH7 : (p = r_pre)) (PreH8 : (0 <= bit_pre)) (PreH9 : (bit_pre < 30)) (PreH10 : (0 <= capacity)) (PreH11 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH12 : ((-1) <= (bit_pre - 1 ))) (PreH13 : ((bit_pre - 1 ) < 30)) (PreH14 : ((Zlength (partition_before)) = n_total)) (PreH15 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH16 : ((Zlength (partition_scratch)) = n_total)) (PreH17 : ((Zlength (first_after)) = n_total)) (PreH18 : ((Zlength (first_scratch)) = n_total)) (PreH19 : ((Zlength (first_cost)) = 30)) (PreH20 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0))))) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH22 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH23 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH24 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH25 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH26 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH27 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_entail_wit_1 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) > 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  EX (current_costs: (@list (@list Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((0 + 0 ) = (l_pre - l_pre )) ”
  &&  “ (0 <= n_total) ”
  &&  “ (0 <= n_total) ”
  &&  “ (SolveCountPrefix before cost_before current_costs l_pre l_pre bit_pre 0 0 ) ”
  &&  “ (CostBound current_costs (capacity + ((l_pre - l_pre ) * (l_pre - l_pre ) ) ) ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) > 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i before 0)) /\ ((Znth i before 0) <= 1000000000)))),
  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  EX (current_costs: (@list (@list Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((0 + 0 ) = (l_pre - l_pre )) ”
  &&  “ (0 <= n_total) ”
  &&  “ (0 <= n_total) ”
  &&  “ (SolveCountPrefix before cost_before current_costs l_pre l_pre bit_pre 0 0 ) ”
  &&  “ (CostBound current_costs (capacity + ((l_pre - l_pre ) * (l_pre - l_pre ) ) ) ) ”
  &&  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
).

Definition solve_entail_wit_2_1 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs_2)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs_2 __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> ((Znth 1 (Znth bit_pre current_costs_2 __default__List_Z) 0) + zeros ))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs_2)) )
|--
  EX (current_costs: (@list (@list Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (0 <= zeros) ”
  &&  “ (0 <= (ones + 1 )) ”
  &&  “ ((zeros + (ones + 1 ) ) = ((i + 1 ) - l_pre )) ”
  &&  “ (zeros <= n_total) ”
  &&  “ ((ones + 1 ) <= n_total) ”
  &&  “ (SolveCountPrefix before cost_before current_costs l_pre (i + 1 ) bit_pre zeros (ones + 1 ) ) ”
  &&  “ (CostBound current_costs (capacity + (((i + 1 ) - l_pre ) * ((i + 1 ) - l_pre ) ) ) ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  TT && emp 
|--
  “ (CostBound current_costs_2 (capacity + (((i + 1 ) - l_pre ) * ((i + 1 ) - l_pre ) ) ) ) ”
  &&  “ (SolveCountPrefix before cost_before current_costs_2 l_pre (i + 1 ) bit_pre zeros (ones + 1 ) ) ”
  &&  “ (((Znth 1 (Znth bit_pre current_costs_2 __default__List_Z) 0) + zeros ) = (Znth 1 (Znth bit_pre current_costs_2 __default__List_Z) 0)) ”
  &&  emp
).

Definition solve_entail_wit_2_1_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (CostBound current_costs_2 (capacity + (((i + 1 ) - l_pre ) * ((i + 1 ) - l_pre ) ) ) )
.

Definition solve_entail_wit_2_1_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (SolveCountPrefix before cost_before current_costs_2 l_pre (i + 1 ) bit_pre zeros (ones + 1 ) )
.

Definition solve_entail_wit_2_1_split_goal_3 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (((Znth 1 (Znth bit_pre current_costs_2 __default__List_Z) 0) + zeros ) = (Znth 1 (Znth bit_pre current_costs_2 __default__List_Z) 0))
.

Definition solve_entail_wit_2_2 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs_2)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 (Znth bit_pre current_costs_2 __default__List_Z) 0) + ones ))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs_2 __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs_2)) )
|--
  EX (current_costs: (@list (@list Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (0 <= (zeros + 1 )) ”
  &&  “ (0 <= ones) ”
  &&  “ (((zeros + 1 ) + ones ) = ((i + 1 ) - l_pre )) ”
  &&  “ ((zeros + 1 ) <= n_total) ”
  &&  “ (ones <= n_total) ”
  &&  “ (SolveCountPrefix before cost_before current_costs l_pre (i + 1 ) bit_pre (zeros + 1 ) ones ) ”
  &&  “ (CostBound current_costs (capacity + (((i + 1 ) - l_pre ) * ((i + 1 ) - l_pre ) ) ) ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  TT && emp 
|--
  “ (CostBound current_costs_2 (capacity + (((i + 1 ) - l_pre ) * ((i + 1 ) - l_pre ) ) ) ) ”
  &&  “ (SolveCountPrefix before cost_before current_costs_2 l_pre (i + 1 ) bit_pre (zeros + 1 ) ones ) ”
  &&  “ (((Znth 0 (Znth bit_pre current_costs_2 __default__List_Z) 0) + ones ) = (Znth 0 (Znth bit_pre current_costs_2 __default__List_Z) 0)) ”
  &&  emp
).

Definition solve_entail_wit_2_2_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (CostBound current_costs_2 (capacity + (((i + 1 ) - l_pre ) * ((i + 1 ) - l_pre ) ) ) )
.

Definition solve_entail_wit_2_2_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (SolveCountPrefix before cost_before current_costs_2 l_pre (i + 1 ) bit_pre (zeros + 1 ) ones )
.

Definition solve_entail_wit_2_2_split_goal_3 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs_2: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs_2 l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs_2 (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (((Znth 0 (Znth bit_pre current_costs_2 __default__List_Z) 0) + ones ) = (Znth 0 (Znth bit_pre current_costs_2 __default__List_Z) 0))
.

Definition solve_entail_wit_3 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_total)) -> ((0 <= (Znth k_2 before 0)) /\ ((Znth k_2 before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  EX (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre l_pre l_pre 0 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) <= INT64_MAX)) (PreH2 : ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) <= INT64_MAX)) (PreH3 : ((Znth 1 (Znth bit_pre current_costs __default__List_Z) 0) >= INT64_MIN)) (PreH4 : ((Znth 0 (Znth bit_pre current_costs __default__List_Z) 0) >= INT64_MIN)) (PreH5 : (i >= r_pre)) (PreH6 : (0 <= l_pre)) (PreH7 : (l_pre <= i)) (PreH8 : (i <= r_pre)) (PreH9 : (r_pre <= n_total)) (PreH10 : (n_total <= 300000)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch)) = n_total)) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_total)) -> ((0 <= (Znth k_2 before 0)) /\ ((Znth k_2 before 0) <= 1000000000)))) (PreH18 : (0 <= zeros)) (PreH19 : (0 <= ones)) (PreH20 : ((zeros + ones ) = (i - l_pre ))) (PreH21 : (zeros <= n_total)) (PreH22 : (ones <= n_total)) (PreH23 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH24 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )),
  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  EX (counted_costs: (@list (@list Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch l_pre r_pre bit_pre l_pre l_pre 0 ) ”
  &&  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
).

Definition solve_entail_wit_4_1 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= (i + 1 )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre (i + 1 ) (p + 1 ) 0 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  TT && emp 
|--
  “ (StablePartitionPrefix before (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)) l_pre r_pre bit_pre (i + 1 ) (p + 1 ) 0 ) ”
  &&  “ ((Zlength ((replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)))) = n_total) ”
  &&  emp
).

Definition solve_entail_wit_4_1_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  (StablePartitionPrefix before (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)) l_pre r_pre bit_pre (i + 1 ) (p + 1 ) 0 )
.

Definition solve_entail_wit_4_1_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  ((Zlength ((replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)))) = n_total)
.

Definition solve_entail_wit_4_2 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= p) ”
  &&  “ (p <= (i + 1 )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre (i + 1 ) p 0 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  TT && emp 
|--
  “ (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre (i + 1 ) p 0 ) ”
  &&  emp
).

Definition solve_entail_wit_4_2_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current_2)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre (i + 1 ) p 0 )
.

Definition solve_entail_wit_5 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current_2)) = n_total)) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_total)) -> ((0 <= (Znth k_2 before 0)) /\ ((Znth k_2 before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= p) ”
  &&  “ (p <= p) ”
  &&  “ (p <= r_pre) ”
  &&  “ (p = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre l_pre p 1 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current_2)) = n_total)) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_total)) -> ((0 <= (Znth k_2 before 0)) /\ ((Znth k_2 before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  TT && emp 
|--
  “ (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre l_pre p 1 ) ”
  &&  “ (p = (l_pre + zeros )) ”
  &&  emp
).

Definition solve_entail_wit_5_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current_2)) = n_total)) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_total)) -> ((0 <= (Znth k_2 before 0)) /\ ((Znth k_2 before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre l_pre p 1 )
.

Definition solve_entail_wit_5_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current_2: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current_2)) = n_total)) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_total)) -> ((0 <= (Znth k_2 before 0)) /\ ((Znth k_2 before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 0 )),
  (p = (l_pre + zeros ))
.

Definition solve_entail_wit_6 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (p < r_pre) ”
  &&  “ (ones <= INT64_MAX) ”
  &&  “ (zeros <= INT64_MAX) ”
  &&  “ (ones >= INT64_MIN) ”
  &&  “ (zeros >= INT64_MIN) ”
  &&  “ (mid <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (bit_pre <= INT_MAX) ”
  &&  “ (l_pre <= INT_MAX) ”
  &&  “ (mid >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (bit_pre >= INT_MIN) ”
  &&  “ (l_pre >= INT_MIN) ”
  &&  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= p) ”
  &&  “ (p <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 ) ”
  &&  “ ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  (IntArray.full a_p n_total before )
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (r_pre <= INT_MAX)) (PreH10 : (l_pre <= INT_MAX)) (PreH11 : (p >= INT_MIN)) (PreH12 : (mid >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (bit_pre >= INT_MIN)) (PreH15 : (r_pre >= INT_MIN)) (PreH16 : (l_pre >= INT_MIN)) (PreH17 : (i < r_pre)) (PreH18 : (0 <= l_pre)) (PreH19 : (l_pre <= i)) (PreH20 : (i <= r_pre)) (PreH21 : (r_pre <= n_total)) (PreH22 : (n_total <= 300000)) (PreH23 : (l_pre <= mid)) (PreH24 : (mid <= p)) (PreH25 : (p <= r_pre)) (PreH26 : (mid = (l_pre + zeros ))) (PreH27 : (0 <= bit_pre)) (PreH28 : (bit_pre < 30)) (PreH29 : (0 <= capacity)) (PreH30 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (scratch_current)) = n_total)) (PreH33 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH34 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH35 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH36 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH37 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  TT && emp 
|--
  “ (p < r_pre) ”
  &&  emp
).

Definition solve_entail_wit_6_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (r_pre <= INT_MAX)) (PreH10 : (l_pre <= INT_MAX)) (PreH11 : (p >= INT_MIN)) (PreH12 : (mid >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (bit_pre >= INT_MIN)) (PreH15 : (r_pre >= INT_MIN)) (PreH16 : (l_pre >= INT_MIN)) (PreH17 : (i < r_pre)) (PreH18 : (0 <= l_pre)) (PreH19 : (l_pre <= i)) (PreH20 : (i <= r_pre)) (PreH21 : (r_pre <= n_total)) (PreH22 : (n_total <= 300000)) (PreH23 : (l_pre <= mid)) (PreH24 : (mid <= p)) (PreH25 : (p <= r_pre)) (PreH26 : (mid = (l_pre + zeros ))) (PreH27 : (0 <= bit_pre)) (PreH28 : (bit_pre < 30)) (PreH29 : (0 <= capacity)) (PreH30 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (scratch_current)) = n_total)) (PreH33 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH34 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH35 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH36 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH37 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (p < r_pre)
.

Definition solve_entail_wit_7_1 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current_2)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.mixed_full tmp_p n_total (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)) )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre (i + 1 ) (p + 1 ) 1 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current_2)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  TT && emp 
|--
  “ (StablePartitionPrefix before (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)) l_pre r_pre bit_pre (i + 1 ) (p + 1 ) 1 ) ”
  &&  “ ((Zlength ((replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)))) = n_total) ”
  &&  emp
).

Definition solve_entail_wit_7_1_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current_2)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (StablePartitionPrefix before (replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)) l_pre r_pre bit_pre (i + 1 ) (p + 1 ) 1 )
.

Definition solve_entail_wit_7_1_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current_2)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  ((Zlength ((replace_Znth (p) ((Some ((Znth i before 0)))) (scratch_current_2)))) = n_total)
.

Definition solve_entail_wit_7_2 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current_2)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= p) ”
  &&  “ (p <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre (i + 1 ) p 1 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current_2)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  TT && emp 
|--
  “ (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre (i + 1 ) p 1 ) ”
  &&  emp
).

Definition solve_entail_wit_7_2_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current_2)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )) (PreH21 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)),
  (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre (i + 1 ) p 1 )
.

Definition solve_entail_wit_8 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) __default__App_option_Z __default__List_Z (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current_2)) = n_total)) (PreH17 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 before 0)) /\ ((Znth k_5 before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ ((l_pre < r_pre) -> ((((Znth l_pre scratch_current __default__App_option_Z) = (Some ((Znth (l_pre - l_pre ) partitioned 0)))) /\ (0 <= (Znth (l_pre - l_pre ) partitioned 0))) /\ ((Znth (l_pre - l_pre ) partitioned 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre l_pre ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (ones: Z) (scratch_current_2: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) __default__App_option_Z __default__List_Z (PreH1 : (i >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current_2)) = n_total)) (PreH17 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 before 0)) /\ ((Znth k_5 before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre i p 1 )),
  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ ((l_pre < r_pre) -> ((((Znth l_pre scratch_current __default__App_option_Z) = (Some ((Znth (l_pre - l_pre ) partitioned 0)))) /\ (0 <= (Znth (l_pre - l_pre ) partitioned 0))) /\ ((Znth (l_pre - l_pre ) partitioned 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre l_pre ) ”
  &&  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
).

Definition solve_entail_wit_9 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs_2: (@list (@list Z))) (p: Z) (zeros: Z) (mid: Z) (i: Z) (scratch_current_2: (@list (@option Z))) (current_2: (@list Z)) (partitioned_2: (@list Z)) __default__App_option_Z __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= r_pre)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (before)) = n_total)) (PreH18 : ((Zlength (current_2)) = n_total)) (PreH19 : ((Zlength (scratch_current_2)) = n_total)) (PreH20 : (mid <= (Zlength (current_2)))) (PreH21 : ((Zlength (scratch_current_2)) = (Zlength (current_2)))) (PreH22 : ((Zlength (partitioned_2)) = (r_pre - l_pre ))) (PreH23 : ((Zlength (counted_costs_2)) = 30)) (PreH24 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH25 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 current_2 0)) /\ ((Znth k_5 current_2 0) <= 1000000000)))) (PreH26 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (current_2)))) -> ((0 <= (Znth k_6 current_2 0)) /\ ((Znth k_6 current_2 0) <= 1000000000)))) (PreH27 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_7 partitioned_2 0)) /\ ((Znth k_7 partitioned_2 0) <= 1000000000)))) (PreH28 : forall (k_8: Z), (((l_pre <= k_8) /\ (k_8 < r_pre)) -> ((Znth k_8 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_8 - l_pre ) partitioned_2 0)))))) (PreH29 : ((i < r_pre) -> ((((Znth i scratch_current_2 __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned_2 0)))) /\ (0 <= (Znth (i - l_pre ) partitioned_2 0))) /\ ((Znth (i - l_pre ) partitioned_2 0) <= 1000000000)))) (PreH30 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH31 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH32 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre r_pre p 1 )) (PreH33 : (PartitionCopyBack before current_2 partitioned_2 l_pre r_pre i )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current_2)) current_2 )
  **  (IntArray.mixed_full tmp_p (Zlength (current_2)) scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i < r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ ((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) ”
  &&  “ (0 <= (Znth (i - l_pre ) partitioned 0)) ”
  &&  “ ((Znth (i - l_pre ) partitioned 0) <= 1000000000) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre i ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (((tmp_p + (i * sizeof(INT)))) # Int  |-> (Znth (i - l_pre ) partitioned 0))
  **  (IntArray.mixed_missing_i tmp_p i 0 (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs_2: (@list (@list Z))) (p: Z) (zeros: Z) (mid: Z) (i: Z) (scratch_current_2: (@list (@option Z))) (current_2: (@list Z)) (partitioned_2: (@list Z)) __default__App_option_Z __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= r_pre)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (before)) = n_total)) (PreH18 : ((Zlength (current_2)) = n_total)) (PreH19 : ((Zlength (scratch_current_2)) = n_total)) (PreH20 : (mid <= (Zlength (current_2)))) (PreH21 : ((Zlength (scratch_current_2)) = (Zlength (current_2)))) (PreH22 : ((Zlength (partitioned_2)) = (r_pre - l_pre ))) (PreH23 : ((Zlength (counted_costs_2)) = 30)) (PreH24 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH25 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 current_2 0)) /\ ((Znth k_5 current_2 0) <= 1000000000)))) (PreH26 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (current_2)))) -> ((0 <= (Znth k_6 current_2 0)) /\ ((Znth k_6 current_2 0) <= 1000000000)))) (PreH27 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_7 partitioned_2 0)) /\ ((Znth k_7 partitioned_2 0) <= 1000000000)))) (PreH28 : forall (k_8: Z), (((l_pre <= k_8) /\ (k_8 < r_pre)) -> ((Znth k_8 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_8 - l_pre ) partitioned_2 0)))))) (PreH29 : ((i < r_pre) -> ((((Znth i scratch_current_2 __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned_2 0)))) /\ (0 <= (Znth (i - l_pre ) partitioned_2 0))) /\ ((Znth (i - l_pre ) partitioned_2 0) <= 1000000000)))) (PreH30 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH31 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH32 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre r_pre p 1 )) (PreH33 : (PartitionCopyBack before current_2 partitioned_2 l_pre r_pre i )),
  TT && emp 
|--
  EX (partitioned: (@list Z)),
  “ ((Znth i scratch_current_2 __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ ((Znth i scratch_current_2 __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) ”
  &&  “ (0 <= (Znth (i - l_pre ) partitioned 0)) ”
  &&  “ ((Znth (i - l_pre ) partitioned 0) <= 1000000000) ”
  &&  “ (PartitionCopyBack before current_2 partitioned l_pre r_pre i ) ”
  &&  emp
).

Definition solve_entail_wit_10 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (scratch_current_2: (@list (@option Z))) (current_2: (@list Z)) (partitioned: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= i)) (PreH3 : (i < r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (l_pre <= mid)) (PreH7 : (mid <= r_pre)) (PreH8 : (mid = (l_pre + zeros ))) (PreH9 : (p = r_pre)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((-1) <= (bit_pre - 1 ))) (PreH15 : ((bit_pre - 1 ) < 30)) (PreH16 : ((Zlength (before)) = n_total)) (PreH17 : ((Zlength (current_2)) = n_total)) (PreH18 : ((Zlength (scratch_current_2)) = n_total)) (PreH19 : (mid <= (Zlength (current_2)))) (PreH20 : ((Zlength (scratch_current_2)) = (Zlength (current_2)))) (PreH21 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH22 : ((Zlength (counted_costs_2)) = 30)) (PreH23 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH24 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 current_2 0)) /\ ((Znth k_5 current_2 0) <= 1000000000)))) (PreH25 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (current_2)))) -> ((0 <= (Znth k_6 current_2 0)) /\ ((Znth k_6 current_2 0) <= 1000000000)))) (PreH26 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < (Zlength (partitioned)))) -> ((0 <= (Znth k_7 partitioned 0)) /\ ((Znth k_7 partitioned 0) <= 1000000000)))) (PreH27 : forall (k_8: Z), (((l_pre <= k_8) /\ (k_8 < r_pre)) -> ((Znth k_8 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_8 - l_pre ) partitioned 0)))))) (PreH28 : ((Znth i scratch_current_2 __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0))))) (PreH29 : (0 <= (Znth (i - l_pre ) partitioned 0))) (PreH30 : ((Znth (i - l_pre ) partitioned 0) <= 1000000000)) (PreH31 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre r_pre p 1 )) (PreH34 : (PartitionCopyBack before current_2 partitioned l_pre r_pre i )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current_2)) current_2 )
  **  (((tmp_p + (i * sizeof(INT)))) # Int  |-> (Znth (i - l_pre ) partitioned 0))
  **  (IntArray.mixed_missing_i tmp_p i 0 (Zlength (current_2)) scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned_2: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i < r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned_2)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_3 partitioned_2 0)) /\ ((Znth k_3 partitioned_2 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned_2 0))))) ”
  &&  “ ((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) ”
  &&  “ ((Znth (i - l_pre ) partitioned 0) = (Znth (i - l_pre ) partitioned_2 0)) ”
  &&  “ (0 <= (Znth (i - l_pre ) partitioned 0)) ”
  &&  “ ((Znth (i - l_pre ) partitioned 0) <= 1000000000) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned_2 l_pre r_pre i ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (scratch_current_2: (@list (@option Z))) (current_2: (@list Z)) (partitioned: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : ((Znth (i - l_pre ) partitioned 0) <= INT_MAX)) (PreH2 : ((Znth (i - l_pre ) partitioned 0) >= INT_MIN)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i < r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= mid)) (PreH9 : (mid <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (p = r_pre)) (PreH12 : (0 <= bit_pre)) (PreH13 : (bit_pre < 30)) (PreH14 : (0 <= capacity)) (PreH15 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH16 : ((-1) <= (bit_pre - 1 ))) (PreH17 : ((bit_pre - 1 ) < 30)) (PreH18 : ((Zlength (before)) = n_total)) (PreH19 : ((Zlength (current_2)) = n_total)) (PreH20 : ((Zlength (scratch_current_2)) = n_total)) (PreH21 : (mid <= (Zlength (current_2)))) (PreH22 : ((Zlength (scratch_current_2)) = (Zlength (current_2)))) (PreH23 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH24 : ((Zlength (counted_costs_2)) = 30)) (PreH25 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH26 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 current_2 0)) /\ ((Znth k_5 current_2 0) <= 1000000000)))) (PreH27 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (current_2)))) -> ((0 <= (Znth k_6 current_2 0)) /\ ((Znth k_6 current_2 0) <= 1000000000)))) (PreH28 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < (Zlength (partitioned)))) -> ((0 <= (Znth k_7 partitioned 0)) /\ ((Znth k_7 partitioned 0) <= 1000000000)))) (PreH29 : forall (k_8: Z), (((l_pre <= k_8) /\ (k_8 < r_pre)) -> ((Znth k_8 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_8 - l_pre ) partitioned 0)))))) (PreH30 : ((Znth i scratch_current_2 __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0))))) (PreH31 : (0 <= (Znth (i - l_pre ) partitioned 0))) (PreH32 : ((Znth (i - l_pre ) partitioned 0) <= 1000000000)) (PreH33 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH34 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH35 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre r_pre p 1 )) (PreH36 : (PartitionCopyBack before current_2 partitioned l_pre r_pre i )),
  (IntArray.full a_p (Zlength (current_2)) current_2 )
  **  (((tmp_p + (i * sizeof(INT)))) # Int  |-> (Znth (i - l_pre ) partitioned 0))
  **  (IntArray.mixed_missing_i tmp_p i 0 (Zlength (current_2)) scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned_2: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i < r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned_2)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_3 partitioned_2 0)) /\ ((Znth k_3 partitioned_2 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned_2 0))))) ”
  &&  “ ((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned 0)))) ”
  &&  “ ((Znth (i - l_pre ) partitioned 0) = (Znth (i - l_pre ) partitioned_2 0)) ”
  &&  “ (0 <= (Znth (i - l_pre ) partitioned 0)) ”
  &&  “ ((Znth (i - l_pre ) partitioned 0) <= 1000000000) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned_2 l_pre r_pre i ) ”
  &&  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
).

Definition solve_entail_wit_11 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (scratch_current_2: (@list (@option Z))) (current_2: (@list Z)) (partitioned_2: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (value: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= i)) (PreH3 : (i < r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (l_pre <= mid)) (PreH7 : (mid <= r_pre)) (PreH8 : (mid = (l_pre + zeros ))) (PreH9 : (p = r_pre)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((-1) <= (bit_pre - 1 ))) (PreH15 : ((bit_pre - 1 ) < 30)) (PreH16 : ((Zlength (before)) = n_total)) (PreH17 : ((Zlength (current_2)) = n_total)) (PreH18 : ((Zlength (scratch_current_2)) = n_total)) (PreH19 : (mid <= (Zlength (current_2)))) (PreH20 : ((Zlength (scratch_current_2)) = (Zlength (current_2)))) (PreH21 : ((Zlength (partitioned_2)) = (r_pre - l_pre ))) (PreH22 : ((Zlength (counted_costs_2)) = 30)) (PreH23 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH24 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 current_2 0)) /\ ((Znth k_5 current_2 0) <= 1000000000)))) (PreH25 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (current_2)))) -> ((0 <= (Znth k_6 current_2 0)) /\ ((Znth k_6 current_2 0) <= 1000000000)))) (PreH26 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_7 partitioned_2 0)) /\ ((Znth k_7 partitioned_2 0) <= 1000000000)))) (PreH27 : forall (k_8: Z), (((l_pre <= k_8) /\ (k_8 < r_pre)) -> ((Znth k_8 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_8 - l_pre ) partitioned_2 0)))))) (PreH28 : ((Znth i scratch_current_2 __default__App_option_Z) = (Some (value)))) (PreH29 : (value = (Znth (i - l_pre ) partitioned_2 0))) (PreH30 : (0 <= value)) (PreH31 : (value <= 1000000000)) (PreH32 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH33 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH34 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre r_pre p 1 )) (PreH35 : (PartitionCopyBack before current_2 partitioned_2 l_pre r_pre i )),
  (IntArray.full a_p (Zlength (current_2)) (replace_Znth (i) (value) (current_2)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p (Zlength (current_2)) scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ (((i + 1 ) < r_pre) -> ((((Znth (i + 1 ) scratch_current __default__App_option_Z) = (Some ((Znth ((i + 1 ) - l_pre ) partitioned 0)))) /\ (0 <= (Znth ((i + 1 ) - l_pre ) partitioned 0))) /\ ((Znth ((i + 1 ) - l_pre ) partitioned 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre (i + 1 ) ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs_2: (@list (@list Z))) (scratch_current_2: (@list (@option Z))) (current_2: (@list Z)) (partitioned_2: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (value: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= i)) (PreH3 : (i < r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (l_pre <= mid)) (PreH7 : (mid <= r_pre)) (PreH8 : (mid = (l_pre + zeros ))) (PreH9 : (p = r_pre)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((-1) <= (bit_pre - 1 ))) (PreH15 : ((bit_pre - 1 ) < 30)) (PreH16 : ((Zlength (before)) = n_total)) (PreH17 : ((Zlength (current_2)) = n_total)) (PreH18 : ((Zlength (scratch_current_2)) = n_total)) (PreH19 : (mid <= (Zlength (current_2)))) (PreH20 : ((Zlength (scratch_current_2)) = (Zlength (current_2)))) (PreH21 : ((Zlength (partitioned_2)) = (r_pre - l_pre ))) (PreH22 : ((Zlength (counted_costs_2)) = 30)) (PreH23 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH24 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_total)) -> ((0 <= (Znth k_5 current_2 0)) /\ ((Znth k_5 current_2 0) <= 1000000000)))) (PreH25 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (current_2)))) -> ((0 <= (Znth k_6 current_2 0)) /\ ((Znth k_6 current_2 0) <= 1000000000)))) (PreH26 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_7 partitioned_2 0)) /\ ((Znth k_7 partitioned_2 0) <= 1000000000)))) (PreH27 : forall (k_8: Z), (((l_pre <= k_8) /\ (k_8 < r_pre)) -> ((Znth k_8 scratch_current_2 __default__App_option_Z) = (Some ((Znth (k_8 - l_pre ) partitioned_2 0)))))) (PreH28 : ((Znth i scratch_current_2 __default__App_option_Z) = (Some (value)))) (PreH29 : (value = (Znth (i - l_pre ) partitioned_2 0))) (PreH30 : (0 <= value)) (PreH31 : (value <= 1000000000)) (PreH32 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH33 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH34 : (StablePartitionPrefix before scratch_current_2 l_pre r_pre bit_pre r_pre p 1 )) (PreH35 : (PartitionCopyBack before current_2 partitioned_2 l_pre r_pre i )),
  (IntArray.full a_p (Zlength (current_2)) (replace_Znth (i) (value) (current_2)) )
  **  (IntArray.mixed_full tmp_p (Zlength (current_2)) scratch_current_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs_2 )
|--
  EX (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ (((i + 1 ) < r_pre) -> ((((Znth (i + 1 ) scratch_current __default__App_option_Z) = (Some ((Znth ((i + 1 ) - l_pre ) partitioned 0)))) /\ (0 <= (Znth ((i + 1 ) - l_pre ) partitioned 0))) /\ ((Znth ((i + 1 ) - l_pre ) partitioned 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre (i + 1 ) ) ”
  &&  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
).

Definition solve_entail_wit_12 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs_2: (@list (@list Z))) (partitioned_2: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i: Z) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__App_option_Z __default__List_Z (PreH1 : (SolveEffect current after counted_costs_2 cost_after l_pre mid (bit_pre - 1 ) )) (PreH2 : (CostBound cost_after ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (mid - l_pre ) ) * (mid - l_pre ) ) ) )) (PreH3 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (current)))) -> ((0 <= (Znth i_2 after 0)) /\ ((Znth i_2 after 0) <= 1000000000)))) (PreH4 : (i >= r_pre)) (PreH5 : (0 <= l_pre)) (PreH6 : (l_pre <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (r_pre <= n_total)) (PreH9 : (n_total <= 300000)) (PreH10 : (l_pre <= mid)) (PreH11 : (mid <= r_pre)) (PreH12 : (mid = (l_pre + zeros ))) (PreH13 : (p = r_pre)) (PreH14 : (0 <= bit_pre)) (PreH15 : (bit_pre < 30)) (PreH16 : (0 <= capacity)) (PreH17 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH18 : ((-1) <= (bit_pre - 1 ))) (PreH19 : ((bit_pre - 1 ) < 30)) (PreH20 : ((Zlength (before)) = n_total)) (PreH21 : ((Zlength (current)) = n_total)) (PreH22 : ((Zlength (scratch_current)) = n_total)) (PreH23 : (mid <= (Zlength (current)))) (PreH24 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH25 : ((Zlength (partitioned_2)) = (r_pre - l_pre ))) (PreH26 : ((Zlength (counted_costs_2)) = 30)) (PreH27 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH28 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_total)) -> ((0 <= (Znth k_3 current 0)) /\ ((Znth k_3 current 0) <= 1000000000)))) (PreH29 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (current)))) -> ((0 <= (Znth k_4 current 0)) /\ ((Znth k_4 current 0) <= 1000000000)))) (PreH30 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_5 partitioned_2 0)) /\ ((Znth k_5 partitioned_2 0) <= 1000000000)))) (PreH31 : forall (k_6: Z), (((l_pre <= k_6) /\ (k_6 < r_pre)) -> ((Znth k_6 scratch_current __default__App_option_Z) = (Some ((Znth (k_6 - l_pre ) partitioned_2 0)))))) (PreH32 : ((i < r_pre) -> ((((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned_2 0)))) /\ (0 <= (Znth (i - l_pre ) partitioned_2 0))) /\ ((Znth (i - l_pre ) partitioned_2 0) <= 1000000000)))) (PreH33 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH34 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH35 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH36 : (PartitionCopyBack before current partitioned_2 l_pre r_pre i )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) after )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
|--
  EX (counted_costs: (@list (@list Z))) (first_cost: (@list (@list Z))) (first_scratch: (@list (@option Z))) (first_after: (@list Z)) (partition_scratch: (@list (@option Z))) (partitioned: (@list Z)) (partition_before: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (partition_before)) = n_total) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (partition_scratch)) = n_total) ”
  &&  “ ((Zlength (first_after)) = n_total) ”
  &&  “ ((Zlength (first_scratch)) = n_total) ”
  &&  “ ((Zlength (first_cost)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0))))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre ) ”
  &&  “ (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) ) ”
  &&  “ (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs_2: (@list (@list Z))) (partitioned_2: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i: Z) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__App_option_Z __default__List_Z (PreH1 : (SolveEffect current after counted_costs_2 cost_after l_pre mid (bit_pre - 1 ) )) (PreH2 : (CostBound cost_after ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (mid - l_pre ) ) * (mid - l_pre ) ) ) )) (PreH3 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (current)))) -> ((0 <= (Znth i_2 after 0)) /\ ((Znth i_2 after 0) <= 1000000000)))) (PreH4 : (i >= r_pre)) (PreH5 : (0 <= l_pre)) (PreH6 : (l_pre <= i)) (PreH7 : (i <= r_pre)) (PreH8 : (r_pre <= n_total)) (PreH9 : (n_total <= 300000)) (PreH10 : (l_pre <= mid)) (PreH11 : (mid <= r_pre)) (PreH12 : (mid = (l_pre + zeros ))) (PreH13 : (p = r_pre)) (PreH14 : (0 <= bit_pre)) (PreH15 : (bit_pre < 30)) (PreH16 : (0 <= capacity)) (PreH17 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH18 : ((-1) <= (bit_pre - 1 ))) (PreH19 : ((bit_pre - 1 ) < 30)) (PreH20 : ((Zlength (before)) = n_total)) (PreH21 : ((Zlength (current)) = n_total)) (PreH22 : ((Zlength (scratch_current)) = n_total)) (PreH23 : (mid <= (Zlength (current)))) (PreH24 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH25 : ((Zlength (partitioned_2)) = (r_pre - l_pre ))) (PreH26 : ((Zlength (counted_costs_2)) = 30)) (PreH27 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs_2 __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs_2 __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs_2 __default__List_Z) 0))))) (PreH28 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_total)) -> ((0 <= (Znth k_3 current 0)) /\ ((Znth k_3 current 0) <= 1000000000)))) (PreH29 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (current)))) -> ((0 <= (Znth k_4 current 0)) /\ ((Znth k_4 current 0) <= 1000000000)))) (PreH30 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (partitioned_2)))) -> ((0 <= (Znth k_5 partitioned_2 0)) /\ ((Znth k_5 partitioned_2 0) <= 1000000000)))) (PreH31 : forall (k_6: Z), (((l_pre <= k_6) /\ (k_6 < r_pre)) -> ((Znth k_6 scratch_current __default__App_option_Z) = (Some ((Znth (k_6 - l_pre ) partitioned_2 0)))))) (PreH32 : ((i < r_pre) -> ((((Znth i scratch_current __default__App_option_Z) = (Some ((Znth (i - l_pre ) partitioned_2 0)))) /\ (0 <= (Znth (i - l_pre ) partitioned_2 0))) /\ ((Znth (i - l_pre ) partitioned_2 0) <= 1000000000)))) (PreH33 : (SolveCountPrefix before cost_before counted_costs_2 l_pre r_pre bit_pre zeros ones )) (PreH34 : (CostBound counted_costs_2 (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH35 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH36 : (PartitionCopyBack before current partitioned_2 l_pre r_pre i )),
  (IntArray.full a_p (Zlength (current)) after )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
|--
  EX (counted_costs: (@list (@list Z))) (first_cost: (@list (@list Z))) (first_scratch: (@list (@option Z))) (first_after: (@list Z)) (partition_scratch: (@list (@option Z))) (partitioned: (@list Z)) (partition_before: (@list Z)),
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (partition_before)) = n_total) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (partition_scratch)) = n_total) ”
  &&  “ ((Zlength (first_after)) = n_total) ”
  &&  “ ((Zlength (first_scratch)) = n_total) ”
  &&  “ ((Zlength (first_cost)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0))))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre ) ”
  &&  “ (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) ) ”
  &&  “ (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) ) ”
  &&  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
).

Definition solve_return_wit_1 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (bit_pre < 0)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : ((-1) <= bit_pre)) (PreH7 : (bit_pre < 30)) (PreH8 : ((Zlength (before)) = n_total)) (PreH9 : ((Zlength (scratch)) = n_total)) (PreH10 : ((Zlength (cost_before)) = 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : (CostBound cost_before capacity )) (PreH14 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH15 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  EX (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))),
  “ (SolveEffect before after cost_before cost_after l_pre r_pre bit_pre ) ”
  &&  “ (CostBound cost_after (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total after )
  **  (IntArray.mixed_full tmp_p n_total scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (bit_pre < 0)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : ((-1) <= bit_pre)) (PreH7 : (bit_pre < 30)) (PreH8 : ((Zlength (before)) = n_total)) (PreH9 : ((Zlength (scratch)) = n_total)) (PreH10 : ((Zlength (cost_before)) = 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : (CostBound cost_before capacity )) (PreH14 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH15 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  TT && emp 
|--
  “ (CostBound cost_before (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (SolveEffect before before cost_before cost_before l_pre r_pre bit_pre ) ”
  &&  emp
).

Definition solve_return_wit_1_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (bit_pre < 0)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : ((-1) <= bit_pre)) (PreH7 : (bit_pre < 30)) (PreH8 : ((Zlength (before)) = n_total)) (PreH9 : ((Zlength (scratch)) = n_total)) (PreH10 : ((Zlength (cost_before)) = 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : (CostBound cost_before capacity )) (PreH14 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH15 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  (CostBound cost_before (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) )
.

Definition solve_return_wit_1_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : (bit_pre < 0)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : ((-1) <= bit_pre)) (PreH7 : (bit_pre < 30)) (PreH8 : ((Zlength (before)) = n_total)) (PreH9 : ((Zlength (scratch)) = n_total)) (PreH10 : ((Zlength (cost_before)) = 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : (CostBound cost_before capacity )) (PreH14 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH15 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  (SolveEffect before before cost_before cost_before l_pre r_pre bit_pre )
.

Definition solve_return_wit_2 :=
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) <= 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_before )
|--
  EX (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))),
  “ (SolveEffect before after cost_before cost_after l_pre r_pre bit_pre ) ”
  &&  “ (CostBound cost_after (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total after )
  **  (IntArray.mixed_full tmp_p n_total scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
) \/
(
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) <= 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  TT && emp 
|--
  “ (CostBound cost_before (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (SolveEffect before before cost_before cost_before l_pre r_pre bit_pre ) ”
  &&  emp
).

Definition solve_return_wit_2_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) <= 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  (CostBound cost_before (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) )
.

Definition solve_return_wit_2_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) __default__List_Z (PreH1 : ((r_pre - l_pre ) <= 1)) (PreH2 : (bit_pre >= 0)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : ((-1) <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : ((Zlength (before)) = n_total)) (PreH10 : ((Zlength (scratch)) = n_total)) (PreH11 : ((Zlength (cost_before)) = 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : (CostBound cost_before capacity )) (PreH15 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b cost_before __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b cost_before __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b cost_before __default__List_Z) 0))))) (PreH16 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_total)) -> ((0 <= (Znth i_2 before 0)) /\ ((Znth i_2 before 0) <= 1000000000)))),
  (SolveEffect before before cost_before cost_before l_pre r_pre bit_pre )
.

Definition solve_return_wit_3 :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) (scratch_after_2: (@list (@option Z))) (after_2: (@list Z)) (cost_after_2: (@list (@list Z))) __default__App_option_Z __default__List_Z (PreH1 : (SolveEffect first_after after_2 first_cost cost_after_2 mid r_pre (bit_pre - 1 ) )) (PreH2 : (CostBound cost_after_2 (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - mid ) ) * (r_pre - mid ) ) ) )) (PreH3 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (first_after)))) -> ((0 <= (Znth i_2 after_2 0)) /\ ((Znth i_2 after_2 0) <= 1000000000)))) (PreH4 : (0 <= l_pre)) (PreH5 : (l_pre <= mid)) (PreH6 : (mid <= r_pre)) (PreH7 : (r_pre <= n_total)) (PreH8 : (n_total <= 300000)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (partition_before)) = n_total)) (PreH18 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH19 : ((Zlength (partition_scratch)) = n_total)) (PreH20 : ((Zlength (first_after)) = n_total)) (PreH21 : ((Zlength (first_scratch)) = n_total)) (PreH22 : ((Zlength (first_cost)) = 30)) (PreH23 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0))))) (PreH24 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH25 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH26 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH27 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH28 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH29 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH30 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) after_2 )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) scratch_after_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after_2 )
|--
  EX (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))),
  “ (SolveEffect before after cost_before cost_after l_pre r_pre bit_pre ) ”
  &&  “ (CostBound cost_after (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total after )
  **  (IntArray.mixed_full tmp_p n_total scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) (scratch_after_2: (@list (@option Z))) (after_2: (@list Z)) (cost_after_2: (@list (@list Z))) __default__App_option_Z __default__List_Z (PreH1 : (SolveEffect first_after after_2 first_cost cost_after_2 mid r_pre (bit_pre - 1 ) )) (PreH2 : (CostBound cost_after_2 (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - mid ) ) * (r_pre - mid ) ) ) )) (PreH3 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (first_after)))) -> ((0 <= (Znth i_2 after_2 0)) /\ ((Znth i_2 after_2 0) <= 1000000000)))) (PreH4 : (0 <= l_pre)) (PreH5 : (l_pre <= mid)) (PreH6 : (mid <= r_pre)) (PreH7 : (r_pre <= n_total)) (PreH8 : (n_total <= 300000)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (partition_before)) = n_total)) (PreH18 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH19 : ((Zlength (partition_scratch)) = n_total)) (PreH20 : ((Zlength (first_after)) = n_total)) (PreH21 : ((Zlength (first_scratch)) = n_total)) (PreH22 : ((Zlength (first_cost)) = 30)) (PreH23 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0))))) (PreH24 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH25 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH26 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH27 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH28 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH29 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH30 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  (IntArray.full a_p (Zlength (first_after)) after_2 )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) scratch_after_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after_2 )
|--
  EX (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))),
  “ (SolveEffect before after cost_before cost_after l_pre r_pre bit_pre ) ”
  &&  “ (CostBound cost_after (capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_total)) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000))) ”
  &&  (IntArray.full a_p n_total after )
  **  (IntArray.mixed_full tmp_p n_total scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
).

Definition solve_partial_solve_wit_1 :=
forall (cost_before: (@list (@list Z))) (scratch: (@list (@option Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (current_costs: (@list (@list Z))) (ones: Z) (zeros: Z) (i: Z) __default__List_Z (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (0 <= bit_pre)) (PreH8 : (bit_pre < 30)) (PreH9 : (0 <= capacity)) (PreH10 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH11 : ((Zlength (before)) = n_total)) (PreH12 : ((Zlength (scratch)) = n_total)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH14 : (0 <= zeros)) (PreH15 : (0 <= ones)) (PreH16 : ((zeros + ones ) = (i - l_pre ))) (PreH17 : (zeros <= n_total)) (PreH18 : (ones <= n_total)) (PreH19 : (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones )) (PreH20 : (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
|--
  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (0 <= zeros) ”
  &&  “ (0 <= ones) ”
  &&  “ ((zeros + ones ) = (i - l_pre )) ”
  &&  “ (zeros <= n_total) ”
  &&  “ (ones <= n_total) ”
  &&  “ (SolveCountPrefix before cost_before current_costs l_pre i bit_pre zeros ones ) ”
  &&  “ (CostBound current_costs (capacity + ((i - l_pre ) * (i - l_pre ) ) ) ) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |-> (Znth i before 0))
  **  (IntArray.missing_i a_p i 0 n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch )
  **  (Int64Array2.full ( &( "cost" ) ) bit_pre 2 (sublist (0) (bit_pre) (current_costs)) )
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth bit_pre current_costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (bit_pre * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth bit_pre current_costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((bit_pre + 1 ) * (2 * sizeof(INT64)))) ((30 - bit_pre ) - 1 ) 2 (sublist ((bit_pre + 1 )) (30) (current_costs)) )
.

Definition solve_partial_solve_wit_2 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= p)) (PreH8 : (p <= i)) (PreH9 : (0 <= bit_pre)) (PreH10 : (bit_pre < 30)) (PreH11 : (0 <= capacity)) (PreH12 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH13 : ((Zlength (before)) = n_total)) (PreH14 : ((Zlength (scratch_current)) = n_total)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH16 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH17 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH18 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= p) ”
  &&  “ (p <= i) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 ) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |-> (Znth i before 0))
  **  (IntArray.missing_i a_p i 0 n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_3 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0) ”
  &&  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= p) ”
  &&  “ (p <= i) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 ) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |-> (Znth i before 0))
  **  (IntArray.missing_i a_p i 0 n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_4 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (zeros: Z) (ones: Z) (scratch_current: (@list (@option Z))) (p: Z) (i: Z) (PreH1 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= i)) (PreH5 : (i <= r_pre)) (PreH6 : (r_pre <= n_total)) (PreH7 : (n_total <= 300000)) (PreH8 : (l_pre <= p)) (PreH9 : (p <= i)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((Zlength (before)) = n_total)) (PreH15 : ((Zlength (scratch_current)) = n_total)) (PreH16 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH17 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH18 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH19 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 )),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) = 0) ”
  &&  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= p) ”
  &&  “ (p <= i) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 0 ) ”
  &&  (((tmp_p + (p * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i tmp_p p 0 n_total scratch_current )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_5 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i)) (PreH4 : (i <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= p)) (PreH9 : (p <= r_pre)) (PreH10 : (mid = (l_pre + zeros ))) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((Zlength (before)) = n_total)) (PreH16 : ((Zlength (scratch_current)) = n_total)) (PreH17 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH18 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH19 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH20 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p n_total before )
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= p) ”
  &&  “ (p <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 ) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |-> (Znth i before 0))
  **  (IntArray.missing_i a_p i 0 n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_6 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (p < r_pre) ”
  &&  “ (ones <= INT64_MAX) ”
  &&  “ (zeros <= INT64_MAX) ”
  &&  “ (ones >= INT64_MIN) ”
  &&  “ (zeros >= INT64_MIN) ”
  &&  “ (mid <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (bit_pre <= INT_MAX) ”
  &&  “ (l_pre <= INT_MAX) ”
  &&  “ (mid >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (bit_pre >= INT_MIN) ”
  &&  “ (l_pre >= INT_MIN) ”
  &&  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= p) ”
  &&  “ (p <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 ) ”
  &&  “ ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |-> (Znth i before 0))
  **  (IntArray.missing_i a_p i 0 n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_7 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (ones: Z) (scratch_current: (@list (@option Z))) (zeros: Z) (p: Z) (mid: Z) (i: Z) (PreH1 : (p < r_pre)) (PreH2 : (ones <= INT64_MAX)) (PreH3 : (zeros <= INT64_MAX)) (PreH4 : (ones >= INT64_MIN)) (PreH5 : (zeros >= INT64_MIN)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (bit_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (mid >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (l_pre >= INT_MIN)) (PreH14 : (i < r_pre)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= i)) (PreH17 : (i <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (l_pre <= mid)) (PreH21 : (mid <= p)) (PreH22 : (p <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (0 <= bit_pre)) (PreH25 : (bit_pre < 30)) (PreH26 : (0 <= capacity)) (PreH27 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH28 : ((Zlength (before)) = n_total)) (PreH29 : ((Zlength (scratch_current)) = n_total)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000)))) (PreH31 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH32 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH33 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 )) (PreH34 : ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0)),
  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p n_total scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (p < r_pre) ”
  &&  “ (ones <= INT64_MAX) ”
  &&  “ (zeros <= INT64_MAX) ”
  &&  “ (ones >= INT64_MIN) ”
  &&  “ (zeros >= INT64_MIN) ”
  &&  “ (mid <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (bit_pre <= INT_MAX) ”
  &&  “ (l_pre <= INT_MAX) ”
  &&  “ (mid >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (bit_pre >= INT_MIN) ”
  &&  “ (l_pre >= INT_MIN) ”
  &&  “ (i < r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= p) ”
  &&  “ (p <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k before 0)) /\ ((Znth k before 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre i p 1 ) ”
  &&  “ ((Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) <> 0) ”
  &&  (((tmp_p + (p * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i tmp_p p 0 n_total scratch_current )
  **  (IntArray.full a_p n_total before )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_8 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (counted_costs: (@list (@list Z))) (scratch_current: (@list (@option Z))) (current: (@list Z)) (partitioned: (@list Z)) (i: Z) (mid: Z) (zeros: Z) (p: Z) (value: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= i)) (PreH3 : (i < r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (l_pre <= mid)) (PreH7 : (mid <= r_pre)) (PreH8 : (mid = (l_pre + zeros ))) (PreH9 : (p = r_pre)) (PreH10 : (0 <= bit_pre)) (PreH11 : (bit_pre < 30)) (PreH12 : (0 <= capacity)) (PreH13 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH14 : ((-1) <= (bit_pre - 1 ))) (PreH15 : ((bit_pre - 1 ) < 30)) (PreH16 : ((Zlength (before)) = n_total)) (PreH17 : ((Zlength (current)) = n_total)) (PreH18 : ((Zlength (scratch_current)) = n_total)) (PreH19 : (mid <= (Zlength (current)))) (PreH20 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH21 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH22 : ((Zlength (counted_costs)) = 30)) (PreH23 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0))))) (PreH24 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH26 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH27 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH28 : ((Znth i scratch_current __default__App_option_Z) = (Some (value)))) (PreH29 : (value = (Znth (i - l_pre ) partitioned 0))) (PreH30 : (0 <= value)) (PreH31 : (value <= 1000000000)) (PreH32 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH33 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH34 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH35 : (PartitionCopyBack before current partitioned l_pre r_pre i )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i) ”
  &&  “ (i < r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ ((Znth i scratch_current __default__App_option_Z) = (Some (value))) ”
  &&  “ (value = (Znth (i - l_pre ) partitioned 0)) ”
  &&  “ (0 <= value) ”
  &&  “ (value <= 1000000000) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre i ) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_p i 0 (Zlength (current)) current )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_9_pure :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (i_2 >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i_2)) (PreH4 : (i_2 <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= r_pre)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (before)) = n_total)) (PreH18 : ((Zlength (current)) = n_total)) (PreH19 : ((Zlength (scratch_current)) = n_total)) (PreH20 : (mid <= (Zlength (current)))) (PreH21 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH22 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH23 : ((Zlength (counted_costs)) = 30)) (PreH24 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH25 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH27 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH28 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH29 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH30 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH31 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH32 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH33 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (current)) <= 300000) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (current)) = (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (mid - l_pre ) ) * (mid - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (current)))) -> ((0 <= (Znth i current 0)) /\ ((Znth i current 0) <= 1000000000))) ”
  &&  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ (0 <= (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) )) ”
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (i_2 >= r_pre)) (PreH16 : (0 <= l_pre)) (PreH17 : (l_pre <= i_2)) (PreH18 : (i_2 <= r_pre)) (PreH19 : (r_pre <= n_total)) (PreH20 : (n_total <= 300000)) (PreH21 : (l_pre <= mid)) (PreH22 : (mid <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (p = r_pre)) (PreH25 : (0 <= bit_pre)) (PreH26 : (bit_pre < 30)) (PreH27 : (0 <= capacity)) (PreH28 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH29 : ((-1) <= (bit_pre - 1 ))) (PreH30 : ((bit_pre - 1 ) < 30)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (current)) = n_total)) (PreH33 : ((Zlength (scratch_current)) = n_total)) (PreH34 : (mid <= (Zlength (current)))) (PreH35 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH36 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH37 : ((Zlength (counted_costs)) = 30)) (PreH38 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH40 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH41 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH42 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH43 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH44 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH45 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH46 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH47 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) )) ”
  &&  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (current)))) -> ((0 <= (Znth i current 0)) /\ ((Znth i current 0) <= 1000000000))) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) <= INT64_MAX) ”
).

Definition solve_partial_solve_wit_9_pure_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (i_2 >= r_pre)) (PreH16 : (0 <= l_pre)) (PreH17 : (l_pre <= i_2)) (PreH18 : (i_2 <= r_pre)) (PreH19 : (r_pre <= n_total)) (PreH20 : (n_total <= 300000)) (PreH21 : (l_pre <= mid)) (PreH22 : (mid <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (p = r_pre)) (PreH25 : (0 <= bit_pre)) (PreH26 : (bit_pre < 30)) (PreH27 : (0 <= capacity)) (PreH28 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH29 : ((-1) <= (bit_pre - 1 ))) (PreH30 : ((bit_pre - 1 ) < 30)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (current)) = n_total)) (PreH33 : ((Zlength (scratch_current)) = n_total)) (PreH34 : (mid <= (Zlength (current)))) (PreH35 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH36 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH37 : ((Zlength (counted_costs)) = 30)) (PreH38 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH40 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH41 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH42 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH43 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH44 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH45 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH46 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH47 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) )) ”
.

Definition solve_partial_solve_wit_9_pure_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (i_2 >= r_pre)) (PreH16 : (0 <= l_pre)) (PreH17 : (l_pre <= i_2)) (PreH18 : (i_2 <= r_pre)) (PreH19 : (r_pre <= n_total)) (PreH20 : (n_total <= 300000)) (PreH21 : (l_pre <= mid)) (PreH22 : (mid <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (p = r_pre)) (PreH25 : (0 <= bit_pre)) (PreH26 : (bit_pre < 30)) (PreH27 : (0 <= capacity)) (PreH28 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH29 : ((-1) <= (bit_pre - 1 ))) (PreH30 : ((bit_pre - 1 ) < 30)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (current)) = n_total)) (PreH33 : ((Zlength (scratch_current)) = n_total)) (PreH34 : (mid <= (Zlength (current)))) (PreH35 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH36 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH37 : ((Zlength (counted_costs)) = 30)) (PreH38 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH40 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH41 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH42 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH43 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH44 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH45 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH46 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH47 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) <= INT64_MAX) ”
.

Definition solve_partial_solve_wit_9_pure_split_goal_3 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (i_2 >= r_pre)) (PreH16 : (0 <= l_pre)) (PreH17 : (l_pre <= i_2)) (PreH18 : (i_2 <= r_pre)) (PreH19 : (r_pre <= n_total)) (PreH20 : (n_total <= 300000)) (PreH21 : (l_pre <= mid)) (PreH22 : (mid <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (p = r_pre)) (PreH25 : (0 <= bit_pre)) (PreH26 : (bit_pre < 30)) (PreH27 : (0 <= capacity)) (PreH28 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH29 : ((-1) <= (bit_pre - 1 ))) (PreH30 : ((bit_pre - 1 ) < 30)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (current)) = n_total)) (PreH33 : ((Zlength (scratch_current)) = n_total)) (PreH34 : (mid <= (Zlength (current)))) (PreH35 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH36 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH37 : ((Zlength (counted_costs)) = 30)) (PreH38 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH40 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH41 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH42 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH43 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH44 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH45 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH46 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH47 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (current)))) -> ((0 <= (Znth i current 0)) /\ ((Znth i current 0) <= 1000000000))) ”
.

Definition solve_partial_solve_wit_9_pure_split_goal_4 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (i_2 >= r_pre)) (PreH16 : (0 <= l_pre)) (PreH17 : (l_pre <= i_2)) (PreH18 : (i_2 <= r_pre)) (PreH19 : (r_pre <= n_total)) (PreH20 : (n_total <= 300000)) (PreH21 : (l_pre <= mid)) (PreH22 : (mid <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (p = r_pre)) (PreH25 : (0 <= bit_pre)) (PreH26 : (bit_pre < 30)) (PreH27 : (0 <= capacity)) (PreH28 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH29 : ((-1) <= (bit_pre - 1 ))) (PreH30 : ((bit_pre - 1 ) < 30)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (current)) = n_total)) (PreH33 : ((Zlength (scratch_current)) = n_total)) (PreH34 : (mid <= (Zlength (current)))) (PreH35 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH36 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH37 : ((Zlength (counted_costs)) = 30)) (PreH38 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH40 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH41 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH42 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH43 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH44 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH45 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH46 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH47 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
.

Definition solve_partial_solve_wit_9_pure_split_goal_5 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (i_2 >= r_pre)) (PreH16 : (0 <= l_pre)) (PreH17 : (l_pre <= i_2)) (PreH18 : (i_2 <= r_pre)) (PreH19 : (r_pre <= n_total)) (PreH20 : (n_total <= 300000)) (PreH21 : (l_pre <= mid)) (PreH22 : (mid <= r_pre)) (PreH23 : (mid = (l_pre + zeros ))) (PreH24 : (p = r_pre)) (PreH25 : (0 <= bit_pre)) (PreH26 : (bit_pre < 30)) (PreH27 : (0 <= capacity)) (PreH28 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH29 : ((-1) <= (bit_pre - 1 ))) (PreH30 : ((bit_pre - 1 ) < 30)) (PreH31 : ((Zlength (before)) = n_total)) (PreH32 : ((Zlength (current)) = n_total)) (PreH33 : ((Zlength (scratch_current)) = n_total)) (PreH34 : (mid <= (Zlength (current)))) (PreH35 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH36 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH37 : ((Zlength (counted_costs)) = 30)) (PreH38 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH40 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH41 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH42 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH43 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH44 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH45 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH46 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH47 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) <= INT64_MAX) ”
.

Definition solve_partial_solve_wit_9_aux :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (ones: Z) (counted_costs: (@list (@list Z))) (partitioned: (@list Z)) (scratch_current: (@list (@option Z))) (current: (@list Z)) (p: Z) (zeros: Z) (mid: Z) (i_2: Z) __default__App_option_Z __default__List_Z (PreH1 : (i_2 >= r_pre)) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= i_2)) (PreH4 : (i_2 <= r_pre)) (PreH5 : (r_pre <= n_total)) (PreH6 : (n_total <= 300000)) (PreH7 : (l_pre <= mid)) (PreH8 : (mid <= r_pre)) (PreH9 : (mid = (l_pre + zeros ))) (PreH10 : (p = r_pre)) (PreH11 : (0 <= bit_pre)) (PreH12 : (bit_pre < 30)) (PreH13 : (0 <= capacity)) (PreH14 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH15 : ((-1) <= (bit_pre - 1 ))) (PreH16 : ((bit_pre - 1 ) < 30)) (PreH17 : ((Zlength (before)) = n_total)) (PreH18 : ((Zlength (current)) = n_total)) (PreH19 : ((Zlength (scratch_current)) = n_total)) (PreH20 : (mid <= (Zlength (current)))) (PreH21 : ((Zlength (scratch_current)) = (Zlength (current)))) (PreH22 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH23 : ((Zlength (counted_costs)) = 30)) (PreH24 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0))))) (PreH25 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000)))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH27 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000)))) (PreH28 : forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0)))))) (PreH29 : ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000)))) (PreH30 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH31 : (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) )) (PreH32 : (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 )) (PreH33 : (PartitionCopyBack before current partitioned l_pre r_pre i_2 )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
|--
  “ (0 <= l_pre) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (current)) <= 300000) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (current)) = (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (mid - l_pre ) ) * (mid - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (current)))) -> ((0 <= (Znth i current 0)) /\ ((Znth i current 0) <= 1000000000))) ”
  &&  “ (((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ (0 <= (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) )) ”
  &&  “ (i_2 >= r_pre) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= i_2) ”
  &&  “ (i_2 <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (before)) = n_total) ”
  &&  “ ((Zlength (current)) = n_total) ”
  &&  “ ((Zlength (scratch_current)) = n_total) ”
  &&  “ (mid <= (Zlength (current))) ”
  &&  “ ((Zlength (scratch_current)) = (Zlength (current))) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (counted_costs)) = 30) ”
  &&  “ forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 counted_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 counted_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 counted_costs __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k current 0)) /\ ((Znth k current 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (current)))) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (partitioned)))) -> ((0 <= (Znth k_3 partitioned 0)) /\ ((Znth k_3 partitioned 0) <= 1000000000))) ”
  &&  “ forall (k_4: Z), (((l_pre <= k_4) /\ (k_4 < r_pre)) -> ((Znth k_4 scratch_current __default__App_option_Z) = (Some ((Znth (k_4 - l_pre ) partitioned 0))))) ”
  &&  “ ((i_2 < r_pre) -> ((((Znth i_2 scratch_current __default__App_option_Z) = (Some ((Znth (i_2 - l_pre ) partitioned 0)))) /\ (0 <= (Znth (i_2 - l_pre ) partitioned 0))) /\ ((Znth (i_2 - l_pre ) partitioned 0) <= 1000000000))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (CostBound counted_costs (capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) ) ”
  &&  “ (StablePartitionPrefix before scratch_current l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before current partitioned l_pre r_pre i_2 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (current)) current )
  **  (IntArray.mixed_full tmp_p (Zlength (current)) scratch_current )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 counted_costs )
.

Definition solve_partial_solve_wit_9 := solve_partial_solve_wit_9_pure -> solve_partial_solve_wit_9_aux.

Definition solve_partial_solve_wit_10_pure :=
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= mid)) (PreH3 : (mid <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (mid = (l_pre + zeros ))) (PreH7 : (p = r_pre)) (PreH8 : (0 <= bit_pre)) (PreH9 : (bit_pre < 30)) (PreH10 : (0 <= capacity)) (PreH11 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH12 : ((-1) <= (bit_pre - 1 ))) (PreH13 : ((bit_pre - 1 ) < 30)) (PreH14 : ((Zlength (partition_before)) = n_total)) (PreH15 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH16 : ((Zlength (partition_scratch)) = n_total)) (PreH17 : ((Zlength (first_after)) = n_total)) (PreH18 : ((Zlength (first_scratch)) = n_total)) (PreH19 : ((Zlength (first_cost)) = 30)) (PreH20 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH22 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH23 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH24 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH25 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH26 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH27 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ (0 <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (r_pre <= (Zlength (first_after))) ”
  &&  “ ((Zlength (first_after)) <= 300000) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (first_after)) = (Zlength (first_after))) ”
  &&  “ ((Zlength (first_scratch)) = (Zlength (first_after))) ”
  &&  “ ((Zlength (first_cost)) = 30) ”
  &&  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) )) ”
  &&  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - mid ) ) * (r_pre - mid ) ) ) <= INT64_MAX) ”
  &&  “ (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) ) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0)))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (first_after)))) -> ((0 <= (Znth i first_after 0)) /\ ((Znth i first_after 0) <= 1000000000))) ”
  &&  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - (l_pre + zeros ) ) ) * (r_pre - (l_pre + zeros ) ) ) ) <= INT64_MAX) ”
  &&  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) )) ”
) \/
(
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) )) ”
  &&  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - (l_pre + zeros ) ) ) * (r_pre - (l_pre + zeros ) ) ) ) <= INT64_MAX) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (first_after)))) -> ((0 <= (Znth i first_after 0)) /\ ((Znth i first_after 0) <= 1000000000))) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0)))) ”
  &&  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - (l_pre + zeros ) ) ) * (r_pre - (l_pre + zeros ) ) ) ) <= INT64_MAX) ”
  &&  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) )) ”
).

Definition solve_partial_solve_wit_10_pure_split_goal_1 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) )) ”
.

Definition solve_partial_solve_wit_10_pure_split_goal_2 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - (l_pre + zeros ) ) ) * (r_pre - (l_pre + zeros ) ) ) ) <= INT64_MAX) ”
.

Definition solve_partial_solve_wit_10_pure_split_goal_3 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (first_after)))) -> ((0 <= (Znth i first_after 0)) /\ ((Znth i first_after 0) <= 1000000000))) ”
.

Definition solve_partial_solve_wit_10_pure_split_goal_4 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0)))) ”
.

Definition solve_partial_solve_wit_10_pure_split_goal_5 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - (l_pre + zeros ) ) ) * (r_pre - (l_pre + zeros ) ) ) ) <= INT64_MAX) ”
.

Definition solve_partial_solve_wit_10_pure_split_goal_6 :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (ones <= INT64_MAX)) (PreH2 : (zeros <= INT64_MAX)) (PreH3 : (ones >= INT64_MIN)) (PreH4 : (zeros >= INT64_MIN)) (PreH5 : (p <= INT_MAX)) (PreH6 : (mid <= INT_MAX)) (PreH7 : (bit_pre <= INT_MAX)) (PreH8 : (r_pre <= INT_MAX)) (PreH9 : (l_pre <= INT_MAX)) (PreH10 : (p >= INT_MIN)) (PreH11 : (mid >= INT_MIN)) (PreH12 : (bit_pre >= INT_MIN)) (PreH13 : (r_pre >= INT_MIN)) (PreH14 : (l_pre >= INT_MIN)) (PreH15 : (0 <= l_pre)) (PreH16 : (l_pre <= mid)) (PreH17 : (mid <= r_pre)) (PreH18 : (r_pre <= n_total)) (PreH19 : (n_total <= 300000)) (PreH20 : (mid = (l_pre + zeros ))) (PreH21 : (p = r_pre)) (PreH22 : (0 <= bit_pre)) (PreH23 : (bit_pre < 30)) (PreH24 : (0 <= capacity)) (PreH25 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH26 : ((-1) <= (bit_pre - 1 ))) (PreH27 : ((bit_pre - 1 ) < 30)) (PreH28 : ((Zlength (partition_before)) = n_total)) (PreH29 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH30 : ((Zlength (partition_scratch)) = n_total)) (PreH31 : ((Zlength (first_after)) = n_total)) (PreH32 : ((Zlength (first_scratch)) = n_total)) (PreH33 : ((Zlength (first_cost)) = 30)) (PreH34 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH36 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH37 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH38 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH39 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH40 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH41 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "zeros" ) )) # Int64  |-> zeros)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ones" ) )) # Int64  |-> ones)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) )) ”
.

Definition solve_partial_solve_wit_10_aux :=
forall (cost_before: (@list (@list Z))) (before: (@list Z)) (capacity: Z) (tmp_p: Z) (a_p: Z) (n_total: Z) (l_pre: Z) (r_pre: Z) (bit_pre: Z) (partition_before: (@list Z)) (partitioned: (@list Z)) (partition_scratch: (@list (@option Z))) (counted_costs: (@list (@list Z))) (first_after: (@list Z)) (first_scratch: (@list (@option Z))) (first_cost: (@list (@list Z))) (mid: Z) (zeros: Z) (p: Z) (ones: Z) __default__App_option_Z __default__List_Z (PreH1 : (0 <= l_pre)) (PreH2 : (l_pre <= mid)) (PreH3 : (mid <= r_pre)) (PreH4 : (r_pre <= n_total)) (PreH5 : (n_total <= 300000)) (PreH6 : (mid = (l_pre + zeros ))) (PreH7 : (p = r_pre)) (PreH8 : (0 <= bit_pre)) (PreH9 : (bit_pre < 30)) (PreH10 : (0 <= capacity)) (PreH11 : ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX)) (PreH12 : ((-1) <= (bit_pre - 1 ))) (PreH13 : ((bit_pre - 1 ) < 30)) (PreH14 : ((Zlength (partition_before)) = n_total)) (PreH15 : ((Zlength (partitioned)) = (r_pre - l_pre ))) (PreH16 : ((Zlength (partition_scratch)) = n_total)) (PreH17 : ((Zlength (first_after)) = n_total)) (PreH18 : ((Zlength (first_scratch)) = n_total)) (PreH19 : ((Zlength (first_cost)) = 30)) (PreH20 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0))))) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000)))) (PreH22 : forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0)))))) (PreH23 : (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones )) (PreH24 : (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 )) (PreH25 : (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre )) (PreH26 : (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) )) (PreH27 : (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) )),
  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
|--
  “ (0 <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (r_pre <= (Zlength (first_after))) ”
  &&  “ ((Zlength (first_after)) <= 300000) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (first_after)) = (Zlength (first_after))) ”
  &&  “ ((Zlength (first_scratch)) = (Zlength (first_after))) ”
  &&  “ ((Zlength (first_cost)) = 30) ”
  &&  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) )) ”
  &&  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - mid ) ) * (r_pre - mid ) ) ) <= INT64_MAX) ”
  &&  “ (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) ) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b first_cost __default__List_Z) 0)))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (first_after)))) -> ((0 <= (Znth i first_after 0)) /\ ((Znth i first_after 0) <= 1000000000))) ”
  &&  “ ((((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) ) + ((((bit_pre - 1 ) + 1 ) * (r_pre - (l_pre + zeros ) ) ) * (r_pre - (l_pre + zeros ) ) ) ) <= INT64_MAX) ”
  &&  “ (0 <= ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * ((l_pre + zeros ) - l_pre ) ) * ((l_pre + zeros ) - l_pre ) ) )) ”
  &&  “ (0 <= l_pre) ”
  &&  “ (l_pre <= mid) ”
  &&  “ (mid <= r_pre) ”
  &&  “ (r_pre <= n_total) ”
  &&  “ (n_total <= 300000) ”
  &&  “ (mid = (l_pre + zeros )) ”
  &&  “ (p = r_pre) ”
  &&  “ (0 <= bit_pre) ”
  &&  “ (bit_pre < 30) ”
  &&  “ (0 <= capacity) ”
  &&  “ ((capacity + (((bit_pre + 1 ) * (r_pre - l_pre ) ) * (r_pre - l_pre ) ) ) <= INT64_MAX) ”
  &&  “ ((-1) <= (bit_pre - 1 )) ”
  &&  “ ((bit_pre - 1 ) < 30) ”
  &&  “ ((Zlength (partition_before)) = n_total) ”
  &&  “ ((Zlength (partitioned)) = (r_pre - l_pre )) ”
  &&  “ ((Zlength (partition_scratch)) = n_total) ”
  &&  “ ((Zlength (first_after)) = n_total) ”
  &&  “ ((Zlength (first_scratch)) = n_total) ”
  &&  “ ((Zlength (first_cost)) = 30) ”
  &&  “ forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 first_cost __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b_2 first_cost __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b_2 first_cost __default__List_Z) 0)))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_total)) -> ((0 <= (Znth k first_after 0)) /\ ((Znth k first_after 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((l_pre <= k_2) /\ (k_2 < r_pre)) -> ((Znth k_2 partition_scratch __default__App_option_Z) = (Some ((Znth (k_2 - l_pre ) partitioned 0))))) ”
  &&  “ (SolveCountPrefix before cost_before counted_costs l_pre r_pre bit_pre zeros ones ) ”
  &&  “ (StablePartitionPrefix before partition_scratch l_pre r_pre bit_pre r_pre p 1 ) ”
  &&  “ (PartitionCopyBack before partition_before partitioned l_pre r_pre r_pre ) ”
  &&  “ (SolveEffect partition_before first_after counted_costs first_cost l_pre mid (bit_pre - 1 ) ) ”
  &&  “ (CostBound first_cost ((capacity + ((r_pre - l_pre ) * (r_pre - l_pre ) ) ) + ((bit_pre * (mid - l_pre ) ) * (mid - l_pre ) ) ) ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (first_after)) first_after )
  **  (IntArray.mixed_full tmp_p (Zlength (first_after)) first_scratch )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 first_cost )
.

Definition solve_partial_solve_wit_10 := solve_partial_solve_wit_10_pure -> solve_partial_solve_wit_10_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (cells: (@list (@option Z))) (retval: Z) (cells_2: (@list (@option Z))) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : ((Zlength (cells_2)) = n_pre)) (PreH3 : (retval <> 0)) (PreH4 : ((Zlength (cells)) = n_pre)) (PreH5 : (1 <= (Zlength (input_values)))) (PreH6 : ((Zlength (input_values)) <= 300000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (input_values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.mixed_full retval_2 n_pre cells_2 )
  **  (IntArray.mixed_full retval n_pre cells )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  (IntArray.mixed_full a_p n_pre (replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells)) )
  **  (IntArray.full input_pre n_pre input_values )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  (IntArray.mixed_full a_p n_pre (replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells)) )
  **  (IntArray.full input_pre n_pre input_values )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full a_p n_pre a_cells )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b <= 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) (30 - b ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (30 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 30) ”
.

Definition solver_safety_wit_6 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((b + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (b + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells)) = n_pre)) (PreH8 : ((Zlength (zero_rows)) = b)) (PreH9 : forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells b )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH5 : ((Zlength (zero_costs)) = 30)) (PreH6 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH7 : (CostBound zero_costs 0 )) (PreH8 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH5 : ((Zlength (zero_costs)) = 30)) (PreH6 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH7 : (CostBound zero_costs 0 )) (PreH8 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (29 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 29) ”
.

Definition solver_safety_wit_14 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "inv" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (input_values)) after )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "inv" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (input_values)) after )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> 0)
  **  ((( &( "inv" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (input_values)) after )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)) (x: Z) (inv: Z) (b: Z) (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (0 <= b)) (PreH5 : (b <= 30)) (PreH6 : (0 <= inv)) (PreH7 : (inv <= 90000000000)) (PreH8 : (0 <= x)) (PreH9 : (x < 1073741824)) (PreH10 : ((Zlength (current)) = n_pre)) (PreH11 : ((Zlength (tmp_cells)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH14 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (30 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 30) ”
.

Definition solver_safety_wit_18 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (0 <= b)) (PreH5 : (b < 30)) (PreH6 : (0 <= inv)) (PreH7 : (inv <= 90000000000)) (PreH8 : (0 <= x)) (PreH9 : (x < 1073741824)) (PreH10 : ((Zlength (current)) = n_pre)) (PreH11 : ((Zlength (tmp_cells)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH14 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (0 <= b)) (PreH5 : (b < 30)) (PreH6 : (0 <= inv)) (PreH7 : (inv <= 90000000000)) (PreH8 : (0 <= x)) (PreH9 : (x < 1073741824)) (PreH10 : ((Zlength (current)) = n_pre)) (PreH11 : ((Zlength (tmp_cells)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH14 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((inv + (Znth 1 (Znth b costs __default__List_Z) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (inv + (Znth 1 (Znth b costs __default__List_Z) 0) )) ”
) \/
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((inv + (Znth 1 (Znth b costs __default__List_Z) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (inv + (Znth 1 (Znth b costs __default__List_Z) 0) )) ”
).

Definition solver_safety_wit_20_split_goal_1 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((inv + (Znth 1 (Znth b costs __default__List_Z) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_20_split_goal_2 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((INT64_MIN) <= (inv + (Znth 1 (Znth b costs __default__List_Z) 0) )) ”
.

Definition solver_safety_wit_21 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((signed_last_nbits ((1 * (2^b) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^b) )) (32))) ”
  &&  “ (b <= 31) ”
  &&  “ (0 <= b) ”
) \/
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((signed_last_nbits ((1 * (2^b) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^b) )) (32))) ”
  &&  “ (b <= 31) ”
  &&  “ (0 <= b) ”
).

Definition solver_safety_wit_22_split_goal_1 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((signed_last_nbits ((1 * (2^b) )) (32)) <= INT_MAX) ”
.

Definition solver_safety_wit_22_split_goal_2 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^b) )) (32))) ”
.

Definition solver_safety_wit_22_split_goal_3 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (b <= 31) ”
.

Definition solver_safety_wit_22_split_goal_4 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= b) ”
.

Definition solver_safety_wit_23 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((inv + (Znth 0 (Znth b costs __default__List_Z) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (inv + (Znth 0 (Znth b costs __default__List_Z) 0) )) ”
) \/
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((inv + (Znth 0 (Znth b costs __default__List_Z) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (inv + (Znth 0 (Znth b costs __default__List_Z) 0) )) ”
).

Definition solver_safety_wit_24_split_goal_1 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((inv + (Znth 0 (Znth b costs __default__List_Z) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((INT64_MIN) <= (inv + (Znth 0 (Znth b costs __default__List_Z) 0) )) ”
.

Definition solver_safety_wit_25 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_26 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> (Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32))))
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((b + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (b + 1 )) ”
.

Definition solver_safety_wit_27 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) < (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 1 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> (Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32))))
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_28 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 0 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ ((b + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (b + 1 )) ”
.

Definition solver_safety_wit_29 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (current: (@list Z)) (tmp_cells: (@list (@option Z))) (costs: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs __default__List_Z) 0) >= (Znth 0 (Znth b costs __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs b inv x )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "inv" ) )) # Int64  |-> (inv + (Znth 0 (Znth b costs __default__List_Z) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (costs: (@list (@list Z))) (x: Z) (inv: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv) (x)) )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (costs: (@list (@list Z))) (x: Z) (inv: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv) (x)) )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> 0)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (cells: (@list (@option Z))) (retval: Z) (cells_2: (@list (@option Z))) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : ((Zlength (cells_2)) = n_pre)) (PreH3 : (retval <> 0)) (PreH4 : ((Zlength (cells)) = n_pre)) (PreH5 : (1 <= (Zlength (input_values)))) (PreH6 : ((Zlength (input_values)) <= 300000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (input_values)))),
  (IntArray.mixed_full retval_2 n_pre cells_2 )
  **  (IntArray.mixed_full retval n_pre cells )
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (a_cells)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ (InputCopyPrefix input_values a_cells 0 ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full a_p n_pre a_cells )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (cells: (@list (@option Z))) (retval: Z) (cells_2: (@list (@option Z))) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : ((Zlength (cells_2)) = n_pre)) (PreH3 : (retval <> 0)) (PreH4 : ((Zlength (cells)) = n_pre)) (PreH5 : (1 <= (Zlength (input_values)))) (PreH6 : ((Zlength (input_values)) <= 300000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (input_values)))),
  TT && emp 
|--
  “ (InputCopyPrefix input_values cells 0 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (cells_2)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (input_values: (@list Z)) (n_pre: Z) (cells: (@list (@option Z))) (retval: Z) (cells_2: (@list (@option Z))) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : ((Zlength (cells_2)) = n_pre)) (PreH3 : (retval <> 0)) (PreH4 : ((Zlength (cells)) = n_pre)) (PreH5 : (1 <= (Zlength (input_values)))) (PreH6 : ((Zlength (input_values)) <= 300000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (input_values)))),
  (InputCopyPrefix input_values cells 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (input_values: (@list Z)) (n_pre: Z) (cells: (@list (@option Z))) (retval: Z) (cells_2: (@list (@option Z))) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : ((Zlength (cells_2)) = n_pre)) (PreH3 : (retval <> 0)) (PreH4 : ((Zlength (cells)) = n_pre)) (PreH5 : (1 <= (Zlength (input_values)))) (PreH6 : ((Zlength (input_values)) <= 300000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (input_values)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (cells_2)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))
.

Definition solver_entail_wit_2 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (tmp_cells_2: (@list (@option Z))) (a_cells_2: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells_2)) = n_pre)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells_2 i )),
  (IntArray.mixed_full a_p_2 n_pre (replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells_2)) )
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (a_cells)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ (InputCopyPrefix input_values a_cells (i + 1 ) ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full a_p n_pre a_cells )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (a_cells_2: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells_2)) = n_pre)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells_2 i )),
  TT && emp 
|--
  “ (InputCopyPrefix input_values (replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells_2)) (i + 1 ) ) ”
  &&  “ ((Zlength ((replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells_2)))) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (a_cells_2: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells_2)) = n_pre)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells_2 i )),
  (InputCopyPrefix input_values (replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells_2)) (i + 1 ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (a_cells_2: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells_2)) = n_pre)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells_2 i )),
  ((Zlength ((replace_Znth (i) ((Some ((Znth i input_values 0)))) (a_cells_2)))) = n_pre)
.

Definition solver_entail_wit_3 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (tmp_cells_2: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full a_p_2 n_pre a_cells )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (tmp_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 30) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ ((Zlength (zero_rows)) = 0) ”
  &&  “ forall (row: Z), (((0 <= row) /\ (row < 0)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0))) ”
  &&  “ (ZeroCostPrefix cost_cells 0 ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 0 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (0 * (2 * sizeof(INT64)))) (30 - 0 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (a_p_2: Z) (tmp_cells_2: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  (IntArray.mixed_full a_p_2 n_pre a_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
|--
  EX (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 30) ”
  &&  “ ((Zlength (tmp_cells_2)) = n_pre) ”
  &&  “ ((Zlength (zero_rows)) = 0) ”
  &&  “ forall (row: Z), (((0 <= row) /\ (row < 0)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0))) ”
  &&  “ (ZeroCostPrefix cost_cells 0 ) ”
  &&  (IntArray.full a_p_2 n_pre input_values )
  **  (Int64Array2.full ( &( "cost" ) ) 0 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (0 * (2 * sizeof(INT64)))) (30 - 0 ) 2 )
).

Definition solver_entail_wit_4 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (cost_cells_2: (@list (@list (@option Z)))) (zero_rows_2: (@list (@list Z))) (tmp_cells_2: (@list (@option Z))) (b: Z) __default__List_Z (PreH1 : (b < 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH6 : (0 <= b)) (PreH7 : (b <= 30)) (PreH8 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH9 : ((Zlength (zero_rows_2)) = b)) (PreH10 : forall (row_2: Z), (((0 <= row_2) /\ (row_2 < b)) -> ((((Zlength ((Znth row_2 zero_rows_2 __default__List_Z))) = 2) /\ ((Znth 0 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)))) (PreH11 : (ZeroCostPrefix cost_cells_2 b )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre input_values )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows_2 )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) (30 - b ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (tmp_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= b) ”
  &&  “ (b < 30) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ ((Zlength (zero_rows)) = b) ”
  &&  “ forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0))) ”
  &&  “ (ZeroCostPrefix cost_cells b ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (cost_cells_2: (@list (@list (@option Z)))) (zero_rows_2: (@list (@list Z))) (tmp_cells_2: (@list (@option Z))) (b: Z) __default__List_Z (PreH1 : (b < 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH6 : (0 <= b)) (PreH7 : (b <= 30)) (PreH8 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH9 : ((Zlength (zero_rows_2)) = b)) (PreH10 : forall (row_2: Z), (((0 <= row_2) /\ (row_2 < b)) -> ((((Zlength ((Znth row_2 zero_rows_2 __default__List_Z))) = 2) /\ ((Znth 0 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)))) (PreH11 : (ZeroCostPrefix cost_cells_2 b )),
  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows_2 )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) (30 - b ) 2 )
|--
  EX (x_2: Z) (x: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= b) ”
  &&  “ (b < 30) ”
  &&  “ ((Zlength (tmp_cells_2)) = n_pre) ”
  &&  “ ((Zlength (zero_rows)) = b) ”
  &&  “ forall (row: Z), (((0 <= row) /\ (row < b)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0))) ”
  &&  “ (ZeroCostPrefix cost_cells b ) ”
  &&  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> x_2)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> x)
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
).

Definition solver_entail_wit_5 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p_2: Z) (tmp_p_2: Z) (tmp_cells_2: (@list (@option Z))) (cost_cells_2: (@list (@list (@option Z)))) (zero_rows_2: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH8 : ((Zlength (zero_rows_2)) = b)) (PreH9 : forall (row_2: Z), (((0 <= row_2) /\ (row_2 < b)) -> ((((Zlength ((Znth row_2 zero_rows_2 __default__List_Z))) = 2) /\ ((Znth 0 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)))) (PreH10 : (ZeroCostPrefix cost_cells_2 b )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre input_values )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows_2 )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (tmp_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= (b + 1 )) ”
  &&  “ ((b + 1 ) <= 30) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ ((Zlength (zero_rows)) = (b + 1 )) ”
  &&  “ forall (row: Z), (((0 <= row) /\ (row < (b + 1 ))) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0))) ”
  &&  “ (ZeroCostPrefix cost_cells (b + 1 ) ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) (b + 1 ) 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) (30 - (b + 1 ) ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (cost_cells_2: (@list (@list (@option Z)))) (zero_rows_2: (@list (@list Z))) (b: Z) __default__List_Z (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (n_pre = (Zlength (input_values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH7 : (0 <= b)) (PreH8 : (b < 30)) (PreH9 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH10 : ((Zlength (zero_rows_2)) = b)) (PreH11 : forall (row_2: Z), (((0 <= row_2) /\ (row_2 < b)) -> ((((Zlength ((Znth row_2 zero_rows_2 __default__List_Z))) = 2) /\ ((Znth 0 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row_2 zero_rows_2 __default__List_Z) 0) = 0)))) (PreH12 : (ZeroCostPrefix cost_cells_2 b )),
  (Int64Array2.full ( &( "cost" ) ) b 2 zero_rows_2 )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 )
|--
  EX (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= (b + 1 )) ”
  &&  “ ((b + 1 ) <= 30) ”
  &&  “ ((Zlength (tmp_cells_2)) = n_pre) ”
  &&  “ ((Zlength (zero_rows)) = (b + 1 )) ”
  &&  “ forall (row: Z), (((0 <= row) /\ (row < (b + 1 ))) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0))) ”
  &&  “ (ZeroCostPrefix cost_cells (b + 1 ) ) ”
  &&  (Int64Array2.full ( &( "cost" ) ) (b + 1 ) 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) (30 - (b + 1 ) ) 2 )
).

Definition solver_entail_wit_6 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (tmp_cells_2: (@list (@option Z))) (b_2: Z) __default__List_Z (PreH1 : (b_2 >= 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH6 : (0 <= b_2)) (PreH7 : (b_2 <= 30)) (PreH8 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH9 : ((Zlength (zero_rows)) = b_2)) (PreH10 : forall (row: Z), (((0 <= row) /\ (row < b_2)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH11 : (ZeroCostPrefix cost_cells b_2 )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre input_values )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) b_2 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (b_2 * (2 * sizeof(INT64)))) (30 - b_2 ) 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (zero_costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ ((Zlength (tmp_cells)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (zero_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0))) ”
  &&  “ (CostBound zero_costs 0 ) ”
  &&  “ (((30 * n_pre ) * n_pre ) <= INT64_MAX) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (cost_cells: (@list (@list (@option Z)))) (zero_rows: (@list (@list Z))) (tmp_cells_2: (@list (@option Z))) (b_2: Z) __default__List_Z (PreH1 : (b_2 >= 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input_values 0)) /\ ((Znth k_2 input_values 0) <= 1000000000)))) (PreH6 : (0 <= b_2)) (PreH7 : (b_2 <= 30)) (PreH8 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH9 : ((Zlength (zero_rows)) = b_2)) (PreH10 : forall (row: Z), (((0 <= row) /\ (row < b_2)) -> ((((Zlength ((Znth row zero_rows __default__List_Z))) = 2) /\ ((Znth 0 (Znth row zero_rows __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth row zero_rows __default__List_Z) 0) = 0)))) (PreH11 : (ZeroCostPrefix cost_cells b_2 )),
  (IntArray.full a_p_2 n_pre input_values )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) b_2 2 zero_rows )
  **  (Int64Array2.undef_full (( &( "cost" ) ) + (b_2 * (2 * sizeof(INT64)))) (30 - b_2 ) 2 )
|--
  EX (zero_costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ ((Zlength (tmp_cells)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (zero_costs)) = 30) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0))) ”
  &&  “ (CostBound zero_costs 0 ) ”
  &&  “ (((30 * n_pre ) * n_pre ) <= INT64_MAX) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  (IntArray.full a_p_2 (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p_2 (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
).

Definition solver_entail_wit_7 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p_2: Z) (tmp_p_2: Z) (tmp_cells_2: (@list (@option Z))) (zero_costs: (@list (@list Z))) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells_2)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (input_values)))) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  (IntArray.full a_p_2 (Zlength (input_values)) after )
  **  (IntArray.mixed_full tmp_p_2 (Zlength (input_values)) scratch_after )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_after )
  **  (IntArray.full input_pre n_pre input_values )
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 30) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 90000000000) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < 1073741824) ”
  &&  “ ((Zlength (current)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs 0 0 0 ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (zero_costs: (@list (@list Z))) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells_2)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (input_values)))) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))),
  TT && emp 
|--
  “ (XorChoicePrefix input_values cost_after 0 0 0 ) ”
  &&  “ ((Zlength (scratch_after)) = n_pre) ”
  &&  “ ((Zlength (after)) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (zero_costs: (@list (@list Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells_2)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (input_values)))) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))),
  (XorChoicePrefix input_values cost_after 0 0 0 )
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (zero_costs: (@list (@list Z))) (scratch_after: (@list (@option Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells_2)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (input_values)))) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))),
  ((Zlength (scratch_after)) = n_pre)
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (input_values: (@list Z)) (n_pre: Z) (tmp_cells_2: (@list (@option Z))) (zero_costs: (@list (@list Z))) (after: (@list Z)) (cost_after: (@list (@list Z))) __default__List_Z (PreH1 : (SolveEffect input_values after zero_costs cost_after 0 n_pre 29 )) (PreH2 : (CostBound cost_after (0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) )) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i after 0)) /\ ((Znth i after 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : ((Zlength (tmp_cells_2)) = (Zlength (input_values)))) (PreH8 : ((Zlength (zero_costs)) = 30)) (PreH9 : forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b zero_costs __default__List_Z) 0) = 0)))) (PreH10 : (CostBound zero_costs 0 )) (PreH11 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (input_values)))) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))),
  ((Zlength (after)) = n_pre)
.

Definition solver_entail_wit_8 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (costs_2: (@list (@list Z))) (tmp_cells_2: (@list (@option Z))) (current_2: (@list Z)) (x: Z) (inv: Z) (b: Z) __default__List_Z (PreH1 : (b < 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b <= 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current_2)) = n_pre)) (PreH12 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))) (PreH14 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 current_2 0)) /\ ((Znth k_4 current_2 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs_2 b inv x )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre current_2 )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs_2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= b) ”
  &&  “ (b < 30) ”
  &&  “ (0 <= inv) ”
  &&  “ (inv <= 90000000000) ”
  &&  “ (0 <= x) ”
  &&  “ (x < 1073741824) ”
  &&  “ ((Zlength (current)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs b inv x ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (costs_2: (@list (@list Z))) (tmp_cells_2: (@list (@option Z))) (current_2: (@list Z)) (x: Z) (inv: Z) (b: Z) __default__List_Z (PreH1 : (b < 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b <= 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current_2)) = n_pre)) (PreH12 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))) (PreH14 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 current_2 0)) /\ ((Znth k_4 current_2 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs_2 b inv x )),
  (Int64Array2.full ( &( "cost" ) ) 30 2 costs_2 )
|--
  EX (costs: (@list (@list Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= b) ”
  &&  “ (b < 30) ”
  &&  “ (0 <= inv) ”
  &&  “ (inv <= 90000000000) ”
  &&  “ (0 <= x) ”
  &&  “ (x < 1073741824) ”
  &&  “ ((Zlength (current_2)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells_2)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current_2 0)) /\ ((Znth k_2 current_2 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs b inv x ) ”
  &&  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs)) )
).

Definition solver_entail_wit_9_1 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p_2: Z) (tmp_p_2: Z) (current_2: (@list Z)) (tmp_cells_2: (@list (@option Z))) (costs_2: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) < (Znth 0 (Znth b costs_2 __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current_2)) = n_pre)) (PreH12 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))) (PreH14 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 current_2 0)) /\ ((Znth k_4 current_2 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs_2 b inv x )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre current_2 )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs_2)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs_2 __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs_2 __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs_2)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= (b + 1 )) ”
  &&  “ ((b + 1 ) <= 30) ”
  &&  “ (0 <= (inv + (Znth 1 (Znth b costs_2 __default__List_Z) 0) )) ”
  &&  “ ((inv + (Znth 1 (Znth b costs_2 __default__List_Z) 0) ) <= 90000000000) ”
  &&  “ (0 <= (Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32)))) ”
  &&  “ ((Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32))) < 1073741824) ”
  &&  “ ((Zlength (current)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs (b + 1 ) (inv + (Znth 1 (Znth b costs_2 __default__List_Z) 0) ) (Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32))) ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (current_2: (@list Z)) (tmp_cells_2: (@list (@option Z))) (costs_2: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) <= INT64_MAX)) (PreH2 : ((Znth 0 (Znth b costs_2 __default__List_Z) 0) <= INT64_MAX)) (PreH3 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) >= INT64_MIN)) (PreH4 : ((Znth 0 (Znth b costs_2 __default__List_Z) 0) >= INT64_MIN)) (PreH5 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) < (Znth 0 (Znth b costs_2 __default__List_Z) 0))) (PreH6 : (n_pre = (Zlength (input_values)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 300000)) (PreH9 : (0 <= b)) (PreH10 : (b < 30)) (PreH11 : (0 <= inv)) (PreH12 : (inv <= 90000000000)) (PreH13 : (0 <= x)) (PreH14 : (x < 1073741824)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))) (PreH18 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 current_2 0)) /\ ((Znth k_4 current_2 0) <= 1000000000)))) (PreH19 : (XorChoicePrefix input_values costs_2 b inv x )),
  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs_2)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs_2 __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs_2 __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs_2)) )
|--
  EX (costs: (@list (@list Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= (b + 1 )) ”
  &&  “ ((b + 1 ) <= 30) ”
  &&  “ (0 <= (inv + (Znth 1 (Znth b costs_2 __default__List_Z) 0) )) ”
  &&  “ ((inv + (Znth 1 (Znth b costs_2 __default__List_Z) 0) ) <= 90000000000) ”
  &&  “ (0 <= (Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32)))) ”
  &&  “ ((Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32))) < 1073741824) ”
  &&  “ ((Zlength (current_2)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells_2)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current_2 0)) /\ ((Znth k_2 current_2 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs (b + 1 ) (inv + (Znth 1 (Znth b costs_2 __default__List_Z) 0) ) (Z.lor x (signed_last_nbits ((Z.shiftl 1 b)) (32))) ) ”
  &&  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
).

Definition solver_entail_wit_9_2 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p_2: Z) (tmp_p_2: Z) (current_2: (@list Z)) (tmp_cells_2: (@list (@option Z))) (costs_2: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) >= (Znth 0 (Znth b costs_2 __default__List_Z) 0))) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b < 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current_2)) = n_pre)) (PreH12 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))) (PreH14 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 current_2 0)) /\ ((Znth k_4 current_2 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs_2 b inv x )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre current_2 )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2 )
  **  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs_2)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs_2 __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs_2 __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs_2)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  EX (tmp_p: Z) (a_p: Z) (costs: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= (b + 1 )) ”
  &&  “ ((b + 1 ) <= 30) ”
  &&  “ (0 <= (inv + (Znth 0 (Znth b costs_2 __default__List_Z) 0) )) ”
  &&  “ ((inv + (Znth 0 (Znth b costs_2 __default__List_Z) 0) ) <= 90000000000) ”
  &&  “ (0 <= x) ”
  &&  “ (x < 1073741824) ”
  &&  “ ((Zlength (current)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs (b + 1 ) (inv + (Znth 0 (Znth b costs_2 __default__List_Z) 0) ) x ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p n_pre current )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (current_2: (@list Z)) (tmp_cells_2: (@list (@option Z))) (costs_2: (@list (@list Z))) (b: Z) (inv: Z) (x: Z) __default__List_Z (PreH1 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) <= INT64_MAX)) (PreH2 : ((Znth 0 (Znth b costs_2 __default__List_Z) 0) <= INT64_MAX)) (PreH3 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) >= INT64_MIN)) (PreH4 : ((Znth 0 (Znth b costs_2 __default__List_Z) 0) >= INT64_MIN)) (PreH5 : ((Znth 1 (Znth b costs_2 __default__List_Z) 0) >= (Znth 0 (Znth b costs_2 __default__List_Z) 0))) (PreH6 : (n_pre = (Zlength (input_values)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 300000)) (PreH9 : (0 <= b)) (PreH10 : (b < 30)) (PreH11 : (0 <= inv)) (PreH12 : (inv <= 90000000000)) (PreH13 : (0 <= x)) (PreH14 : (x < 1073741824)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (tmp_cells_2)) = n_pre)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input_values 0)) /\ ((Znth k_3 input_values 0) <= 1000000000)))) (PreH18 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 current_2 0)) /\ ((Znth k_4 current_2 0) <= 1000000000)))) (PreH19 : (XorChoicePrefix input_values costs_2 b inv x )),
  (Int64Array2.full ( &( "cost" ) ) b 2 (sublist (0) (b) (costs_2)) )
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 (Znth b costs_2 __default__List_Z) 0))
  **  ((((( &( "cost" ) ) + (b * (2 * sizeof(INT64)))) + (1 * sizeof(INT64)))) # Int64  |-> (Znth 1 (Znth b costs_2 __default__List_Z) 0))
  **  (Int64Array2.full (( &( "cost" ) ) + ((b + 1 ) * (2 * sizeof(INT64)))) ((30 - b ) - 1 ) 2 (sublist ((b + 1 )) (30) (costs_2)) )
|--
  EX (costs: (@list (@list Z))),
  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ (0 <= (b + 1 )) ”
  &&  “ ((b + 1 ) <= 30) ”
  &&  “ (0 <= (inv + (Znth 0 (Znth b costs_2 __default__List_Z) 0) )) ”
  &&  “ ((inv + (Znth 0 (Znth b costs_2 __default__List_Z) 0) ) <= 90000000000) ”
  &&  “ (0 <= x) ”
  &&  “ (x < 1073741824) ”
  &&  “ ((Zlength (current_2)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells_2)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current_2 0)) /\ ((Znth k_2 current_2 0) <= 1000000000))) ”
  &&  “ (XorChoicePrefix input_values costs (b + 1 ) (inv + (Znth 0 (Znth b costs_2 __default__List_Z) 0) ) x ) ”
  &&  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
).

Definition solver_entail_wit_10 :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (costs_2: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)) (x: Z) (inv: Z) (b: Z) (PreH1 : (b >= 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b <= 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs_2 b inv x )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p_2 n_pre current )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs_2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p_2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p_2)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  EX (costs: (@list (@list Z))) (tmp_p: Z) (a_p: Z),
  “ (0 <= n_pre) ”
  &&  “ (Spec input_values (pair (inv) (x)) ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.undef_full a_p n_pre )
  **  (IntArray.undef_full tmp_p n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
) \/
(
forall (input_values: (@list Z)) (n_pre: Z) (tmp_p_2: Z) (a_p_2: Z) (costs_2: (@list (@list Z))) (tmp_cells: (@list (@option Z))) (current: (@list Z)) (x: Z) (inv: Z) (b: Z) (PreH1 : (b >= 30)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (0 <= b)) (PreH6 : (b <= 30)) (PreH7 : (0 <= inv)) (PreH8 : (inv <= 90000000000)) (PreH9 : (0 <= x)) (PreH10 : (x < 1073741824)) (PreH11 : ((Zlength (current)) = n_pre)) (PreH12 : ((Zlength (tmp_cells)) = n_pre)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 current 0)) /\ ((Znth k_2 current 0) <= 1000000000)))) (PreH15 : (XorChoicePrefix input_values costs_2 b inv x )),
  (IntArray.full a_p_2 n_pre current )
  **  (IntArray.mixed_full tmp_p_2 n_pre tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs_2 )
|--
  EX (costs: (@list (@list Z))),
  “ (0 <= n_pre) ”
  &&  “ (Spec input_values (pair (inv) (x)) ) ”
  &&  (IntArray.undef_full a_p_2 n_pre )
  **  (IntArray.undef_full tmp_p_2 n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
).

Definition solver_return_wit_1 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (costs: (@list (@list Z))) (x_2: Z) (inv_2: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv_2) (x_2)) )),
  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> 0)
  **  ((( &( "tmp" ) )) # Ptr  |-> 0)
  **  ((out_inv_pre) # Int64  |-> inv_2)
  **  ((out_x_pre) # Int  |-> x_2)
|--
  EX (cost_post: (@list (@list Z))) (inv: Z) (x: Z),
  “ (Spec input_values (pair (inv) (x)) ) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 cost_post )
  **  ((( &( "a" ) )) # Ptr  |-> 0)
  **  ((( &( "tmp" ) )) # Ptr  |-> 0)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
.

Definition solver_partial_solve_wit_1_pure :=
forall (tmp_before: Z) (a_before: Z) (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (PreH1 : (1 <= (Zlength (input_values)))) (PreH2 : ((Zlength (input_values)) <= 300000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_before)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_before)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (tmp_before: Z) (a_before: Z) (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (PreH1 : (1 <= (Zlength (input_values)))) (PreH2 : ((Zlength (input_values)) <= 300000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (input_values)))),
  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_before)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_before)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
  &&  “ (1 <= (Zlength (input_values))) ”
  &&  “ ((Zlength (input_values)) <= 300000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000))) ”
  &&  “ (n_pre = (Zlength (input_values))) ”
  &&  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_before)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_before)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
forall (tmp_before: Z) (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (cells: (@list (@option Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Zlength (cells)) = n_pre)) (PreH3 : (1 <= (Zlength (input_values)))) (PreH4 : ((Zlength (input_values)) <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (input_values)))),
  (IntArray.mixed_full retval n_pre cells )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_before)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (tmp_before: Z) (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (cells: (@list (@option Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Zlength (cells)) = n_pre)) (PreH3 : (1 <= (Zlength (input_values)))) (PreH4 : ((Zlength (input_values)) <= 300000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (input_values)))),
  (IntArray.mixed_full retval n_pre cells )
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_before)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= n_pre) ”
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
  &&  “ (retval <> 0) ”
  &&  “ ((Zlength (cells)) = n_pre) ”
  &&  “ (1 <= (Zlength (input_values))) ”
  &&  “ ((Zlength (input_values)) <= 300000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000))) ”
  &&  “ (n_pre = (Zlength (input_values))) ”
  &&  (IntArray.mixed_full retval n_pre cells )
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_before)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full a_p n_pre a_cells )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (a_cells)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ (InputCopyPrefix input_values a_cells i ) ”
  &&  (((input_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input_values 0))
  **  (IntArray.missing_i input_pre i 0 n_pre input_values )
  **  (IntArray.mixed_full a_p n_pre a_cells )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
.

Definition solver_partial_solve_wit_4 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (tmp_p: Z) (a_p: Z) (tmp_cells: (@list (@option Z))) (a_cells: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input_values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (a_cells)) = n_pre)) (PreH9 : ((Zlength (tmp_cells)) = n_pre)) (PreH10 : (InputCopyPrefix input_values a_cells i )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full a_p n_pre a_cells )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (a_cells)) = n_pre) ”
  &&  “ ((Zlength (tmp_cells)) = n_pre) ”
  &&  “ (InputCopyPrefix input_values a_cells i ) ”
  &&  (((a_p + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i a_p i 0 n_pre a_cells )
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.mixed_full tmp_p n_pre tmp_cells )
  **  (Int64Array2.undef_full ( &( "cost" ) ) 30 2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
.

Definition solver_partial_solve_wit_5_pure :=
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH5 : ((Zlength (zero_costs)) = 30)) (PreH6 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b_2 zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b_2 zero_costs __default__List_Z) 0) = 0)))) (PreH7 : (CostBound zero_costs 0 )) (PreH8 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= (Zlength (input_values))) ”
  &&  “ ((Zlength (input_values)) <= 300000) ”
  &&  “ ((-1) <= 29) ”
  &&  “ (29 < 30) ”
  &&  “ ((Zlength (input_values)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (tmp_cells)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (zero_costs)) = 30) ”
  &&  “ (0 <= 0) ”
  &&  “ ((0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) <= INT64_MAX) ”
  &&  “ (CostBound zero_costs 0 ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000))) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b zero_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b zero_costs __default__List_Z) 0)))) ”
) \/
(
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (n_pre = (Zlength (input_values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH7 : ((Zlength (zero_costs)) = 30)) (PreH8 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b_2 zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b_2 zero_costs __default__List_Z) 0) = 0)))) (PreH9 : (CostBound zero_costs 0 )) (PreH10 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b zero_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b zero_costs __default__List_Z) 0)))) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000))) ”
).

Definition solver_partial_solve_wit_5_pure_split_goal_1 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (n_pre = (Zlength (input_values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH7 : ((Zlength (zero_costs)) = 30)) (PreH8 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b_2 zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b_2 zero_costs __default__List_Z) 0) = 0)))) (PreH9 : (CostBound zero_costs 0 )) (PreH10 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b zero_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b zero_costs __default__List_Z) 0)))) ”
.

Definition solver_partial_solve_wit_5_pure_split_goal_2 :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (n_pre = (Zlength (input_values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH7 : ((Zlength (zero_costs)) = 30)) (PreH8 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b_2 zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b_2 zero_costs __default__List_Z) 0) = 0)))) (PreH9 : (CostBound zero_costs 0 )) (PreH10 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000))) ”
.

Definition solver_partial_solve_wit_5_aux :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (tmp_cells: (@list (@option Z))) (zero_costs: (@list (@list Z))) __default__List_Z (PreH1 : (n_pre = (Zlength (input_values)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : ((Zlength (tmp_cells)) = (Zlength (input_values)))) (PreH5 : ((Zlength (zero_costs)) = 30)) (PreH6 : forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b_2 zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b_2 zero_costs __default__List_Z) 0) = 0)))) (PreH7 : (CostBound zero_costs 0 )) (PreH8 : (((30 * n_pre ) * n_pre ) <= INT64_MAX)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000)))),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
|--
  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= (Zlength (input_values))) ”
  &&  “ ((Zlength (input_values)) <= 300000) ”
  &&  “ ((-1) <= 29) ”
  &&  “ (29 < 30) ”
  &&  “ ((Zlength (input_values)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (tmp_cells)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (zero_costs)) = 30) ”
  &&  “ (0 <= 0) ”
  &&  “ ((0 + (((29 + 1 ) * (n_pre - 0 ) ) * (n_pre - 0 ) ) ) <= INT64_MAX) ”
  &&  “ (CostBound zero_costs 0 ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (input_values)))) -> ((0 <= (Znth i input_values 0)) /\ ((Znth i input_values 0) <= 1000000000))) ”
  &&  “ forall (b: Z), (((0 <= b) /\ (b < 30)) -> ((((Zlength ((Znth b zero_costs __default__List_Z))) = 2) /\ (0 <= (Znth 0 (Znth b zero_costs __default__List_Z) 0))) /\ (0 <= (Znth 1 (Znth b zero_costs __default__List_Z) 0)))) ”
  &&  “ (n_pre = (Zlength (input_values))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 300000) ”
  &&  “ ((Zlength (tmp_cells)) = (Zlength (input_values))) ”
  &&  “ ((Zlength (zero_costs)) = 30) ”
  &&  “ forall (b_2: Z), (((0 <= b_2) /\ (b_2 < 30)) -> ((((Zlength ((Znth b_2 zero_costs __default__List_Z))) = 2) /\ ((Znth 0 (Znth b_2 zero_costs __default__List_Z) 0) = 0)) /\ ((Znth 1 (Znth b_2 zero_costs __default__List_Z) 0) = 0))) ”
  &&  “ (CostBound zero_costs 0 ) ”
  &&  “ (((30 * n_pre ) * n_pre ) <= INT64_MAX) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (input_values)))) -> ((0 <= (Znth k input_values 0)) /\ ((Znth k input_values 0) <= 1000000000))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  (IntArray.full a_p (Zlength (input_values)) input_values )
  **  (IntArray.mixed_full tmp_p (Zlength (input_values)) tmp_cells )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 zero_costs )
  **  (IntArray.full input_pre n_pre input_values )
  **  ((out_inv_pre) # Int64  |->_)
  **  ((out_x_pre) # Int  |->_)
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6_pure :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (costs: (@list (@list Z))) (x: Z) (inv: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv) (x)) )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.undef_full a_p n_pre )
  **  (IntArray.undef_full tmp_p n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  “ (0 <= n_pre) ”
.

Definition solver_partial_solve_wit_6_aux :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (costs: (@list (@list Z))) (x: Z) (inv: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv) (x)) )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.undef_full a_p n_pre )
  **  (IntArray.undef_full tmp_p n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  “ (0 <= n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (Spec input_values (pair (inv) (x)) ) ”
  &&  (IntArray.undef_full a_p n_pre )
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.undef_full tmp_p n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
.

Definition solver_partial_solve_wit_6 := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux.

Definition solver_partial_solve_wit_7_pure :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (costs: (@list (@list Z))) (x: Z) (inv: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv) (x)) )),
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out_inv" ) )) # Ptr  |-> out_inv_pre)
  **  ((( &( "out_x" ) )) # Ptr  |-> out_x_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "inv" ) )) # Int64  |-> inv)
  **  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.undef_full tmp_p n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  “ (0 <= n_pre) ”
.

Definition solver_partial_solve_wit_7_aux :=
forall (input_values: (@list Z)) (input_pre: Z) (n_pre: Z) (out_inv_pre: Z) (out_x_pre: Z) (a_p: Z) (tmp_p: Z) (costs: (@list (@list Z))) (x: Z) (inv: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (Spec input_values (pair (inv) (x)) )),
  (IntArray.full input_pre n_pre input_values )
  **  (IntArray.undef_full tmp_p n_pre )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
|--
  “ (0 <= n_pre) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (Spec input_values (pair (inv) (x)) ) ”
  &&  (IntArray.undef_full tmp_p n_pre )
  **  (IntArray.full input_pre n_pre input_values )
  **  (Int64Array2.full ( &( "cost" ) ) 30 2 costs )
  **  ((( &( "a" ) )) # Ptr  |-> a_p)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp_p)
  **  ((out_inv_pre) # Int64  |-> inv)
  **  ((out_x_pre) # Int  |-> x)
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Module Type VC_Correct.


Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Axiom proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Axiom proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Axiom proof_of_solve_safety_wit_11 : solve_safety_wit_11.
Axiom proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Axiom proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Axiom proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Axiom proof_of_solve_safety_wit_15 : solve_safety_wit_15.
Axiom proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Axiom proof_of_solve_safety_wit_17 : solve_safety_wit_17.
Axiom proof_of_solve_safety_wit_18 : solve_safety_wit_18.
Axiom proof_of_solve_safety_wit_19 : solve_safety_wit_19.
Axiom proof_of_solve_safety_wit_20 : solve_safety_wit_20.
Axiom proof_of_solve_safety_wit_21 : solve_safety_wit_21.
Axiom proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Axiom proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Axiom proof_of_solve_safety_wit_24 : solve_safety_wit_24.
Axiom proof_of_solve_safety_wit_25 : solve_safety_wit_25.
Axiom proof_of_solve_safety_wit_26 : solve_safety_wit_26.
Axiom proof_of_solve_safety_wit_27 : solve_safety_wit_27.
Axiom proof_of_solve_safety_wit_28 : solve_safety_wit_28.
Axiom proof_of_solve_safety_wit_29 : solve_safety_wit_29.
Axiom proof_of_solve_safety_wit_30 : solve_safety_wit_30.
Axiom proof_of_solve_safety_wit_31 : solve_safety_wit_31.
Axiom proof_of_solve_safety_wit_32 : solve_safety_wit_32.
Axiom proof_of_solve_safety_wit_33 : solve_safety_wit_33.
Axiom proof_of_solve_safety_wit_34 : solve_safety_wit_34.
Axiom proof_of_solve_safety_wit_35 : solve_safety_wit_35.
Axiom proof_of_solve_safety_wit_36 : solve_safety_wit_36.
Axiom proof_of_solve_safety_wit_37 : solve_safety_wit_37.
Axiom proof_of_solve_safety_wit_38 : solve_safety_wit_38.
Axiom proof_of_solve_safety_wit_39 : solve_safety_wit_39.
Axiom proof_of_solve_safety_wit_40 : solve_safety_wit_40.
Axiom proof_of_solve_safety_wit_41 : solve_safety_wit_41.
Axiom proof_of_solve_safety_wit_42 : solve_safety_wit_42.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2_1 : solve_entail_wit_2_1.
Axiom proof_of_solve_entail_wit_2_2 : solve_entail_wit_2_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4_1 : solve_entail_wit_4_1.
Axiom proof_of_solve_entail_wit_4_2 : solve_entail_wit_4_2.
Axiom proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7_1 : solve_entail_wit_7_1.
Axiom proof_of_solve_entail_wit_7_2 : solve_entail_wit_7_2.
Axiom proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Axiom proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Axiom proof_of_solve_entail_wit_12 : solve_entail_wit_12.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_return_wit_2 : solve_return_wit_2.
Axiom proof_of_solve_return_wit_3 : solve_return_wit_3.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.
Axiom proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6.
Axiom proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7.
Axiom proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8.
Axiom proof_of_solve_partial_solve_wit_9_pure : solve_partial_solve_wit_9_pure.
Axiom proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9.
Axiom proof_of_solve_partial_solve_wit_10_pure : solve_partial_solve_wit_10_pure.
Axiom proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
