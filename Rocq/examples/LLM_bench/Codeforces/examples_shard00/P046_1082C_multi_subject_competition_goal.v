From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P046_1082C_multi_subject_competition_lib.
Local Open Scope sac.

(*----- Function cmp_candidate -----*)

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (students)))) (PreH2 : ((Zlength (students)) <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000))))) (PreH6 : (n_pre = (Zlength (students)))) (PreH7 : ((Zlength (raw)) = (2 * n_pre ))) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z))))))),
  ((( &( "total" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) __default__Prod_Z_Z (PreH1 : (Permutation students sorted )) (PreH2 : (CandidatesSorted sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw_sorted 0) = (fst ((Znth i_3 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw_sorted 0) = (snd ((Znth i_3 sorted __default__Prod_Z_Z))))))) (PreH6 : (retval <> 0)) (PreH7 : (1 <= (Zlength (students)))) (PreH8 : ((Zlength (students)) <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (n_pre = (Zlength (students)))) (PreH13 : ((Zlength (raw)) = (2 * n_pre ))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z))))))),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "total" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted i totals )) (PreH19 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (i * 10000 ))))),
  ((( &( "prefix" ) )) # Int64  |->_)
  **  ((( &( "j" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted i j prefix totals )) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH24 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((2 * i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition solver_safety_wit_5 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted i j prefix totals )) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH24 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((2 * j ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * j )) ”
.

Definition solver_safety_wit_6 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted i j prefix totals )) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH24 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_7 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted i j prefix totals )) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH24 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) )) ”
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) )) ”
).

Definition solver_safety_wit_8_split_goal_1 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_8_split_goal_2 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((INT64_MIN) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) )) ”
.

Definition solver_safety_wit_9 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (((2 * j ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * j ) + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((2 * j ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * j )) ”
.

Definition solver_safety_wit_11 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_12 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> prefix)
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (((j + 1 ) - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((j + 1 ) - i )) ”
.

Definition solver_safety_wit_16 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
|--
  “ (((Znth ((j + 1 ) - i ) totals 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth ((j + 1 ) - i ) totals 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) )) ”
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
|--
  “ (((Znth ((j + 1 ) - i ) totals 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth ((j + 1 ) - i ) totals 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) )) ”
).

Definition solver_safety_wit_16_split_goal_1 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
|--
  “ (((Znth ((j + 1 ) - i ) totals 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_16_split_goal_2 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "prefix" ) )) # Int64  |-> (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ))
|--
  “ ((INT64_MIN) <= ((Znth ((j + 1 ) - i ) totals 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) )) ”
.

Definition solver_safety_wit_17 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted i totals )) (PreH19 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (i * 10000 ))))),
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted i totals )) (PreH19 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (i * 10000 ))))),
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals 0) > answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted n_pre totals )) (PreH22 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "answer" ) )) # Int64  |-> (Znth k totals 0))
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals 0) <= answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted n_pre totals )) (PreH22 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "total" ) )) # Ptr  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) __default__Prod_Z_Z (PreH1 : (Permutation students sorted_2 )) (PreH2 : (CandidatesSorted sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw_sorted_2 0) = (fst ((Znth i_3 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw_sorted_2 0) = (snd ((Znth i_3 sorted_2 __default__Prod_Z_Z))))))) (PreH6 : (retval <> 0)) (PreH7 : (1 <= (Zlength (students)))) (PreH8 : ((Zlength (students)) <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (n_pre = (Zlength (students)))) (PreH13 : ((Zlength (raw)) = (2 * n_pre ))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z))))))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
  **  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (retval <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (CompetitionOuterState sorted 0 totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (0 * 10000 )))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full retval (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (retval: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) __default__Prod_Z_Z (PreH1 : (Permutation students sorted_2 )) (PreH2 : (CandidatesSorted sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH5 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw_sorted_2 0) = (fst ((Znth i_3 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw_sorted_2 0) = (snd ((Znth i_3 sorted_2 __default__Prod_Z_Z))))))) (PreH6 : (retval <> 0)) (PreH7 : (1 <= (Zlength (students)))) (PreH8 : ((Zlength (students)) <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (n_pre = (Zlength (students)))) (PreH13 : ((Zlength (raw)) = (2 * n_pre ))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z))))))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (1 <= (Zlength (sorted_2))) ”
  &&  “ ((Zlength (sorted_2)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (sorted_2)))) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (sorted_2))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (sorted_2)))) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (sorted_2)))) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (sorted_2))) ”
  &&  “ (CompetitionOuterState sorted 0 (repeat_Z (0) (((Zlength (sorted_2)) + 1 ))) ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= (Zlength (sorted_2)))) -> ((0 <= (Znth k_4 (repeat_Z (0) (((Zlength (sorted_2)) + 1 ))) 0)) /\ ((Znth k_4 (repeat_Z (0) (((Zlength (sorted_2)) + 1 ))) 0) <= (0 * 10000 )))) ”
  &&  emp
).

Definition solver_entail_wit_2 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> (((1 <= (fst ((Znth k_6 students __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_6 students __default__Prod_Z_Z)))) /\ ((snd ((Znth k_6 students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted_2 )) (PreH11 : (CandidatesSorted sorted_2 )) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH14 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < n_pre)) -> (((Znth (2 * k_7 ) raw_sorted_2 0) = (fst ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_7 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_7 sorted_2 __default__Prod_Z_Z))))))) (PreH15 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < n_pre)) -> (((1 <= (fst ((Znth k_8 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_8 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_8 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_8 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted_2 i totals_2 )) (PreH19 : forall (k_9: Z), (((0 <= k_9) /\ (k_9 <= n_pre)) -> ((0 <= (Znth k_9 totals_2 0)) /\ ((Znth k_9 totals_2 0) <= (i * 10000 ))))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
  **  (Int64Array.full total (n_pre + 1 ) totals_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (((-10000) * (i - i ) ) <= 0) ”
  &&  “ (0 <= (10000 * (i - i ) )) ”
  &&  “ (CompetitionInnerState sorted i i 0 totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (i * 10000 )))) ”
  &&  “ forall (k_5: Z), ((((i - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> (((1 <= (fst ((Znth k_6 students __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_6 students __default__Prod_Z_Z)))) /\ ((snd ((Znth k_6 students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted_2 )) (PreH11 : (CandidatesSorted sorted_2 )) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH14 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < n_pre)) -> (((Znth (2 * k_7 ) raw_sorted_2 0) = (fst ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_7 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_7 sorted_2 __default__Prod_Z_Z))))))) (PreH15 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < n_pre)) -> (((1 <= (fst ((Znth k_8 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_8 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_8 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_8 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted_2 i totals_2 )) (PreH19 : forall (k_9: Z), (((0 <= k_9) /\ (k_9 <= n_pre)) -> ((0 <= (Znth k_9 totals_2 0)) /\ ((Znth k_9 totals_2 0) <= (i * 10000 ))))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (students)))) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (i <= i) ”
  &&  “ (((-10000) * (i - i ) ) <= 0) ”
  &&  “ (0 <= (10000 * (i - i ) )) ”
  &&  “ (CompetitionInnerState sorted i i 0 totals_2 ) ”
  &&  “ forall (k_5: Z), ((((i - i ) < k_5) /\ (k_5 <= (Zlength (students)))) -> ((Znth k_5 totals_2 0) <= (i * 10000 ))) ”
  &&  emp
).

Definition solver_entail_wit_3_1 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted_2 0) = (Znth (2 * i ) raw_sorted_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted_2 )) (PreH13 : (CandidatesSorted sorted_2 )) (PreH14 : ((Zlength (sorted_2)) = n_pre)) (PreH15 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted_2 __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals_2 0) <= (i * 10000 )))),
  (Int64Array.full total (n_pre + 1 ) (replace_Znth (((j + 1 ) - i )) (((Znth ((j + 1 ) - i ) totals_2 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) )) (totals_2)) )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ (((-10000) * ((j + 1 ) - i ) ) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) )) ”
  &&  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) <= (10000 * ((j + 1 ) - i ) )) ”
  &&  “ (CompetitionInnerState sorted i (j + 1 ) (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= ((j + 1 ) * 10000 )))) ”
  &&  “ forall (k_5: Z), (((((j + 1 ) - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted_2 0) = (Znth (2 * i ) raw_sorted_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted_2 )) (PreH13 : (CandidatesSorted sorted_2 )) (PreH14 : ((Zlength (sorted_2)) = n_pre)) (PreH15 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted_2 __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals_2 0) <= (i * 10000 )))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (students)))) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (i <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (students))) ”
  &&  “ (((-10000) * ((j + 1 ) - i ) ) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) )) ”
  &&  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) <= (10000 * ((j + 1 ) - i ) )) ”
  &&  “ (CompetitionInnerState sorted i (j + 1 ) (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) (replace_Znth (((j + 1 ) - i )) (((Znth ((j + 1 ) - i ) totals_2 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) )) (totals_2)) ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= (Zlength (students)))) -> ((0 <= (Znth k_4 (replace_Znth (((j + 1 ) - i )) (((Znth ((j + 1 ) - i ) totals_2 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) )) (totals_2)) 0)) /\ ((Znth k_4 (replace_Znth (((j + 1 ) - i )) (((Znth ((j + 1 ) - i ) totals_2 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) )) (totals_2)) 0) <= ((j + 1 ) * 10000 )))) ”
  &&  “ forall (k_5: Z), (((((j + 1 ) - i ) < k_5) /\ (k_5 <= (Zlength (students)))) -> ((Znth k_5 (replace_Znth (((j + 1 ) - i )) (((Znth ((j + 1 ) - i ) totals_2 0) + (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) )) (totals_2)) 0) <= (i * 10000 ))) ”
  &&  emp
).

Definition solver_entail_wit_3_2 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) <= 0)) (PreH2 : ((Znth (2 * j ) raw_sorted_2 0) = (Znth (2 * i ) raw_sorted_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted_2 )) (PreH13 : (CandidatesSorted sorted_2 )) (PreH14 : ((Zlength (sorted_2)) = n_pre)) (PreH15 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted_2 __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals_2 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
  **  (Int64Array.full total (n_pre + 1 ) totals_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= n_pre) ”
  &&  “ (((-10000) * ((j + 1 ) - i ) ) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) )) ”
  &&  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) <= (10000 * ((j + 1 ) - i ) )) ”
  &&  “ (CompetitionInnerState sorted i (j + 1 ) (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= ((j + 1 ) * 10000 )))) ”
  &&  “ forall (k_5: Z), (((((j + 1 ) - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) <= 0)) (PreH2 : ((Znth (2 * j ) raw_sorted_2 0) = (Znth (2 * i ) raw_sorted_2 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted_2 )) (PreH13 : (CandidatesSorted sorted_2 )) (PreH14 : ((Zlength (sorted_2)) = n_pre)) (PreH15 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted_2 __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals_2 0) <= (i * 10000 )))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (students)))) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (i <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (students))) ”
  &&  “ (((-10000) * ((j + 1 ) - i ) ) <= (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) )) ”
  &&  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) <= (10000 * ((j + 1 ) - i ) )) ”
  &&  “ (CompetitionInnerState sorted i (j + 1 ) (prefix + (Znth ((2 * j ) + 1 ) raw_sorted_2 0) ) totals_2 ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= (Zlength (students)))) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= ((j + 1 ) * 10000 )))) ”
  &&  “ forall (k_5: Z), (((((j + 1 ) - i ) < k_5) /\ (k_5 <= (Zlength (students)))) -> ((Znth k_5 totals_2 0) <= (i * 10000 ))) ”
  &&  emp
).

Definition solver_entail_wit_4_1 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_pre)) -> (((1 <= (fst ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((fst ((Znth k_5 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((snd ((Znth k_5 students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted_2 )) (PreH11 : (CandidatesSorted sorted_2 )) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH14 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> (((Znth (2 * k_6 ) raw_sorted_2 0) = (fst ((Znth k_6 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_6 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_6 sorted_2 __default__Prod_Z_Z))))))) (PreH15 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < n_pre)) -> (((1 <= (fst ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH23 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 totals_2 0)) /\ ((Znth k_8 totals_2 0) <= (j * 10000 ))))) (PreH24 : forall (k_9: Z), ((((j - i ) < k_9) /\ (k_9 <= n_pre)) -> ((Znth k_9 totals_2 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
  **  (Int64Array.full total (n_pre + 1 ) totals_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (CompetitionOuterState sorted j totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_pre)) -> (((1 <= (fst ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((fst ((Znth k_5 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((snd ((Znth k_5 students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted_2 )) (PreH11 : (CandidatesSorted sorted_2 )) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH14 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> (((Znth (2 * k_6 ) raw_sorted_2 0) = (fst ((Znth k_6 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_6 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_6 sorted_2 __default__Prod_Z_Z))))))) (PreH15 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < n_pre)) -> (((1 <= (fst ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH23 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 totals_2 0)) /\ ((Znth k_8 totals_2 0) <= (j * 10000 ))))) (PreH24 : forall (k_9: Z), ((((j - i ) < k_9) /\ (k_9 <= n_pre)) -> ((Znth k_9 totals_2 0) <= (i * 10000 )))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (students)))) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= j) ”
  &&  “ (CompetitionOuterState sorted j totals_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_2 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted_2 0) <> (Znth (2 * i ) raw_sorted_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_pre)) -> (((1 <= (fst ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((fst ((Znth k_5 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((snd ((Znth k_5 students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted_2 )) (PreH12 : (CandidatesSorted sorted_2 )) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH15 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> (((Znth (2 * k_6 ) raw_sorted_2 0) = (fst ((Znth k_6 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_6 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_6 sorted_2 __default__Prod_Z_Z))))))) (PreH16 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < n_pre)) -> (((1 <= (fst ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH24 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 totals_2 0)) /\ ((Znth k_8 totals_2 0) <= (j * 10000 ))))) (PreH25 : forall (k_9: Z), ((((j - i ) < k_9) /\ (k_9 <= n_pre)) -> ((Znth k_9 totals_2 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
  **  (Int64Array.full total (n_pre + 1 ) totals_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (CompetitionOuterState sorted j totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted_2 0) <> (Znth (2 * i ) raw_sorted_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_pre)) -> (((1 <= (fst ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((fst ((Znth k_5 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_5 students __default__Prod_Z_Z)))) /\ ((snd ((Znth k_5 students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted_2 )) (PreH12 : (CandidatesSorted sorted_2 )) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH15 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> (((Znth (2 * k_6 ) raw_sorted_2 0) = (fst ((Znth k_6 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_6 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_6 sorted_2 __default__Prod_Z_Z))))))) (PreH16 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < n_pre)) -> (((1 <= (fst ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_7 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_7 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted_2 i j prefix totals_2 )) (PreH24 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 totals_2 0)) /\ ((Znth k_8 totals_2 0) <= (j * 10000 ))))) (PreH25 : forall (k_9: Z), ((((j - i ) < k_9) /\ (k_9 <= n_pre)) -> ((Znth k_9 totals_2 0) <= (i * 10000 )))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (students)))) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= j) ”
  &&  “ (CompetitionOuterState sorted j totals_2 ) ”
  &&  emp
).

Definition solver_entail_wit_5 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted_2 )) (PreH11 : (CandidatesSorted sorted_2 )) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted_2 __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted_2 i totals_2 )) (PreH19 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= (i * 10000 ))))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
  **  (Int64Array.full total (n_pre + 1 ) totals_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (n_pre * 10000 )) ”
  &&  “ (CompetitionOuterState sorted n_pre totals ) ”
  &&  “ (CompetitionAnswerPrefix totals n_pre (1 - 1 ) 0 ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 )))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (i: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted_2 )) (PreH11 : (CandidatesSorted sorted_2 )) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted_2 0) = (fst ((Znth k_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth k_2 sorted_2 __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (CompetitionOuterState sorted_2 i totals_2 )) (PreH19 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals_2 0)) /\ ((Znth k_4 totals_2 0) <= (i * 10000 ))))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (students)))) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= ((Zlength (students)) + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((Zlength (students)) * 10000 )) ”
  &&  “ (CompetitionOuterState sorted (Zlength (students)) totals_2 ) ”
  &&  “ (CompetitionAnswerPrefix totals_2 (Zlength (students)) (1 - 1 ) 0 ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= (Zlength (students)))) -> ((0 <= (Znth p_4 totals_2 0)) /\ ((Znth p_4 totals_2 0) <= ((Zlength (students)) * 10000 )))) ”
  &&  emp
).

Definition solver_entail_wit_6_1 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (answer: Z) (k: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals_2 0) > answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted_2 )) (PreH12 : (CandidatesSorted sorted_2 )) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted_2 __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted_2 n_pre totals_2 )) (PreH22 : (CompetitionAnswerPrefix totals_2 n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals_2 0)) /\ ((Znth p_4 totals_2 0) <= (n_pre * 10000 ))))),
  (Int64Array.full total (n_pre + 1 ) totals_2 )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= (Znth k totals_2 0)) ”
  &&  “ ((Znth k totals_2 0) <= (n_pre * 10000 )) ”
  &&  “ (CompetitionOuterState sorted n_pre totals ) ”
  &&  “ (CompetitionAnswerPrefix totals n_pre ((k + 1 ) - 1 ) (Znth k totals_2 0) ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 )))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (answer: Z) (k: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals_2 0) > answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted_2 )) (PreH12 : (CandidatesSorted sorted_2 )) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted_2 __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted_2 n_pre totals_2 )) (PreH22 : (CompetitionAnswerPrefix totals_2 n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals_2 0)) /\ ((Znth p_4 totals_2 0) <= (n_pre * 10000 ))))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (students)))) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= ((Zlength (students)) + 1 )) ”
  &&  “ (0 <= (Znth k totals_2 0)) ”
  &&  “ ((Znth k totals_2 0) <= ((Zlength (students)) * 10000 )) ”
  &&  “ (CompetitionOuterState sorted (Zlength (students)) totals_2 ) ”
  &&  “ (CompetitionAnswerPrefix totals_2 (Zlength (students)) ((k + 1 ) - 1 ) (Znth k totals_2 0) ) ”
  &&  emp
).

Definition solver_entail_wit_6_2 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (answer: Z) (k: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals_2 0) <= answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted_2 )) (PreH12 : (CandidatesSorted sorted_2 )) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted_2 __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted_2 n_pre totals_2 )) (PreH22 : (CompetitionAnswerPrefix totals_2 n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals_2 0)) /\ ((Znth p_4 totals_2 0) <= (n_pre * 10000 ))))),
  (Int64Array.full total (n_pre + 1 ) totals_2 )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted_2 )
|--
  EX (totals: (@list Z)) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))),
  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (n_pre * 10000 )) ”
  &&  “ (CompetitionOuterState sorted n_pre totals ) ”
  &&  “ (CompetitionAnswerPrefix totals n_pre ((k + 1 ) - 1 ) answer ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 )))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals_2: (@list Z)) (answer: Z) (k: Z) (raw_sorted_2: (@list Z)) (sorted_2: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals_2 0) <= answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted_2 )) (PreH12 : (CandidatesSorted sorted_2 )) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (raw_sorted_2)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted_2 __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted_2 __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted_2 __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted_2 __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted_2 n_pre totals_2 )) (PreH22 : (CompetitionAnswerPrefix totals_2 n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals_2 0)) /\ ((Znth p_4 totals_2 0) <= (n_pre * 10000 ))))),
  TT && emp 
|--
  EX (sorted: (@list (Z * Z))),
  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = (Zlength (students))) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (students)))) -> (((Znth (2 * p_2 ) raw_sorted_2 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted_2 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < (Zlength (students)))) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= ((Zlength (students)) + 1 )) ”
  &&  “ (CompetitionOuterState sorted (Zlength (students)) totals_2 ) ”
  &&  “ (CompetitionAnswerPrefix totals_2 (Zlength (students)) ((k + 1 ) - 1 ) answer ) ”
  &&  emp
).

Definition solver_return_wit_1 :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (k > n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (1 <= k)) (PreH17 : (k <= (n_pre + 1 ))) (PreH18 : (0 <= answer)) (PreH19 : (answer <= (n_pre * 10000 ))) (PreH20 : (CompetitionOuterState sorted n_pre totals )) (PreH21 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH22 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
|--
  EX (raw_after: (@list Z)) (students_after: (@list (Z * Z))),
  “ (Spec m_pre students answer ) ”
  &&  “ (Permutation students students_after ) ”
  &&  “ ((Zlength (raw_after)) = (2 * n_pre )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth (2 * i ) raw_after 0) = (fst ((Znth i students_after __default__Prod_Z_Z)))) /\ ((Znth ((2 * i ) + 1 ) raw_after 0) = (snd ((Znth i students_after __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw_after )
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (k > n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (1 <= k)) (PreH17 : (k <= (n_pre + 1 ))) (PreH18 : (0 <= answer)) (PreH19 : (answer <= (n_pre * 10000 ))) (PreH20 : (CompetitionOuterState sorted n_pre totals )) (PreH21 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH22 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  TT && emp 
|--
  EX (students_after: (@list (Z * Z))),
  “ (Spec m_pre students answer ) ”
  &&  “ (Permutation students students_after ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((Znth (2 * i ) raw_sorted 0) = (fst ((Znth i students_after __default__Prod_Z_Z)))) /\ ((Znth ((2 * i ) + 1 ) raw_sorted 0) = (snd ((Znth i students_after __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_partial_solve_wit_1_pure :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (students)))) (PreH2 : ((Zlength (students)) <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000))))) (PreH6 : (n_pre = (Zlength (students)))) (PreH7 : ((Zlength (raw)) = (2 * n_pre ))) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z))))))),
  ((( &( "total" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ (0 <= (n_pre + 1 )) ”
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ”
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (students)))) (PreH2 : ((Zlength (students)) <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000))))) (PreH6 : (n_pre = (Zlength (students)))) (PreH7 : ((Zlength (raw)) = (2 * n_pre ))) (PreH8 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z))))))),
  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ (0 <= (n_pre + 1 )) ”
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ”
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
  &&  “ (1 <= (Zlength (students))) ”
  &&  “ ((Zlength (students)) <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (students)))) -> (((1 <= (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((fst ((Znth i students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i students __default__Prod_Z_Z)))) /\ ((snd ((Znth i students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth (2 * i_2 ) raw 0) = (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_2 ) + 1 ) raw 0) = (snd ((Znth i_2 students __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (students)))) (PreH3 : ((Zlength (students)) <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (students)))) -> (((1 <= (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((snd ((Znth i_2 students __default__Prod_Z_Z))) <= 10000))))) (PreH7 : (n_pre = (Zlength (students)))) (PreH8 : ((Zlength (raw)) = (2 * n_pre ))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw 0) = (fst ((Znth i_3 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw 0) = (snd ((Znth i_3 students __default__Prod_Z_Z))))))),
  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "total" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth (2 * i ) raw 0) = (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i ) + 1 ) raw 0) = (snd ((Znth i students __default__Prod_Z_Z)))))) ”
) \/
(
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (m_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (m_pre >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (1 <= (Zlength (students)))) (PreH7 : ((Zlength (students)) <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (students)))) -> (((1 <= (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((snd ((Znth i_2 students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (n_pre = (Zlength (students)))) (PreH12 : ((Zlength (raw)) = (2 * n_pre ))) (PreH13 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw 0) = (fst ((Znth i_3 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw 0) = (snd ((Znth i_3 students __default__Prod_Z_Z))))))),
  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "total" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth (2 * i ) raw 0) = (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i ) + 1 ) raw 0) = (snd ((Znth i students __default__Prod_Z_Z)))))) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (m_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (m_pre >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (1 <= (Zlength (students)))) (PreH7 : ((Zlength (students)) <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (students)))) -> (((1 <= (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((snd ((Znth i_2 students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (n_pre = (Zlength (students)))) (PreH12 : ((Zlength (raw)) = (2 * n_pre ))) (PreH13 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw 0) = (fst ((Znth i_3 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw 0) = (snd ((Znth i_3 students __default__Prod_Z_Z))))))),
  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "total" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth (2 * i ) raw 0) = (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i ) + 1 ) raw 0) = (snd ((Znth i students __default__Prod_Z_Z)))))) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (students)))) (PreH3 : ((Zlength (students)) <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (students)))) -> (((1 <= (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((snd ((Znth i_2 students __default__Prod_Z_Z))) <= 10000))))) (PreH7 : (n_pre = (Zlength (students)))) (PreH8 : ((Zlength (raw)) = (2 * n_pre ))) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw 0) = (fst ((Znth i_3 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw 0) = (snd ((Znth i_3 students __default__Prod_Z_Z))))))),
  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  (IntArray.full a_pre (2 * n_pre ) raw )
|--
  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> (((Znth (2 * i ) raw 0) = (fst ((Znth i students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i ) + 1 ) raw 0) = (snd ((Znth i students __default__Prod_Z_Z)))))) ”
  &&  “ (retval <> 0) ”
  &&  “ (1 <= (Zlength (students))) ”
  &&  “ ((Zlength (students)) <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (students)))) -> (((1 <= (fst ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth i_2 students __default__Prod_Z_Z)))) /\ ((snd ((Znth i_2 students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (2 * i_3 ) raw 0) = (fst ((Znth i_3 students __default__Prod_Z_Z)))) /\ ((Znth ((2 * i_3 ) + 1 ) raw 0) = (snd ((Znth i_3 students __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full a_pre (2 * n_pre ) raw )
  **  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted i j prefix totals )) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH24 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (j < n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (((-10000) * (j - i ) ) <= prefix) ”
  &&  “ (prefix <= (10000 * (j - i ) )) ”
  &&  “ (CompetitionInnerState sorted i j prefix totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  “ forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (((a_pre + ((2 * j ) * sizeof(INT)))) # Int  |-> (Znth (2 * j ) raw_sorted 0))
  **  (IntArray.missing_i a_pre (2 * j ) 0 (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
.

Definition solver_partial_solve_wit_4 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (i <= j)) (PreH19 : (j <= n_pre)) (PreH20 : (((-10000) * (j - i ) ) <= prefix)) (PreH21 : (prefix <= (10000 * (j - i ) ))) (PreH22 : (CompetitionInnerState sorted i j prefix totals )) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH24 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (j < n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (((-10000) * (j - i ) ) <= prefix) ”
  &&  “ (prefix <= (10000 * (j - i ) )) ”
  &&  “ (CompetitionInnerState sorted i j prefix totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  “ forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (((a_pre + ((2 * i ) * sizeof(INT)))) # Int  |-> (Znth (2 * i ) raw_sorted 0))
  **  (IntArray.missing_i a_pre (2 * i ) 0 (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
.

Definition solver_partial_solve_wit_5 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH2 : (j < n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (i <= j)) (PreH20 : (j <= n_pre)) (PreH21 : (((-10000) * (j - i ) ) <= prefix)) (PreH22 : (prefix <= (10000 * (j - i ) ))) (PreH23 : (CompetitionInnerState sorted i j prefix totals )) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH25 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (((-10000) * (j - i ) ) <= prefix) ”
  &&  “ (prefix <= (10000 * (j - i ) )) ”
  &&  “ (CompetitionInnerState sorted i j prefix totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  “ forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (((a_pre + (((2 * j ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * j ) + 1 ) raw_sorted 0))
  **  (IntArray.missing_i a_pre ((2 * j ) + 1 ) 0 (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
.

Definition solver_partial_solve_wit_6 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0) ”
  &&  “ ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (((-10000) * (j - i ) ) <= prefix) ”
  &&  “ (prefix <= (10000 * (j - i ) )) ”
  &&  “ (CompetitionInnerState sorted i j prefix totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  “ forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (((total + (((j + 1 ) - i ) * sizeof(INT64)))) # Int64  |-> (Znth ((j + 1 ) - i ) totals 0))
  **  (Int64Array.missing_i total ((j + 1 ) - i ) 0 (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
.

Definition solver_partial_solve_wit_7 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (prefix: Z) (j: Z) (i: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0)) (PreH2 : ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0))) (PreH3 : (j < n_pre)) (PreH4 : (total <> 0)) (PreH5 : (n_pre = (Zlength (students)))) (PreH6 : ((Zlength (raw)) = (2 * n_pre ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000))))) (PreH12 : (Permutation students sorted )) (PreH13 : (CandidatesSorted sorted )) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z))))))) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <= j)) (PreH21 : (j <= n_pre)) (PreH22 : (((-10000) * (j - i ) ) <= prefix)) (PreH23 : (prefix <= (10000 * (j - i ) ))) (PreH24 : (CompetitionInnerState sorted i j prefix totals )) (PreH25 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 ))))) (PreH26 : forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 )))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
|--
  “ ((prefix + (Znth ((2 * j ) + 1 ) raw_sorted 0) ) > 0) ”
  &&  “ ((Znth (2 * j ) raw_sorted 0) = (Znth (2 * i ) raw_sorted 0)) ”
  &&  “ (j < n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> (((1 <= (fst ((Znth k students __default__Prod_Z_Z)))) /\ ((fst ((Znth k students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k students __default__Prod_Z_Z)))) /\ ((snd ((Znth k students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth (2 * k_2 ) raw_sorted 0) = (fst ((Znth k_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * k_2 ) + 1 ) raw_sorted 0) = (snd ((Znth k_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> (((1 <= (fst ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth k_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth k_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth k_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (i <= j) ”
  &&  “ (j <= n_pre) ”
  &&  “ (((-10000) * (j - i ) ) <= prefix) ”
  &&  “ (prefix <= (10000 * (j - i ) )) ”
  &&  “ (CompetitionInnerState sorted i j prefix totals ) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 totals 0)) /\ ((Znth k_4 totals 0) <= (j * 10000 )))) ”
  &&  “ forall (k_5: Z), ((((j - i ) < k_5) /\ (k_5 <= n_pre)) -> ((Znth k_5 totals 0) <= (i * 10000 ))) ”
  &&  (((total + (((j + 1 ) - i ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i total ((j + 1 ) - i ) 0 (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
.

Definition solver_partial_solve_wit_8 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (k <= n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (1 <= k)) (PreH17 : (k <= (n_pre + 1 ))) (PreH18 : (0 <= answer)) (PreH19 : (answer <= (n_pre * 10000 ))) (PreH20 : (CompetitionOuterState sorted n_pre totals )) (PreH21 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH22 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (k <= n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= (n_pre + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (n_pre * 10000 )) ”
  &&  “ (CompetitionOuterState sorted n_pre totals ) ”
  &&  “ (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 )))) ”
  &&  (((total + (k * sizeof(INT64)))) # Int64  |-> (Znth k totals 0))
  **  (Int64Array.missing_i total k 0 (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
.

Definition solver_partial_solve_wit_9 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : ((Znth k totals 0) > answer)) (PreH2 : (k <= n_pre)) (PreH3 : (total <> 0)) (PreH4 : (n_pre = (Zlength (students)))) (PreH5 : ((Zlength (raw)) = (2 * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100000)) (PreH10 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH11 : (Permutation students sorted )) (PreH12 : (CandidatesSorted sorted )) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH15 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH16 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH17 : (1 <= k)) (PreH18 : (k <= (n_pre + 1 ))) (PreH19 : (0 <= answer)) (PreH20 : (answer <= (n_pre * 10000 ))) (PreH21 : (CompetitionOuterState sorted n_pre totals )) (PreH22 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH23 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  (Int64Array.full total (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
|--
  “ ((Znth k totals 0) > answer) ”
  &&  “ (k <= n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= (n_pre + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (n_pre * 10000 )) ”
  &&  “ (CompetitionOuterState sorted n_pre totals ) ”
  &&  “ (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 )))) ”
  &&  (((total + (k * sizeof(INT64)))) # Int64  |-> (Znth k totals 0))
  **  (Int64Array.missing_i total k 0 (n_pre + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
.

Definition solver_partial_solve_wit_10 :=
forall (raw: (@list Z)) (students: (@list (Z * Z))) (a_pre: Z) (n_pre: Z) (m_pre: Z) (totals: (@list Z)) (answer: Z) (k: Z) (raw_sorted: (@list Z)) (sorted: (@list (Z * Z))) (total: Z) __default__Prod_Z_Z (PreH1 : (k > n_pre)) (PreH2 : (total <> 0)) (PreH3 : (n_pre = (Zlength (students)))) (PreH4 : ((Zlength (raw)) = (2 * n_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100000)) (PreH9 : forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000))))) (PreH10 : (Permutation students sorted )) (PreH11 : (CandidatesSorted sorted )) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (raw_sorted)) = (2 * n_pre ))) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z))))))) (PreH15 : forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000))))) (PreH16 : (1 <= k)) (PreH17 : (k <= (n_pre + 1 ))) (PreH18 : (0 <= answer)) (PreH19 : (answer <= (n_pre * 10000 ))) (PreH20 : (CompetitionOuterState sorted n_pre totals )) (PreH21 : (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer )) (PreH22 : forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 ))))),
  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
  **  (Int64Array.full total (n_pre + 1 ) totals )
|--
  “ (k > n_pre) ”
  &&  “ (total <> 0) ”
  &&  “ (n_pre = (Zlength (students))) ”
  &&  “ ((Zlength (raw)) = (2 * n_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100000) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < n_pre)) -> (((1 <= (fst ((Znth p students __default__Prod_Z_Z)))) /\ ((fst ((Znth p students __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p students __default__Prod_Z_Z)))) /\ ((snd ((Znth p students __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (Permutation students sorted ) ”
  &&  “ (CandidatesSorted sorted ) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ ((Zlength (raw_sorted)) = (2 * n_pre )) ”
  &&  “ forall (p_2: Z), (((0 <= p_2) /\ (p_2 < n_pre)) -> (((Znth (2 * p_2 ) raw_sorted 0) = (fst ((Znth p_2 sorted __default__Prod_Z_Z)))) /\ ((Znth ((2 * p_2 ) + 1 ) raw_sorted 0) = (snd ((Znth p_2 sorted __default__Prod_Z_Z)))))) ”
  &&  “ forall (p_3: Z), (((0 <= p_3) /\ (p_3 < n_pre)) -> (((1 <= (fst ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((fst ((Znth p_3 sorted __default__Prod_Z_Z))) <= m_pre)) /\ (((-10000) <= (snd ((Znth p_3 sorted __default__Prod_Z_Z)))) /\ ((snd ((Znth p_3 sorted __default__Prod_Z_Z))) <= 10000)))) ”
  &&  “ (1 <= k) ”
  &&  “ (k <= (n_pre + 1 )) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (n_pre * 10000 )) ”
  &&  “ (CompetitionOuterState sorted n_pre totals ) ”
  &&  “ (CompetitionAnswerPrefix totals n_pre (k - 1 ) answer ) ”
  &&  “ forall (p_4: Z), (((0 <= p_4) /\ (p_4 <= n_pre)) -> ((0 <= (Znth p_4 totals 0)) /\ ((Znth p_4 totals 0) <= (n_pre * 10000 )))) ”
  &&  (Int64Array.full total ((Zlength (students)) + 1 ) totals )
  **  (IntArray.full a_pre (2 * n_pre ) raw_sorted )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.

End VC_Correct.
