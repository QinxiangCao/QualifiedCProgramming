From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P039_1955D_inaccurate_subsequence_search_lib.
Local Open Scope sac.

(*----- Function minimum -----*)

Definition minimum_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre < b_pre)),
  TT && emp 
|--
  “ (a_pre = (z_min (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre < b_pre)),
  TT && emp 
|--
  “ (a_pre = (z_min (a_pre) (b_pre))) ”
  &&  emp
).

Definition minimum_return_wit_1_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre < b_pre)),
  (a_pre = (z_min (a_pre) (b_pre)))
.

Definition minimum_return_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)),
  TT && emp 
|--
  “ (b_pre = (z_min (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)),
  TT && emp 
|--
  “ (b_pre = (z_min (a_pre) (b_pre))) ”
  &&  emp
).

Definition minimum_return_wit_2_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)),
  (b_pre = (z_min (a_pre) (b_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (b_data)))) (PreH3 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (m_pre = (Zlength (b_data)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 (repeat_Z (0) (1000001)) )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (((Znth (Znth i b_data 0) need_data 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth i b_data 0) need_data 0) + 1 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (((Znth (Znth i b_data 0) need_data 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth i b_data 0) need_data 0) + 1 )) ”
).

Definition solver_safety_wit_2_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (((Znth (Znth i b_data 0) need_data 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_2_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ ((INT_MIN) <= ((Znth (Znth i b_data 0) need_data 0) + 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full ( &( "need" ) ) 1000001 (replace_Znth ((Znth i b_data 0)) (((Znth (Znth i b_data 0) need_data 0) + 1 )) (need_data)) )
  **  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "matched" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  ((( &( "matched" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "matched" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((matched - retval ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (matched - retval )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((matched - retval ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (matched - retval )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((matched - retval ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= (matched - retval )) ”
.

Definition solver_safety_wit_8 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth i values 0) have_data 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth i values 0) have_data 0) + 1 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth i values 0) have_data 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth i values 0) have_data 0) + 1 )) ”
).

Definition solver_safety_wit_8_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth i values 0) have_data 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_8_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= ((Znth (Znth i values 0) have_data 0) + 1 )) ”
.

Definition solver_safety_wit_9 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((matched - retval ) + retval_2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((matched - retval ) + retval_2 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((matched - retval ) + retval_2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((matched - retval ) + retval_2 )) ”
).

Definition solver_safety_wit_9_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((matched - retval ) + retval_2 ) <= INT_MAX) ”
.

Definition solver_safety_wit_9_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= ((matched - retval ) + retval_2 )) ”
.

Definition solver_safety_wit_10 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((matched - retval ) + retval_2 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ ((answer + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (answer + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ ((i - m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - m_pre )) ”
.

Definition solver_safety_wit_13 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((matched - retval ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (matched - retval )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((matched - retval ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (matched - retval )) ”
).

Definition solver_safety_wit_13_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((matched - retval ) <= INT_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= (matched - retval )) ”
.

Definition solver_safety_wit_14 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) ”
).

Definition solver_safety_wit_14_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_14_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= ((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) ”
.

Definition solver_safety_wit_15 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((matched - retval ) + retval_2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((matched - retval ) + retval_2 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((matched - retval ) + retval_2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((matched - retval ) + retval_2 )) ”
).

Definition solver_safety_wit_15_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((matched - retval ) + retval_2 ) <= INT_MAX) ”
.

Definition solver_safety_wit_15_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - m_pre ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (matched - retval ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= ((matched - retval ) + retval_2 )) ”
.

Definition solver_safety_wit_16 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((matched - retval ) + retval_2 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((((matched - retval ) + retval_2 ) - retval_3 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((matched - retval ) + retval_2 ) - retval_3 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((matched - retval ) + retval_2 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((((matched - retval ) + retval_2 ) - retval_3 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((matched - retval ) + retval_2 ) - retval_3 )) ”
).

Definition solver_safety_wit_16_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((matched - retval ) + retval_2 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((((matched - retval ) + retval_2 ) - retval_3 ) <= INT_MAX) ”
.

Definition solver_safety_wit_16_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((matched - retval ) + retval_2 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= (((matched - retval ) + retval_2 ) - retval_3 )) ”
.

Definition solver_safety_wit_17 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ”
).

Definition solver_safety_wit_17_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ”
.

Definition solver_safety_wit_18 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= (Zlength (b_data)))) (PreH8 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH9 : ((Zlength (values)) <= 200000)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (m_pre = (Zlength (b_data)))) (PreH14 : (m_pre <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= matched)) (PreH17 : (matched <= m_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= ((i - m_pre ) + 1 ))) (PreH20 : (FrequencyTable b_data need_data )) (PreH21 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH22 : (TableMatchScore need_data have_data matched )) (PreH23 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 )) ”
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= (Zlength (b_data)))) (PreH8 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH9 : ((Zlength (values)) <= 200000)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (m_pre = (Zlength (b_data)))) (PreH14 : (m_pre <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= matched)) (PreH17 : (matched <= m_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= ((i - m_pre ) + 1 ))) (PreH20 : (FrequencyTable b_data need_data )) (PreH21 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH22 : (TableMatchScore need_data have_data matched )) (PreH23 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 )) ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= (Zlength (b_data)))) (PreH8 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH9 : ((Zlength (values)) <= 200000)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (m_pre = (Zlength (b_data)))) (PreH14 : (m_pre <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= matched)) (PreH17 : (matched <= m_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= ((i - m_pre ) + 1 ))) (PreH20 : (FrequencyTable b_data need_data )) (PreH21 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH22 : (TableMatchScore need_data have_data matched )) (PreH23 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= INT_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= (Zlength (b_data)))) (PreH8 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH9 : ((Zlength (values)) <= 200000)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH11 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (m_pre = (Zlength (b_data)))) (PreH14 : (m_pre <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= matched)) (PreH17 : (matched <= m_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= ((i - m_pre ) + 1 ))) (PreH20 : (FrequencyTable b_data need_data )) (PreH21 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH22 : (TableMatchScore need_data have_data matched )) (PreH23 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> (((matched - retval ) + retval_2 ) - retval_3 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((INT_MIN) <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 )) ”
.

Definition solver_safety_wit_19 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH23 : (TableMatchScore need_data have_data matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((answer + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (answer + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH23 : (TableMatchScore need_data have_data matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ))
  **  ((( &( "answer" ) )) # Int  |-> (answer + 1 ))
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH23 : (TableMatchScore need_data have_data matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ))
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (0) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_26 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_27 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 (replace_Znth ((Znth i b_data 0)) (0) (need_data)) )
  **  (IntArray.full b_pre m_pre b_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "matched" ) )) # Int  |-> matched)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (b_data)))) (PreH3 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (m_pre = (Zlength (b_data)))),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 (repeat_Z (0) (1000001)) )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  EX (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (FrequencyTable (sublist (0) (0) (b_data)) need_data ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (b_data)))) (PreH3 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (m_pre = (Zlength (b_data)))),
  TT && emp 
|--
  “ (FrequencyTable (sublist (0) (0) (b_data)) (repeat_Z (0) (1000001)) ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (b_data)))) (PreH3 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (m_pre = (Zlength (b_data)))),
  (FrequencyTable (sublist (0) (0) (b_data)) (repeat_Z (0) (1000001)) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (b_data)))) (PreH3 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (m_pre = (Zlength (b_data)))),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= (Zlength (b_data)))) (PreH3 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000)))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (m_pre = (Zlength (b_data)))),
  forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))
.

Definition solver_entail_wit_2 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  (IntArray.full ( &( "need" ) ) 1000001 (replace_Znth ((Znth i b_data 0)) (((Znth (Znth i b_data 0) need_data_2 0) + 1 )) (need_data_2)) )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  EX (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (FrequencyTable (sublist (0) ((i + 1 )) (b_data)) need_data ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  TT && emp 
|--
  “ (FrequencyTable (sublist (0) ((i + 1 )) (b_data)) (replace_Znth ((Znth i b_data 0)) (((Znth (Znth i b_data 0) need_data_2 0) + 1 )) (need_data_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  (FrequencyTable (sublist (0) ((i + 1 )) (b_data)) (replace_Znth ((Znth i b_data 0)) (((Znth (Znth i b_data 0) need_data_2 0) + 1 )) (need_data_2)) )
.

Definition solver_entail_wit_3 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  EX (have_data: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (0) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  TT && emp 
|--
  “ (TableMatchScore need_data_2 (repeat_Z (0) (1000001)) 0 ) ”
  &&  “ (FrequencyTable (sublist (0) (0) (values)) (repeat_Z (0) (1000001)) ) ”
  &&  “ (FrequencyTable b_data need_data_2 ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  (TableMatchScore need_data_2 (repeat_Z (0) (1000001)) 0 )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  (FrequencyTable (sublist (0) (0) (values)) (repeat_Z (0) (1000001)) )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  (FrequencyTable b_data need_data_2 )
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))
.

Definition solver_entail_wit_3_split_goal_5 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data_2 )),
  forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))
.

Definition solver_entail_wit_4 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data_2 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data_2 )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH19 : (TableMatchScore need_data_2 have_data_2 matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  EX (have_data: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (0 <= ((matched - retval ) + retval_2 )) ”
  &&  “ (((matched - retval ) + retval_2 ) <= (i + 1 )) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) ((i + 1 )) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data ((matched - retval ) + retval_2 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data_2 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data_2 )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH19 : (TableMatchScore need_data_2 have_data_2 matched )),
  TT && emp 
|--
  “ (TableMatchScore need_data_2 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) ((matched - retval ) + retval_2 ) ) ”
  &&  “ (FrequencyTable (sublist (0) ((i + 1 )) (values)) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) ) ”
  &&  “ (((matched - retval ) + retval_2 ) <= (i + 1 )) ”
  &&  “ (0 <= ((matched - retval ) + retval_2 )) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data_2 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data_2 )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH19 : (TableMatchScore need_data_2 have_data_2 matched )),
  (TableMatchScore need_data_2 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) ((matched - retval ) + retval_2 ) )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data_2 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data_2 )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH19 : (TableMatchScore need_data_2 have_data_2 matched )),
  (FrequencyTable (sublist (0) ((i + 1 )) (values)) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) )
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data_2 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data_2 )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH19 : (TableMatchScore need_data_2 have_data_2 matched )),
  (((matched - retval ) + retval_2 ) <= (i + 1 ))
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data_2 0) + 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH2 : (retval = (z_min ((Znth (Znth i values 0) have_data_2 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (i < m_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= i)) (PreH16 : (answer = 0)) (PreH17 : (FrequencyTable b_data need_data_2 )) (PreH18 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH19 : (TableMatchScore need_data_2 have_data_2 matched )),
  (0 <= ((matched - retval ) + retval_2 ))
.

Definition solver_entail_wit_5_1 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data_2 )
|--
  EX (have_data: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= (answer + 1 )) ”
  &&  “ ((answer + 1 ) <= ((m_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((m_pre - m_pre )) (m_pre) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((m_pre - m_pre ) + 1 ) (answer + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  TT && emp 
|--
  “ (CountedGoodWindows k_pre values b_data ((m_pre - m_pre ) + 1 ) (0 + 1 ) ) ”
  &&  “ (FrequencyTable (sublist ((m_pre - m_pre )) (m_pre) (values)) have_data_2 ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  (CountedGoodWindows k_pre values b_data ((m_pre - m_pre ) + 1 ) (0 + 1 ) )
.

Definition solver_entail_wit_5_1_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  (FrequencyTable (sublist ((m_pre - m_pre )) (m_pre) (values)) have_data_2 )
.

Definition solver_entail_wit_5_1_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))
.

Definition solver_entail_wit_5_1_split_goal_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched >= k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))
.

Definition solver_entail_wit_5_2 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched < k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data_2 )
|--
  EX (have_data: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= m_pre) ”
  &&  “ (m_pre <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((m_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((m_pre - m_pre )) (m_pre) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((m_pre - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched < k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  TT && emp 
|--
  “ (CountedGoodWindows k_pre values b_data ((m_pre - m_pre ) + 1 ) 0 ) ”
  &&  “ (FrequencyTable (sublist ((m_pre - m_pre )) (m_pre) (values)) have_data_2 ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched < k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  (CountedGoodWindows k_pre values b_data ((m_pre - m_pre ) + 1 ) 0 )
.

Definition solver_entail_wit_5_2_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched < k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  (FrequencyTable (sublist ((m_pre - m_pre )) (m_pre) (values)) have_data_2 )
.

Definition solver_entail_wit_5_2_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched < k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))
.

Definition solver_entail_wit_5_2_split_goal_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (matched < k_pre)) (PreH2 : (i >= m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH8 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )),
  forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))
.

Definition solver_entail_wit_6_1 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  EX (have_data: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 )) ”
  &&  “ (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= m_pre) ”
  &&  “ (0 <= (answer + 1 )) ”
  &&  “ ((answer + 1 ) <= (((i + 1 ) - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (((i + 1 ) - m_pre )) ((i + 1 )) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) ) ”
  &&  “ (CountedGoodWindows k_pre values b_data (((i + 1 ) - m_pre ) + 1 ) (answer + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  “ (CountedGoodWindows k_pre values b_data (((i + 1 ) - m_pre ) + 1 ) (answer + 1 ) ) ”
  &&  “ (TableMatchScore need_data_2 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) ) ”
  &&  “ (FrequencyTable (sublist (((i + 1 ) - m_pre )) ((i + 1 )) (values)) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) ) ”
  &&  “ (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= m_pre) ”
  &&  emp
).

Definition solver_entail_wit_6_1_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (CountedGoodWindows k_pre values b_data (((i + 1 ) - m_pre ) + 1 ) (answer + 1 ) )
.

Definition solver_entail_wit_6_1_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (TableMatchScore need_data_2 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) )
.

Definition solver_entail_wit_6_1_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (FrequencyTable (sublist (((i + 1 ) - m_pre )) ((i + 1 )) (values)) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) )
.

Definition solver_entail_wit_6_1_split_goal_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) >= k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= m_pre)
.

Definition solver_entail_wit_6_2 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  EX (have_data: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 )) ”
  &&  “ (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= (((i + 1 ) - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (((i + 1 ) - m_pre )) ((i + 1 )) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) ) ”
  &&  “ (CountedGoodWindows k_pre values b_data (((i + 1 ) - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  “ (CountedGoodWindows k_pre values b_data (((i + 1 ) - m_pre ) + 1 ) answer ) ”
  &&  “ (TableMatchScore need_data_2 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) ) ”
  &&  “ (FrequencyTable (sublist (((i + 1 ) - m_pre )) ((i + 1 )) (values)) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) ) ”
  &&  “ (0 <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 )) ”
  &&  emp
).

Definition solver_entail_wit_6_2_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (CountedGoodWindows k_pre values b_data (((i + 1 ) - m_pre ) + 1 ) answer )
.

Definition solver_entail_wit_6_2_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (TableMatchScore need_data_2 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) )
.

Definition solver_entail_wit_6_2_split_goal_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (FrequencyTable (sublist (((i + 1 ) - m_pre )) ((i + 1 )) (values)) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) )
.

Definition solver_entail_wit_6_2_split_goal_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ) < k_pre)) (PreH2 : (retval_4 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)))) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH3 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth i values 0) need_data_2 0))))) (PreH4 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data_2 0) - 1 )) (have_data_2)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH5 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data_2 0)) ((Znth (Znth (i - m_pre ) values 0) need_data_2 0))))) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= (Zlength (b_data)))) (PreH9 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH10 : ((Zlength (values)) <= 200000)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH12 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (m_pre = (Zlength (b_data)))) (PreH15 : (m_pre <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= matched)) (PreH18 : (matched <= m_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= ((i - m_pre ) + 1 ))) (PreH21 : (FrequencyTable b_data need_data_2 )) (PreH22 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH23 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH24 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (0 <= ((((matched - retval ) + retval_2 ) - retval_3 ) + retval_4 ))
.

Definition solver_entail_wit_7 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data_2 )
|--
  EX (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have ) ”
  &&  “ (ClearedByPrefix original_have values 0 have_data ) ”
  &&  “ (TableMatchScore need_data original_have matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data_2 )) (PreH18 : (TableMatchScore need_data_2 have_data_2 matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  EX (original_have: (@list Z)),
  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (values))) ”
  &&  “ (answer <= (((Zlength (values)) - (Zlength (b_data)) ) + 1 )) ”
  &&  “ (FrequencyTable (sublist (((Zlength (values)) - (Zlength (b_data)) )) ((Zlength (values))) (values)) original_have ) ”
  &&  “ (ClearedByPrefix original_have values 0 have_data_2 ) ”
  &&  “ (TableMatchScore need_data_2 original_have matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data (((Zlength (values)) - (Zlength (b_data)) ) + 1 ) answer ) ”
  &&  emp
).

Definition solver_entail_wit_8 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (original_have_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have_2 )) (PreH18 : (ClearedByPrefix original_have_2 values i have_data_2 )) (PreH19 : (TableMatchScore need_data_2 original_have_2 matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (0) (have_data_2)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
|--
  EX (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have ) ”
  &&  “ (ClearedByPrefix original_have values (i + 1 ) have_data ) ”
  &&  “ (TableMatchScore need_data original_have matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data_2: (@list Z)) (original_have_2: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have_2 )) (PreH18 : (ClearedByPrefix original_have_2 values i have_data_2 )) (PreH19 : (TableMatchScore need_data_2 original_have_2 matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  EX (original_have: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (values))) ”
  &&  “ (FrequencyTable (sublist (((Zlength (values)) - (Zlength (b_data)) )) ((Zlength (values))) (values)) original_have ) ”
  &&  “ (ClearedByPrefix original_have values (i + 1 ) (replace_Znth ((Znth i values 0)) (0) (have_data_2)) ) ”
  &&  “ (TableMatchScore need_data_2 original_have matched ) ”
  &&  emp
).

Definition solver_entail_wit_9 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data_2 original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data_2 )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  EX (need_data: (@list Z)) (original_need: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data original_need ) ”
  &&  “ (ClearedByPrefix original_need b_data 0 need_data ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < (Zlength (values)))) -> ((1 <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000)))) (PreH7 : forall (j_4: Z), (((0 <= j_4) /\ (j_4 < (Zlength (b_data)))) -> ((1 <= (Znth j_4 b_data 0)) /\ ((Znth j_4 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data_2 )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data_2 original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  EX (original_need: (@list Z)),
  “ (have_data = (repeat_Z (0) (1000001))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (b_data))) ”
  &&  “ (FrequencyTable b_data original_need ) ”
  &&  “ (ClearedByPrefix original_need b_data 0 need_data_2 ) ”
  &&  emp
).

Definition solver_entail_wit_10 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (original_need_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need_2 )) (PreH17 : (ClearedByPrefix original_need_2 b_data i need_data_2 )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 (replace_Znth ((Znth i b_data 0)) (0) (need_data_2)) )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  EX (need_data: (@list Z)) (original_need: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data original_need ) ”
  &&  “ (ClearedByPrefix original_need b_data (i + 1 ) need_data ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data_2: (@list Z)) (original_need_2: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need_2 )) (PreH17 : (ClearedByPrefix original_need_2 b_data i need_data_2 )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  EX (original_need: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (b_data))) ”
  &&  “ (FrequencyTable b_data original_need ) ”
  &&  “ (ClearedByPrefix original_need b_data (i + 1 ) (replace_Znth ((Znth i b_data 0)) (0) (need_data_2)) ) ”
  &&  emp
).

Definition solver_return_wit_1 :=
(
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (Spec k_pre values b_data answer ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 (repeat_Z (0) (1000001)) )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
) \/
(
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  TT && emp 
|--
  “ (Spec k_pre values b_data answer ) ”
  &&  “ (need_data = (repeat_Z (0) (1000001))) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (Spec k_pre values b_data answer )
.

Definition solver_return_wit_1_split_goal_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (n_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (need_data = (repeat_Z (0) (1000001)))
.

Definition solver_partial_solve_wit_1 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (FrequencyTable (sublist (0) (i) (b_data)) need_data ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i b_data 0))
  **  (IntArray.missing_i b_pre i 0 m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
.

Definition solver_partial_solve_wit_2 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (FrequencyTable (sublist (0) (i) (b_data)) need_data ) ”
  &&  (((( &( "need" ) ) + ((Znth i b_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i b_data 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i b_data 0) 0 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
.

Definition solver_partial_solve_wit_3 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (FrequencyTable (sublist (0) (i) (b_data)) need_data )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (FrequencyTable (sublist (0) (i) (b_data)) need_data ) ”
  &&  (((( &( "need" ) ) + ((Znth i b_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i b_data 0) 0 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
.

Definition solver_partial_solve_wit_4 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= i)) (PreH14 : (answer = 0)) (PreH15 : (FrequencyTable b_data need_data )) (PreH16 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH17 : (TableMatchScore need_data have_data matched )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
.

Definition solver_partial_solve_wit_5 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= i)) (PreH14 : (answer = 0)) (PreH15 : (FrequencyTable b_data need_data )) (PreH16 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH17 : (TableMatchScore need_data have_data matched )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) have_data 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
.

Definition solver_partial_solve_wit_6 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= i)) (PreH14 : (answer = 0)) (PreH15 : (FrequencyTable b_data need_data )) (PreH16 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH17 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((( &( "need" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i values 0) 0 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_7 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= i)) (PreH14 : (answer = 0)) (PreH15 : (FrequencyTable b_data need_data )) (PreH16 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH17 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_8 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) have_data 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_9 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_10 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_11 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (((( &( "need" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i values 0) 0 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_12 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (i < m_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= i)) (PreH15 : (answer = 0)) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist (0) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth i values 0) have_data 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= i) ”
  &&  “ (answer = 0) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist (0) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) have_data 0) + 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_13 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((a_pre + ((i - m_pre ) * sizeof(INT)))) # Int  |-> (Znth (i - m_pre ) values 0))
  **  (IntArray.missing_i a_pre (i - m_pre ) 0 n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
.

Definition solver_partial_solve_wit_14 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth (i - m_pre ) values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (i - m_pre ) values 0) have_data 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth (i - m_pre ) values 0) 0 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
.

Definition solver_partial_solve_wit_15 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "need" ) ) + ((Znth (i - m_pre ) values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (i - m_pre ) values 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth (i - m_pre ) values 0) 0 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_16 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (m_pre <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((i - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH18 : (TableMatchScore need_data have_data matched )) (PreH19 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_17 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth (i - m_pre ) values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (i - m_pre ) values 0) have_data 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth (i - m_pre ) values 0) 0 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_18 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth (i - m_pre ) values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "have" ) ) (Znth (i - m_pre ) values 0) 0 1000001 have_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_19 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth (i - m_pre ) values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth (i - m_pre ) values 0) 0 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_20 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "need" ) ) + ((Znth (i - m_pre ) values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (i - m_pre ) values 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth (i - m_pre ) values 0) 0 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_21 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (PreH1 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= (Zlength (b_data)))) (PreH5 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (m_pre = (Zlength (b_data)))) (PreH11 : (m_pre <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= matched)) (PreH14 : (matched <= m_pre)) (PreH15 : (0 <= answer)) (PreH16 : (answer <= ((i - m_pre ) + 1 ))) (PreH17 : (FrequencyTable b_data need_data )) (PreH18 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH19 : (TableMatchScore need_data have_data matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_22 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_23 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_24 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "need" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i values 0) 0 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_25 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH2 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= (Zlength (b_data)))) (PreH6 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 200000)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH10 : (n_pre = (Zlength (values)))) (PreH11 : (m_pre = (Zlength (b_data)))) (PreH12 : (m_pre <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= matched)) (PreH15 : (matched <= m_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= ((i - m_pre ) + 1 ))) (PreH18 : (FrequencyTable b_data need_data )) (PreH19 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH20 : (TableMatchScore need_data have_data matched )) (PreH21 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_26 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_27 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_28 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) 0))
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_29 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "need" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) need_data 0))
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i values 0) 0 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_30 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0))))) (PreH2 : (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH3 : (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0))))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= (Zlength (b_data)))) (PreH7 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 200000)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (m_pre = (Zlength (b_data)))) (PreH13 : (m_pre <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= matched)) (PreH16 : (matched <= m_pre)) (PreH17 : (0 <= answer)) (PreH18 : (answer <= ((i - m_pre ) + 1 ))) (PreH19 : (FrequencyTable b_data need_data )) (PreH20 : (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data )) (PreH21 : (TableMatchScore need_data have_data matched )) (PreH22 : (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer )),
  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
|--
  “ (retval_3 = (z_min ((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth i values 0) need_data 0)))) ”
  &&  “ (retval_2 = (z_min ((Znth (Znth (i - m_pre ) values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (retval = (z_min ((Znth (Znth (i - m_pre ) values 0) have_data 0)) ((Znth (Znth (i - m_pre ) values 0) need_data 0)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (m_pre <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((i - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((i - m_pre )) (i) (values)) have_data ) ”
  &&  “ (TableMatchScore need_data have_data matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((i - m_pre ) + 1 ) answer ) ”
  &&  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) (replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)) 0) + 1 )) ((replace_Znth ((Znth (i - m_pre ) values 0)) (((Znth (Znth (i - m_pre ) values 0) have_data 0) - 1 )) (have_data)))) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
.

Definition solver_partial_solve_wit_31 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have ) ”
  &&  “ (ClearedByPrefix original_have values i have_data ) ”
  &&  “ (TableMatchScore need_data original_have matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
.

Definition solver_partial_solve_wit_32 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (have_data: (@list Z)) (original_have: (@list Z)) (need_data: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data need_data )) (PreH17 : (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have )) (PreH18 : (ClearedByPrefix original_have values i have_data )) (PreH19 : (TableMatchScore need_data original_have matched )) (PreH20 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 have_data )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data need_data ) ”
  &&  “ (FrequencyTable (sublist ((n_pre - m_pre )) (n_pre) (values)) original_have ) ”
  &&  “ (ClearedByPrefix original_have values i have_data ) ”
  &&  “ (TableMatchScore need_data original_have matched ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "have" ) ) + ((Znth i values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "have" ) ) (Znth i values 0) 0 1000001 have_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
.

Definition solver_partial_solve_wit_33 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data original_need ) ”
  &&  “ (ClearedByPrefix original_need b_data i need_data ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i b_data 0))
  **  (IntArray.missing_i b_pre i 0 m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
.

Definition solver_partial_solve_wit_34 :=
forall (b_data: (@list Z)) (values: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_pre: Z) (need_data: (@list Z)) (original_need: (@list Z)) (answer: Z) (matched: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= (Zlength (b_data)))) (PreH4 : ((Zlength (b_data)) <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000)))) (PreH7 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000)))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (m_pre = (Zlength (b_data)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= matched)) (PreH13 : (matched <= m_pre)) (PreH14 : (0 <= answer)) (PreH15 : (answer <= ((n_pre - m_pre ) + 1 ))) (PreH16 : (FrequencyTable b_data original_need )) (PreH17 : (ClearedByPrefix original_need b_data i need_data )) (PreH18 : (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer )),
  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "need" ) ) 1000001 need_data )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= (Zlength (b_data))) ”
  &&  “ ((Zlength (b_data)) <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (values)))) -> ((1 <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000))) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (b_data)))) -> ((1 <= (Znth j_2 b_data 0)) /\ ((Znth j_2 b_data 0) <= 1000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (m_pre = (Zlength (b_data))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ (0 <= matched) ”
  &&  “ (matched <= m_pre) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= ((n_pre - m_pre ) + 1 )) ”
  &&  “ (FrequencyTable b_data original_need ) ”
  &&  “ (ClearedByPrefix original_need b_data i need_data ) ”
  &&  “ (CountedGoodWindows k_pre values b_data ((n_pre - m_pre ) + 1 ) answer ) ”
  &&  (((( &( "need" ) ) + ((Znth i b_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "need" ) ) (Znth i b_data 0) 0 1000001 need_data )
  **  (IntArray.full b_pre m_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "have" ) ) 1000001 (repeat_Z (0) (1000001)) )
.

Module Type VC_Correct.


Axiom proof_of_minimum_return_wit_1 : minimum_return_wit_1.
Axiom proof_of_minimum_return_wit_2 : minimum_return_wit_2.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
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
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.

End VC_Correct.
