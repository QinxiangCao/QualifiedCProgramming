From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P036_1201C_maximum_median_lib.
Local Open Scope sac.

(*----- Function cost -----*)

Definition cost_safety_wit_1 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cost_safety_wit_2 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "need" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition cost_safety_wit_3 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "need" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cost_safety_wit_4 :=
(
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((need + (m_pre - (Znth i sorted 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (need + (m_pre - (Znth i sorted 0) ) )) ”
) \/
(
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((need + (m_pre - (Znth i sorted 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (need + (m_pre - (Znth i sorted 0) ) )) ”
).

Definition cost_safety_wit_4_split_goal_1 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((need + (m_pre - (Znth i sorted 0) ) ) <= INT64_MAX) ”
.

Definition cost_safety_wit_4_split_goal_2 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((INT64_MIN) <= (need + (m_pre - (Znth i sorted 0) ) )) ”
.

Definition cost_safety_wit_5 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((m_pre - (Znth i sorted 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (m_pre - (Znth i sorted 0) )) ”
.

Definition cost_safety_wit_6 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "need" ) )) # Int64  |-> (need + (m_pre - (Znth i sorted 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition cost_entail_wit_1 :=
(
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 2000000000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (0 <= (n_pre ÷ 2 )) ”
  &&  “ ((n_pre ÷ 2 ) <= (n_pre ÷ 2 )) ”
  &&  “ ((n_pre ÷ 2 ) <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (((n_pre ÷ 2 ) - (n_pre ÷ 2 ) ) * 2000000000 )) ”
  &&  “ (MedianCostPrefix sorted m_pre (n_pre ÷ 2 ) 0 ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  TT && emp 
|--
  “ (MedianCostPrefix sorted m_pre (n_pre ÷ 2 ) 0 ) ”
  &&  “ ((n_pre ÷ 2 ) <= n_pre) ”
  &&  “ (0 <= (n_pre ÷ 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_entail_wit_1_split_goal_1 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  (MedianCostPrefix sorted m_pre (n_pre ÷ 2 ) 0 )
.

Definition cost_entail_wit_1_split_goal_2 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  ((n_pre ÷ 2 ) <= n_pre)
.

Definition cost_entail_wit_1_split_goal_3 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  (0 <= (n_pre ÷ 2 ))
.

Definition cost_entail_wit_1_split_goal_4 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000)))),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))
.

Definition cost_entail_wit_2 :=
(
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 2000000000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((n_pre ÷ 2 ) <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (need + (m_pre - (Znth i sorted 0) ) )) ”
  &&  “ ((need + (m_pre - (Znth i sorted 0) ) ) <= (((i + 1 ) - (n_pre ÷ 2 ) ) * 2000000000 )) ”
  &&  “ (MedianCostPrefix sorted m_pre (i + 1 ) (need + (m_pre - (Znth i sorted 0) ) ) ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  TT && emp 
|--
  “ (MedianCostPrefix sorted m_pre (i + 1 ) (need + (m_pre - (Znth i sorted 0) ) ) ) ”
  &&  emp
).

Definition cost_entail_wit_2_split_goal_1 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (MedianCostPrefix sorted m_pre (i + 1 ) (need + (m_pre - (Znth i sorted 0) ) ) )
.

Definition cost_entail_wit_3_1 :=
(
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000000000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (mono_nondec sorted )) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : ((n_pre ÷ 2 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= need)) (PreH13 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH14 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 2000000000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (need = (MedianRaiseCost (sorted) (m_pre))) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000000000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (mono_nondec sorted )) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : ((n_pre ÷ 2 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= need)) (PreH13 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH14 : (MedianCostPrefix sorted m_pre i need )),
  TT && emp 
|--
  “ (need = (MedianRaiseCost (sorted) (m_pre))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_entail_wit_3_1_split_goal_1 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000000000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (mono_nondec sorted )) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : ((n_pre ÷ 2 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= need)) (PreH13 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH14 : (MedianCostPrefix sorted m_pre i need )),
  (need = (MedianRaiseCost (sorted) (m_pre)))
.

Definition cost_entail_wit_3_1_split_goal_2 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000000000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (mono_nondec sorted )) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : ((n_pre ÷ 2 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= need)) (PreH13 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH14 : (MedianCostPrefix sorted m_pre i need )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))
.

Definition cost_entail_wit_3_2 :=
(
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) >= m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 2000000000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (need = (MedianRaiseCost (sorted) (m_pre))) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) >= m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  TT && emp 
|--
  “ (need = (MedianRaiseCost (sorted) (m_pre))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  emp
).

Definition cost_entail_wit_3_2_split_goal_1 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) >= m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (need = (MedianRaiseCost (sorted) (m_pre)))
.

Definition cost_entail_wit_3_2_split_goal_2 :=
forall (sorted: (@list Z)) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) >= m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))
.

Definition cost_return_wit_1 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000000000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (mono_nondec sorted )) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH8 : (need = (MedianRaiseCost (sorted) (m_pre)))),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (need = (MedianRaiseCost (sorted) (m_pre))) ”
  &&  (IntArray.full a_pre n_pre sorted )
.

Definition cost_partial_solve_wit_1 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000000000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (mono_nondec sorted )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : ((n_pre ÷ 2 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= need)) (PreH13 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH14 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 2000000000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ ((n_pre ÷ 2 ) <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= need) ”
  &&  “ (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 )) ”
  &&  “ (MedianCostPrefix sorted m_pre i need ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
.

Definition cost_partial_solve_wit_2 :=
forall (sorted: (@list Z)) (a_pre: Z) (n_pre: Z) (m_pre: Z) (need: Z) (i: Z) (PreH1 : ((Znth i sorted 0) < m_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000000000)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (mono_nondec sorted )) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : ((n_pre ÷ 2 ) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= need)) (PreH14 : (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 ))) (PreH15 : (MedianCostPrefix sorted m_pre i need )),
  (IntArray.full a_pre n_pre sorted )
|--
  “ ((Znth i sorted 0) < m_pre) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 2000000000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ ((n_pre ÷ 2 ) <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= need) ”
  &&  “ (need <= ((i - (n_pre ÷ 2 ) ) * 2000000000 )) ”
  &&  “ (MedianCostPrefix sorted m_pre i need ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  ((( &( "hi" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre ÷ 2 ) sorted 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (2000000000 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 2000000000) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  ((( &( "lo" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  ((( &( "lo" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition solver_safety_wit_4_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((((hi - lo ) + 1 ) <> (INT64_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (((hi - lo ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((hi - lo ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (hi - lo )) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_10 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH12 : (Permutation values sorted )) (PreH13 : (mono_nondec sorted )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH12 : (Permutation values sorted )) (PreH13 : (mono_nondec sorted )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
).

Definition solver_safety_wit_10_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH12 : (Permutation values sorted )) (PreH13 : (mono_nondec sorted )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH12 : (Permutation values sorted )) (PreH13 : (mono_nondec sorted )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH12 : (Permutation values sorted )) (PreH13 : (mono_nondec sorted )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre k_pre values )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre l1 )
|--
  EX (sorted: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (Permutation values sorted ) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ (0 <= (n_pre ÷ 2 )) ”
  &&  “ ((n_pre ÷ 2 ) < n_pre) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre k_pre values )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ ((n_pre ÷ 2 ) < n_pre) ”
  &&  “ (0 <= (n_pre ÷ 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= 1000000000))) ”
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre k_pre values )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  ((n_pre ÷ 2 ) < n_pre)
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre k_pre values )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  (0 <= (n_pre ÷ 2 ))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre k_pre values )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= 1000000000)))
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (l1: (@list Z)) (PreH1 : (Permutation values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre k_pre values )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))),
  ((Zlength (l1)) = n_pre)
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  (IntArray.full a_pre n_pre sorted )
|--
  EX (sorted_2: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (sorted_2)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000))) ”
  &&  “ (Permutation values sorted_2 ) ”
  &&  “ (mono_nondec sorted_2 ) ”
  &&  “ (1 <= (Znth (n_pre ÷ 2 ) sorted 0)) ”
  &&  “ ((Znth (n_pre ÷ 2 ) sorted 0) <= 2000000000) ”
  &&  “ (2000000000 <= 2000000000) ”
  &&  “ (MedianSearchBounds values k_pre (Znth (n_pre ÷ 2 ) sorted 0) 2000000000 ) ”
  &&  (IntArray.full a_pre n_pre sorted_2 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  TT && emp 
|--
  “ (MedianSearchBounds values k_pre (Znth (n_pre ÷ 2 ) sorted 0) 2000000000 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  (MedianSearchBounds values k_pre (Znth (n_pre ÷ 2 ) sorted 0) 2000000000 )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < n_pre)) -> ((1 <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))
.

Definition solver_entail_wit_3_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval <= k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (Permutation values sorted ) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ”
  &&  “ (hi <= 2000000000) ”
  &&  “ (MedianSearchBounds values k_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval <= k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  TT && emp 
|--
  “ (MedianSearchBounds values k_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi ) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ”
  &&  “ (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval <= k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (MedianSearchBounds values k_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi )
.

Definition solver_entail_wit_3_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval <= k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi)
.

Definition solver_entail_wit_3_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval <= k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
.

Definition solver_entail_wit_3_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)),
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (Permutation values sorted ) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000000) ”
  &&  “ (MedianSearchBounds values k_pre lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  TT && emp 
|--
  “ (MedianSearchBounds values k_pre lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) ) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000000) ”
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (MedianSearchBounds values k_pre lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) )
.

Definition solver_entail_wit_3_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000000)
.

Definition solver_entail_wit_3_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted_2: (@list Z)) (retval: Z) (PreH1 : (retval > k_pre)) (PreH2 : (retval = (MedianRaiseCost (sorted_2) ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ))))) (PreH3 : (lo < hi)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre k_pre values )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_2 0)) /\ ((Znth j sorted_2 0) <= 1000000000)))) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (mono_nondec sorted_2 )) (PreH14 : (1 <= lo)) (PreH15 : (lo <= hi)) (PreH16 : (hi <= 2000000000)) (PreH17 : (MedianSearchBounds values k_pre lo hi )),
  (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ))
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo >= hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
|--
  EX (a_after: (@list Z)),
  “ (Spec k_pre values lo ) ”
  &&  “ (Permutation values a_after ) ”
  &&  (IntArray.full a_pre n_pre a_after )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo >= hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  TT && emp 
|--
  “ (Spec k_pre values lo ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo >= hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  (Spec k_pre values lo )
.

Definition solver_partial_solve_wit_1_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (sorted: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH9 : (Permutation values sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= (n_pre ÷ 2 ))) (PreH12 : ((n_pre ÷ 2 ) < n_pre)),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (Permutation values sorted ) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ (0 <= (n_pre ÷ 2 )) ”
  &&  “ ((n_pre ÷ 2 ) < n_pre) ”
  &&  (((a_pre + ((n_pre ÷ 2 ) * sizeof(INT)))) # Int  |-> (Znth (n_pre ÷ 2 ) sorted 0))
  **  (IntArray.missing_i a_pre (n_pre ÷ 2 ) 0 n_pre sorted )
.

Definition solver_partial_solve_wit_3_pure :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000))) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000000) ”
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH5 : (hi >= INT64_MIN)) (PreH6 : (lo >= INT64_MIN)) (PreH7 : (k_pre >= INT64_MIN)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (Pre k_pre values )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (n_pre = (Zlength (values)))) (PreH18 : ((Zlength (sorted)) = n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH20 : (Permutation values sorted )) (PreH21 : (mono_nondec sorted )) (PreH22 : (1 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 2000000000)) (PreH25 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000))) ”
).

Definition solver_partial_solve_wit_3_pure_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH5 : (hi >= INT64_MIN)) (PreH6 : (lo >= INT64_MIN)) (PreH7 : (k_pre >= INT64_MIN)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (Pre k_pre values )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (n_pre = (Zlength (values)))) (PreH18 : ((Zlength (sorted)) = n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH20 : (Permutation values sorted )) (PreH21 : (mono_nondec sorted )) (PreH22 : (1 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 2000000000)) (PreH25 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition solver_partial_solve_wit_3_pure_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH5 : (hi >= INT64_MIN)) (PreH6 : (lo >= INT64_MIN)) (PreH7 : (k_pre >= INT64_MIN)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (Pre k_pre values )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (n_pre = (Zlength (values)))) (PreH18 : ((Zlength (sorted)) = n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH20 : (Permutation values sorted )) (PreH21 : (mono_nondec sorted )) (PreH22 : (1 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 2000000000)) (PreH25 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000000) ”
.

Definition solver_partial_solve_wit_3_pure_split_goal_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH5 : (hi >= INT64_MIN)) (PreH6 : (lo >= INT64_MIN)) (PreH7 : (k_pre >= INT64_MIN)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (lo < hi)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (Pre k_pre values )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (n_pre = (Zlength (values)))) (PreH18 : ((Zlength (sorted)) = n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH20 : (Permutation values sorted )) (PreH21 : (mono_nondec sorted )) (PreH22 : (1 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 2000000000)) (PreH25 : (MedianSearchBounds values k_pre lo hi )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000))) ”
.

Definition solver_partial_solve_wit_3_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (k_pre: Z) (hi: Z) (lo: Z) (sorted: (@list Z)) (PreH1 : (lo < hi)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 1000000000)) (PreH4 : (Pre k_pre values )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000)))) (PreH10 : (Permutation values sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (1 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 2000000000)) (PreH15 : (MedianSearchBounds values k_pre lo hi )),
  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i sorted 0)) /\ ((Znth i sorted 0) <= 1000000000))) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000000) ”
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ (lo < hi) ”
  &&  “ (1 <= k_pre) ”
  &&  “ (k_pre <= 1000000000) ”
  &&  “ (Pre k_pre values ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ ((Zlength (sorted)) = n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted 0)) /\ ((Znth j sorted 0) <= 1000000000))) ”
  &&  “ (Permutation values sorted ) ”
  &&  “ (mono_nondec sorted ) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= hi) ”
  &&  “ (hi <= 2000000000) ”
  &&  “ (MedianSearchBounds values k_pre lo hi ) ”
  &&  (IntArray.full a_pre n_pre sorted )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Module Type VC_Correct.


Axiom proof_of_cost_safety_wit_1 : cost_safety_wit_1.
Axiom proof_of_cost_safety_wit_2 : cost_safety_wit_2.
Axiom proof_of_cost_safety_wit_3 : cost_safety_wit_3.
Axiom proof_of_cost_safety_wit_4 : cost_safety_wit_4.
Axiom proof_of_cost_safety_wit_5 : cost_safety_wit_5.
Axiom proof_of_cost_safety_wit_6 : cost_safety_wit_6.
Axiom proof_of_cost_entail_wit_1 : cost_entail_wit_1.
Axiom proof_of_cost_entail_wit_2 : cost_entail_wit_2.
Axiom proof_of_cost_entail_wit_3_1 : cost_entail_wit_3_1.
Axiom proof_of_cost_entail_wit_3_2 : cost_entail_wit_3_2.
Axiom proof_of_cost_return_wit_1 : cost_return_wit_1.
Axiom proof_of_cost_partial_solve_wit_1 : cost_partial_solve_wit_1.
Axiom proof_of_cost_partial_solve_wit_2 : cost_partial_solve_wit_2.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
