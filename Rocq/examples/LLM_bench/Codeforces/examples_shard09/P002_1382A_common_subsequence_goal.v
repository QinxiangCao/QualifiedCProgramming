From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH9 : (0 <= (1001 * sizeof(CHAR)))) (PreH10 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH9 : (0 <= (1001 * sizeof(CHAR)))) (PreH10 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval = (( &( "seen" ) ) + (0 * sizeof(CHAR))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= (1001 * sizeof(CHAR)))) (PreH11 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) (repeat_Z (0) ((1001 * sizeof(CHAR)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  (CharArray.full ( &( "seen" ) ) 1001 (replace_Znth ((Znth i left 0)) (1) (seen_l)) )
  **  (IntArray.full a_pre n_pre left )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full b_pre m_pre right )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  (IntArray.full a_pre n_pre left )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))) (PreH17 : ((Znth (Znth j right 0) seen_l 0) = 0)),
  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
  **  (IntArray.full b_pre m_pre right )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre left )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i left 0)) /\ ((Znth i left 0) <= 1000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))),
  (CharArray.undef_full ( &( "seen" ) ) 1001 )
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= (1001 * sizeof(CHAR))) ”
  &&  “ ((1001 * sizeof(CHAR)) < INT_MAX) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
) \/
(
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i left 0)) /\ ((Znth i left 0) <= 1000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))),
  (CharArray.undef_full ( &( "seen" ) ) 1001 )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i left 0)) /\ ((Znth i left 0) <= 1000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))),
  (CharArray.undef_full ( &( "seen" ) ) 1001 )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i left 0)) /\ ((Znth i left 0) <= 1000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))),
  (CharArray.undef_full ( &( "seen" ) ) 1001 )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i left 0)) /\ ((Znth i left 0) <= 1000)))) (PreH6 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))),
  (CharArray.undef_full ( &( "seen" ) ) 1001 )
|--
  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
.

Definition solver_entail_wit_2 :=
(
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (retval: Z) (k_4: Z) (PreH1 : (retval = (( &( "seen" ) ) + (0 * sizeof(CHAR))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 left 0)) /\ ((Znth k_5 left 0) <= 1000)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 right 0)) /\ ((Znth k_6 right 0) <= 1000)))) (PreH10 : (0 <= (1001 * sizeof(CHAR)))) (PreH11 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  (CharArray.full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) (repeat_Z (0) ((1001 * sizeof(CHAR)))) )
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
|--
  EX (seen_l: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < 0)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
) \/
(
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (retval: Z) (k_4: Z) (PreH1 : (retval = (( &( "seen" ) ) + (0 * sizeof(CHAR))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 left 0)) /\ ((Znth k_5 left 0) <= 1000)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 right 0)) /\ ((Znth k_6 right 0) <= 1000)))) (PreH10 : (0 <= (1001 * sizeof(CHAR)))) (PreH11 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  (CharArray.full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) (repeat_Z (0) ((1001 * sizeof(CHAR)))) )
|--
  EX (seen_l: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < 0)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
).

Definition solver_entail_wit_3 :=
(
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l_2 0) = 0) \/ ((Znth v seen_l_2 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l_2 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  (CharArray.full ( &( "seen" ) ) 1001 (replace_Znth ((Znth i left 0)) (1) (seen_l_2)) )
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
|--
  EX (seen_l: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < (i + 1 ))) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
) \/
(
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_4: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l_2 0) = 0) \/ ((Znth v seen_l_2 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l_2 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  TT && emp 
|--
  “ ((Zlength ((replace_Znth ((Znth i left 0)) (1) (seen_l_2)))) = 1001) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_4: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l_2 0) = 0) \/ ((Znth v seen_l_2 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l_2 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  ((Zlength ((replace_Znth ((Znth i left 0)) (1) (seen_l_2)))) = 1001)
.

Definition solver_entail_wit_4 :=
(
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (k_4: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l_2 )
|--
  EX (seen_l: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  “ forall (k_5: Z), (((0 <= k_5) /\ (k_5 < 0)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0)) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
) \/
(
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (k_4: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  TT && emp 
|--
  “ forall (k_5: Z), (((0 <= k_5) /\ (k_5 < 0)) -> ((Znth (Znth k_5 right 0) seen_l_2 0) = 0)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l_2 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l_2 0) = 1)) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l_2 0) = 0) \/ ((Znth v seen_l_2 0) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  forall (k_5: Z), (((0 <= k_5) /\ (k_5 < 0)) -> ((Znth (Znth k_5 right 0) seen_l_2 0) = 0))
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (k_4: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l_2 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l_2 0) = 1))
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l_2 0) = 0) \/ ((Znth v seen_l_2 0) = 1)))
.

Definition solver_entail_wit_4_split_goal_5 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))
.

Definition solver_entail_wit_4_split_goal_6 :=
forall (right: (@list Z)) (left: (@list Z)) (n_pre: Z) (m_pre: Z) (k_9: Z) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left 0)) /\ ((Znth k_6 left 0) <= 1000)))) (PreH9 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right 0)) /\ ((Znth k_7 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3: Z), (((0 <= v_3) /\ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 0) = 0) \/ ((Znth v_3 seen_l_2 0) = 1)))) (PreH14 : forall (k_8: Z), (((0 <= k_8) /\ (k_8 < i)) -> ((Znth (Znth k_8 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_4: Z), ((((0 <= v_4) /\ (v_4 < 1001)) /\ ((Znth v_4 seen_l_2 0) = 1)) -> exists (k_9: Z), (((0 <= k_9) /\ (k_9 < i)) /\ ((Znth k_9 left 0) = v_4)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))
.

Definition solver_entail_wit_5 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l_2: (@list Z)) (j: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l_2 0) = 0) \/ ((Znth v seen_l_2 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l_2 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l_2 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l_2 0) = 0))) (PreH17 : ((Znth (Znth j right 0) seen_l_2 0) = 0)),
  (CharArray.full ( &( "seen" ) ) 1001 seen_l_2 )
  **  (IntArray.full b_pre m_pre right )
  **  (IntArray.full a_pre n_pre left )
|--
  EX (seen_l: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= m_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  “ forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (j + 1 ))) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0)) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
.

Definition solver_return_wit_1 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))),
  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
|--
  (EX (out: (@option (@list Z))),
  “ (Spec left right out ) ”
  &&  “ (out = None) ”
  &&  “ (0 = 0) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right ))
  ||
  (EX (out: (@option (@list Z))),
  “ (Spec left right out ) ”
  &&  “ (out = (Some ((cons (0) ((@nil Z)))))) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right ))
.

Definition solver_return_wit_2 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))) (PreH17 : ((Znth (Znth j right 0) seen_l 0) <> 0)),
  (IntArray.full b_pre m_pre right )
  **  (IntArray.full a_pre n_pre left )
|--
  (EX (out: (@option (@list Z))),
  “ (Spec left right out ) ”
  &&  “ (out = None) ”
  &&  “ ((Znth j right 0) = 0) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right ))
  ||
  (EX (out: (@option (@list Z))),
  “ (Spec left right out ) ”
  &&  “ (out = (Some ((cons ((Znth j right 0)) ((@nil Z)))))) ”
  &&  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right ))
.

Definition solver_partial_solve_wit_1_pure :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH9 : (0 <= (1001 * sizeof(CHAR)))) (PreH10 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
|--
  “ (0 <= (1001 * sizeof(CHAR))) ”
  &&  “ ((1001 * sizeof(CHAR)) < INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 127) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH9 : (0 <= (1001 * sizeof(CHAR)))) (PreH10 : ((1001 * sizeof(CHAR)) < INT_MAX)),
  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
|--
  “ (0 <= (1001 * sizeof(CHAR))) ”
  &&  “ ((1001 * sizeof(CHAR)) < INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 127) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= (1001 * sizeof(CHAR))) ”
  &&  “ ((1001 * sizeof(CHAR)) < INT_MAX) ”
  &&  (CharArray.undef_full (( &( "seen" ) ) + (0 * sizeof(CHAR))) (1001 * sizeof(CHAR)) )
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i left 0))
  **  (IntArray.missing_i a_pre i 0 n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
.

Definition solver_partial_solve_wit_3 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2)))),
  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  (((( &( "seen" ) ) + ((Znth i left 0) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i ( &( "seen" ) ) (Znth i left 0) 0 1001 seen_l )
  **  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
.

Definition solver_partial_solve_wit_4 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))),
  (IntArray.full a_pre n_pre left )
  **  (IntArray.full b_pre m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (j < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= m_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  “ forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0)) ”
  &&  (((b_pre + (j * sizeof(INT)))) # Int  |-> (Znth j right 0))
  **  (IntArray.missing_i b_pre j 0 m_pre right )
  **  (IntArray.full a_pre n_pre left )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
.

Definition solver_partial_solve_wit_5 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))),
  (IntArray.full b_pre m_pre right )
  **  (IntArray.full a_pre n_pre left )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
|--
  “ (j < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= m_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  “ forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0)) ”
  &&  (((( &( "seen" ) ) + ((Znth j right 0) * sizeof(CHAR)))) # Char  |-> (Znth (Znth j right 0) seen_l 0))
  **  (CharArray.missing_i ( &( "seen" ) ) (Znth j right 0) 0 1001 seen_l )
  **  (IntArray.full b_pre m_pre right )
  **  (IntArray.full a_pre n_pre left )
.

Definition solver_partial_solve_wit_6 :=
forall (right: (@list Z)) (left: (@list Z)) (a_pre: Z) (n_pre: Z) (b_pre: Z) (m_pre: Z) (k_4: Z) (seen_l: (@list Z)) (j: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000)))) (PreH10 : (0 <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1)))) (PreH14 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1))) (PreH15 : forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2)))) (PreH16 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0))) (PreH17 : ((Znth (Znth j right 0) seen_l 0) <> 0)),
  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
  **  (IntArray.full b_pre m_pre right )
  **  (IntArray.full a_pre n_pre left )
|--
  “ (j < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (left))) ”
  &&  “ (m_pre = (Zlength (right))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k left 0)) /\ ((Znth k left 0) <= 1000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right 0)) /\ ((Znth k_2 right 0) <= 1000))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= m_pre) ”
  &&  “ ((Zlength (seen_l)) = 1001) ”
  &&  “ forall (v: Z), (((0 <= v) /\ (v < 1001)) -> (((Znth v seen_l 0) = 0) \/ ((Znth v seen_l 0) = 1))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (Znth k_3 left 0) seen_l 0) = 1)) ”
  &&  “ forall (v_2: Z), ((((0 <= v_2) /\ (v_2 < 1001)) /\ ((Znth v_2 seen_l 0) = 1)) -> exists (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) /\ ((Znth k_4 left 0) = v_2))) ”
  &&  “ forall (k_5: Z), (((0 <= k_5) /\ (k_5 < j)) -> ((Znth (Znth k_5 right 0) seen_l 0) = 0)) ”
  &&  “ ((Znth (Znth j right 0) seen_l 0) <> 0) ”
  &&  (((b_pre + (j * sizeof(INT)))) # Int  |-> (Znth j right 0))
  **  (IntArray.missing_i b_pre j 0 m_pre right )
  **  (CharArray.full ( &( "seen" ) ) 1001 seen_l )
  **  (IntArray.full a_pre n_pre left )
.

Module Type VC_Correct.

Include string_Strategy_Correct.

Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.

End VC_Correct.
