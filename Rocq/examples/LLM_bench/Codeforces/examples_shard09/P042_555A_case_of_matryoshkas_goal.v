Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P042_555A_case_of_matryoshkas_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  ((( &( "ops" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ops" ) )) # Int64  |-> (ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ops" ) )) # Int64  |-> ops)
|--
  “ ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) )) ”
.

Definition solver_safety_wit_5 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ops" ) )) # Int64  |-> ops)
|--
  “ (((Znth i (ChainLengths (chains)) 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (ChainLengths (chains)) 0) - 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ops" ) )) # Int64  |-> ops)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "ops" ) )) # Int64  |-> ops)
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ ((ops - (p_pre - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ops - (p_pre - 1 ) )) ”
.

Definition solver_safety_wit_8 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "ops" ) )) # Int64  |-> ops)
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ ((p_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p_pre - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "ops" ) )) # Int64  |-> ops)
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "ops" ) )) # Int64  |-> (ops - (p_pre - 1 ) ))
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (((ops - (p_pre - 1 ) ) + (n_pre - p_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((ops - (p_pre - 1 ) ) + (n_pre - p_pre ) )) ”
.

Definition solver_safety_wit_11 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "ops" ) )) # Int64  |-> (ops - (p_pre - 1 ) ))
  **  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ ((n_pre - p_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - p_pre )) ”
.

Definition solver_entail_wit_1 := 
(
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (Pre n_pre chains ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre))) ” 
  &&  “ (k_pre = (Zlength (chains))) ” 
  &&  “ (p_pre = (usable_prefix (chains))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= p_pre) ” 
  &&  “ (p_pre <= n_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (PrefixExtractionCost (chains) (0))) ”
  &&  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  TT && emp 
|--
  “ (0 = (PrefixExtractionCost (chains) (0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre))) ” 
  &&  “ (p_pre <= n_pre) ” 
  &&  “ (1 <= p_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  (0 = (PrefixExtractionCost (chains) (0)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  (p_pre <= n_pre)
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  (1 <= p_pre)
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  (k_pre <= n_pre)
.

Definition solver_entail_wit_1_split_goal_6 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < k_pre)) -> ((1 <= (Znth i (ChainLengths (chains)) 0)) /\ ((Znth i (ChainLengths (chains)) 0) <= n_pre)))) (PreH6 : (Pre n_pre chains )) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 (concat (chains)) 0)) /\ ((Znth i_2 (concat (chains)) 0) <= n_pre)))) (PreH8 : (k_pre = (Zlength (chains)))) (PreH9 : (p_pre = (usable_prefix (chains)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))
.

Definition solver_entail_wit_2 := 
(
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (Pre n_pre chains ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre))) ” 
  &&  “ (k_pre = (Zlength (chains))) ” 
  &&  “ (p_pre = (usable_prefix (chains))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= p_pre) ” 
  &&  “ (p_pre <= n_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ (0 <= (ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) )) ” 
  &&  “ ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) <= n_pre) ” 
  &&  “ ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) = (PrefixExtractionCost (chains) ((i + 1 )))) ”
  &&  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  TT && emp 
|--
  “ ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) = (PrefixExtractionCost (chains) ((i + 1 )))) ” 
  &&  “ ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) <= n_pre) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) = (PrefixExtractionCost (chains) ((i + 1 ))))
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  ((ops + ((Znth i (ChainLengths (chains)) 0) - 1 ) ) <= n_pre)
.

Definition solver_entail_wit_3 := 
(
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (Spec n_pre chains ((ops - (p_pre - 1 ) ) + (n_pre - p_pre ) ) ) ”
  &&  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  TT && emp 
|--
  “ (Spec n_pre chains ((ops - (p_pre - 1 ) ) + (n_pre - p_pre ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (Spec n_pre chains ((ops - (p_pre - 1 ) ) + (n_pre - p_pre ) ) )
.

Definition solver_return_wit_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (PreH1 : (Spec n_pre chains ops )) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (Spec n_pre chains ops ) ”
  &&  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
.

Definition solver_partial_solve_wit_1 := 
forall (p_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (chains: (@list (@list Z))) (ops: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (Pre n_pre chains )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre)))) (PreH6 : (k_pre = (Zlength (chains)))) (PreH7 : (p_pre = (usable_prefix (chains)))) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= n_pre)) (PreH10 : (1 <= p_pre)) (PreH11 : (p_pre <= n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= ops)) (PreH16 : (ops <= n_pre)) (PreH17 : (ops = (PrefixExtractionCost (chains) (i)))) ,
  (IntArray.full m_pre k_pre (ChainLengths (chains)) )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (Pre n_pre chains ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j (concat (chains)) 0)) /\ ((Znth j (concat (chains)) 0) <= n_pre))) ” 
  &&  “ (k_pre = (Zlength (chains))) ” 
  &&  “ (p_pre = (usable_prefix (chains))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= p_pre) ” 
  &&  “ (p_pre <= n_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < k_pre)) -> ((1 <= (Znth j_2 (ChainLengths (chains)) 0)) /\ ((Znth j_2 (ChainLengths (chains)) 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (0 <= ops) ” 
  &&  “ (ops <= n_pre) ” 
  &&  “ (ops = (PrefixExtractionCost (chains) (i))) ”
  &&  (((m_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (ChainLengths (chains)) 0))
  **  (IntArray.missing_i m_pre i 0 k_pre (ChainLengths (chains)) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
