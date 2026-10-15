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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P031_1311C_perform_the_combo_lib.
Local Open Scope sac.

(*----- Function memset -----*)

Definition memset_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (c_pre = 0)) (PreH3 : (aligned_4 dst_pre )) ,
  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # UInt  |-> n_pre)
  **  (UCharArray.undef_full dst_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memset_entail_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (c_pre = 0)) (PreH3 : (aligned_4 dst_pre )) ,
  (UCharArray.undef_full dst_pre n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (c_pre = 0) ” 
  &&  “ (aligned_4 dst_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UCharArray.full dst_pre 0 (repeat_Z (0) (0)) )
  **  (UCharArray.undef_seg dst_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (c_pre = 0)) (PreH3 : (aligned_4 dst_pre )) ,
  TT && emp 
|--
  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
  &&  emp
).

Definition memset_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (c_pre = 0)) (PreH3 : (aligned_4 dst_pre )) ,
  ((repeat_Z (0) (0)) = (@nil Z))
.

Definition memset_entail_wit_2 := 
(
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (UCharArray.full dst_pre (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (c_pre) ((@nil Z))))) )
  **  (UCharArray.undef_seg dst_pre (i + 1 ) n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (c_pre = 0) ” 
  &&  “ (aligned_4 dst_pre ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (UCharArray.full dst_pre (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (UCharArray.undef_seg dst_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
  &&  emp
).

Definition memset_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 ))))
.

Definition memset_return_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (UCharArray.full dst_pre i (repeat_Z (0) (i)) )
  **  (UCharArray.undef_seg dst_pre i n_pre )
|--
  “ (dst_pre = dst_pre) ” 
  &&  “ (aligned_4 dst_pre ) ”
  &&  (UCharArray.full dst_pre n_pre (repeat_Z (0) (n_pre)) )
) \/
(
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (UCharArray.full dst_pre i (repeat_Z (0) (i)) )
|--
  (UCharArray.full dst_pre n_pre (repeat_Z (0) (n_pre)) )
).

Definition memset_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (UCharArray.full dst_pre i (repeat_Z (0) (i)) )
|--
  (UCharArray.full dst_pre n_pre (repeat_Z (0) (n_pre)) )
.

Definition memset_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (dst_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (c_pre = 0)) (PreH4 : (aligned_4 dst_pre )) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (UCharArray.full dst_pre i (repeat_Z (0) (i)) )
  **  (UCharArray.undef_seg dst_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (c_pre = 0) ” 
  &&  “ (aligned_4 dst_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dst_pre + (i * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.undef_seg dst_pre (i + 1 ) n_pre )
  **  (UCharArray.full dst_pre i (repeat_Z (0) (i)) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_2 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (((Znth 0 diff_l 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth 0 diff_l 0) + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 )) ”
) \/
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 )) ”
).

Definition solver_safety_wit_10_split_goal_1 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ ((INT64_MIN) <= ((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth ((Znth i tries 0)) (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0) - 1 )) ((replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)))) )
  **  (IntArray.full p_pre m_pre tries )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (((Znth 0 diff_l 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth 0 diff_l 0) + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l )) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l )) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition solver_safety_wit_19 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l )) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  ((( &( "cover" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 (repeat_Z (0) (26)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l )) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cover" ) )) # Int64  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 (repeat_Z (0) (26)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cover" ) )) # Int64  |-> cover)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full cnt_pre 26 out )
|--
  “ ((cover + (Znth j diff_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (cover + (Znth j diff_l 0) )) ”
.

Definition solver_safety_wit_22 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cover" ) )) # Int64  |-> cover)
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
|--
  “ (((Znth j text 0) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j text 0) - 97 )) ”
.

Definition solver_safety_wit_23 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cover" ) )) # Int64  |-> cover)
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_24 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (Int64Array.full cnt_pre 26 out )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cover" ) )) # Int64  |-> cover)
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (((Znth ((Znth j text 0) - 97 ) out 0) + cover ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((Znth j text 0) - 97 ) out 0) + cover )) ”
.

Definition solver_safety_wit_25 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (Int64Array.full cnt_pre 26 (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out 0) + cover )) (out)) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cover" ) )) # Int64  |-> cover)
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 tries 0)) /\ ((Znth i_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.undef_full ( &( "diff" ) ) (n_pre + 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 tries 0)) /\ ((Znth i_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) ,
  (Int64Array.undef_full ( &( "diff" ) ) (n_pre + 1 ) )
|--
  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 tries 0)) /\ ((Znth i_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) ,
  (Int64Array.undef_full ( &( "diff" ) ) (n_pre + 1 ) )
|--
  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 tries 0)) /\ ((Znth i_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) ,
  (Int64Array.undef_full ( &( "diff" ) ) (n_pre + 1 ) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ”
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 tries 0)) /\ ((Znth i_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) ,
  (Int64Array.undef_full ( &( "diff" ) ) (n_pre + 1 ) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((1 <= (Znth i_2 tries 0)) /\ ((Znth i_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) ,
  (Int64Array.undef_full ( &( "diff" ) ) (n_pre + 1 ) )
|--
  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
.

Definition solver_entail_wit_2 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "diff" ) ) + (0 * sizeof(INT64))))) (PreH2 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 122)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((1 <= (Znth k_4 tries 0)) /\ ((Znth k_4 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (UCharArray.full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT64) * (n_pre + 1 ) ))) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "diff" ) ) + (0 * sizeof(INT64))))) (PreH2 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 122)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((1 <= (Znth k_4 tries 0)) /\ ((Znth k_4 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (UCharArray.full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT64) * (n_pre + 1 ) ))) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "diff" ) ) + (0 * sizeof(INT64))))) (PreH2 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 122)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((1 <= (Znth k_4 tries 0)) /\ ((Znth k_4 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (UCharArray.full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT64) * (n_pre + 1 ) ))) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ”
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "diff" ) ) + (0 * sizeof(INT64))))) (PreH2 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 122)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((1 <= (Znth k_4 tries 0)) /\ ((Znth k_4 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (UCharArray.full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT64) * (n_pre + 1 ) ))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
.

Definition solver_entail_wit_2_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "diff" ) ) + (0 * sizeof(INT64))))) (PreH2 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((97 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 122)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((1 <= (Znth k_4 tries 0)) /\ ((Znth k_4 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (UCharArray.full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT64) * (n_pre + 1 ) ))) )
|--
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
.

Definition solver_entail_wit_3 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
|--
  EX (diff_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre 0 diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-0) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= 0))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  TT && emp 
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-0) <= (Znth k_3 (repeat_Z (0) ((n_pre + 1 ))) 0)) /\ ((Znth k_3 (repeat_Z (0) ((n_pre + 1 ))) 0) <= 0))) ” 
  &&  “ (DifferencePrefix tries n_pre 0 (repeat_Z (0) ((n_pre + 1 ))) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-0) <= (Znth k_3 (repeat_Z (0) ((n_pre + 1 ))) 0)) /\ ((Znth k_3 (repeat_Z (0) ((n_pre + 1 ))) 0) <= 0)))
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (DifferencePrefix tries n_pre 0 (repeat_Z (0) ((n_pre + 1 ))) )
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))
.

Definition solver_entail_wit_3_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))
.

Definition solver_entail_wit_4 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth ((Znth i tries 0)) (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0) - 1 )) ((replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)))) )
  **  (IntArray.full p_pre m_pre tries )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  EX (diff_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre (i + 1 ) diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-(i + 1 )) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (i + 1 )))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= i)))) ,
  TT && emp 
|--
  “ (DifferencePrefix tries n_pre (i + 1 ) (replace_Znth ((Znth i tries 0)) (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0) - 1 )) ((replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= i)))) ,
  (DifferencePrefix tries n_pre (i + 1 ) (replace_Znth ((Znth i tries 0)) (((Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0) - 1 )) ((replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)))) )
.

Definition solver_entail_wit_5 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  EX (diff_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (aligned_4 cnt_pre ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
) \/
(
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (aligned_4 cnt_pre ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0)) /\ ((Znth k_3 (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0) <= (m_pre + 1 )))) ” 
  &&  “ (DifferenceReady tries n_pre (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (aligned_4 cnt_pre ) ”
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0)) /\ ((Znth k_3 (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) 0) <= (m_pre + 1 )))) ”
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (DifferenceReady tries n_pre (replace_Znth (0) (((Znth 0 diff_l_2 0) + 1 )) (diff_l_2)) ) ”
.

Definition solver_entail_wit_5_split_goal_4 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ”
.

Definition solver_entail_wit_5_split_goal_5 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
.

Definition solver_entail_wit_5_split_goal_spatial := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l_2 )) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-i) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= i)))) ,
  (Int64Array.undef_full cnt_pre 26 )
|--
  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
.

Definition solver_entail_wit_6 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (aligned_4 cnt_pre )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH8 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (aligned_4 cnt_pre )) ,
  (UCharArray.full cnt_pre (sizeof(INT64) * 26 ) (repeat_Z (0) ((sizeof(INT64) * 26 ))) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l_2 )
|--
  EX (diff_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (aligned_4 cnt_pre ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 (repeat_Z (0) (26)) )
) \/
(
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (aligned_4 cnt_pre )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH8 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (aligned_4 cnt_pre )) ,
  (UCharArray.full cnt_pre (sizeof(INT64) * 26 ) (repeat_Z (0) ((sizeof(INT64) * 26 ))) )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  (Int64Array.full cnt_pre 26 (repeat_Z (0) (26)) )
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (aligned_4 cnt_pre )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH8 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (aligned_4 cnt_pre )) ,
  (UCharArray.full cnt_pre (sizeof(INT64) * 26 ) (repeat_Z (0) ((sizeof(INT64) * 26 ))) )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 )))) ”
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (aligned_4 cnt_pre )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH8 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (aligned_4 cnt_pre )) ,
  (UCharArray.full cnt_pre (sizeof(INT64) * 26 ) (repeat_Z (0) ((sizeof(INT64) * 26 ))) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ”
.

Definition solver_entail_wit_6_split_goal_3 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (aligned_4 cnt_pre )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH8 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (aligned_4 cnt_pre )) ,
  (UCharArray.full cnt_pre (sizeof(INT64) * 26 ) (repeat_Z (0) ((sizeof(INT64) * 26 ))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
.

Definition solver_entail_wit_6_split_goal_spatial := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (aligned_4 cnt_pre )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((97 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 122)))) (PreH8 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m_pre)) -> ((1 <= (Znth k_5 tries 0)) /\ ((Znth k_5 tries 0) < n_pre)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (m_pre = (Zlength (tries)))) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_6 diff_l_2 0)) /\ ((Znth k_6 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (aligned_4 cnt_pre )) ,
  (UCharArray.full cnt_pre (sizeof(INT64) * 26 ) (repeat_Z (0) ((sizeof(INT64) * 26 ))) )
|--
  (Int64Array.full cnt_pre 26 (repeat_Z (0) (26)) )
.

Definition solver_entail_wit_7 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l_2 )
  **  (Int64Array.full cnt_pre 26 (repeat_Z (0) (26)) )
|--
  EX (out: (@list Z))  (diff_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (diff_l))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries 0 out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (0 * (m_pre + 1 ) )))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
) \/
(
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 (repeat_Z (0) (26)) 0)) /\ ((Znth k_4 (repeat_Z (0) (26)) 0) <= (0 * (m_pre + 1 ) )))) ” 
  &&  “ (PartialSpec text tries 0 (repeat_Z (0) (26)) ) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (diff_l_2))))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 (repeat_Z (0) (26)) 0)) /\ ((Znth k_4 (repeat_Z (0) (26)) 0) <= (0 * (m_pre + 1 ) ))))
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  (PartialSpec text tries 0 (repeat_Z (0) (26)) )
.

Definition solver_entail_wit_7_split_goal_3 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  (0 = (sum ((sublist (0) (0) (diff_l_2)))))
.

Definition solver_entail_wit_7_split_goal_4 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 ))))
.

Definition solver_entail_wit_7_split_goal_5 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))
.

Definition solver_entail_wit_7_split_goal_6 := 
forall (cnt_pre: Z) (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l_2 )) (PreH10 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))
.

Definition solver_entail_wit_8 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full cnt_pre 26 out_2 )
|--
  EX (out: (@list Z))  (diff_l_2: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l_2 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 )))) ” 
  &&  “ ((cover + (Znth j diff_l 0) ) = (sum ((sublist (0) ((j + 1 )) (diff_l_2))))) ” 
  &&  “ (0 <= (cover + (Znth j diff_l 0) )) ” 
  &&  “ ((cover + (Znth j diff_l 0) ) <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries j out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) )))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l_2 )
  **  (Int64Array.full cnt_pre 26 out )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out_2 0)) /\ ((Znth k_4 out_2 0) <= (j * (m_pre + 1 ) )))) ” 
  &&  “ ((cover + (Znth j diff_l 0) ) <= (m_pre + 1 )) ” 
  &&  “ (0 <= (cover + (Znth j diff_l 0) )) ” 
  &&  “ ((cover + (Znth j diff_l 0) ) = (sum ((sublist (0) ((j + 1 )) (diff_l))))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out_2 0)) /\ ((Znth k_4 out_2 0) <= (j * (m_pre + 1 ) ))))
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  ((cover + (Znth j diff_l 0) ) <= (m_pre + 1 ))
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  (0 <= (cover + (Znth j diff_l 0) ))
.

Definition solver_entail_wit_8_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  ((cover + (Znth j diff_l 0) ) = (sum ((sublist (0) ((j + 1 )) (diff_l)))))
.

Definition solver_entail_wit_8_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))
.

Definition solver_entail_wit_8_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))
.

Definition solver_entail_wit_8_split_goal_7 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l 0)) /\ ((Znth k_7 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))
.

Definition solver_entail_wit_9 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  (Int64Array.full cnt_pre 26 (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l_2 )
|--
  EX (out: (@list Z))  (diff_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (cover = (sum ((sublist (0) ((j + 1 )) (diff_l))))) ” 
  &&  “ (0 <= cover) ” 
  &&  “ (cover <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries (j + 1 ) out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= ((j + 1 ) * (m_pre + 1 ) )))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) 0)) /\ ((Znth k_4 (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) 0) <= ((j + 1 ) * (m_pre + 1 ) )))) ” 
  &&  “ (PartialSpec text tries (j + 1 ) (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) 0)) /\ ((Znth k_4 (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) 0) <= ((j + 1 ) * (m_pre + 1 ) ))))
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  (PartialSpec text tries (j + 1 ) (replace_Znth (((Znth j text 0) - 97 )) (((Znth ((Znth j text 0) - 97 ) out_2 0) + cover )) (out_2)) )
.

Definition solver_entail_wit_9_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l_2 0)) /\ ((Znth k_3 diff_l_2 0) <= (m_pre + 1 ))))
.

Definition solver_entail_wit_9_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))
.

Definition solver_entail_wit_9_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l_2: (@list Z)) (out_2: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((97 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 122)))) (PreH6 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < m_pre)) -> ((1 <= (Znth k_6 tries 0)) /\ ((Znth k_6 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l_2 )) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_7 diff_l_2 0)) /\ ((Znth k_7 diff_l_2 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l_2)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> ((0 <= (Znth k_8 out_2 0)) /\ ((Znth k_8 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))
.

Definition solver_return_wit_1 := 
(
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out_2 0)) /\ ((Znth k_4 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out_2 )
|--
  EX (diff_after: (@list Z))  (out: (@list Z)) ,
  “ (Spec text tries out ) ” 
  &&  “ ((Zlength (diff_after)) = (n_pre + 1 )) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full cnt_pre 26 out )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_after )
) \/
(
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out_2 0)) /\ ((Znth k_4 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  TT && emp 
|--
  “ ((Zlength (diff_l)) = (n_pre + 1 )) ” 
  &&  “ (Spec text tries out_2 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out_2 0)) /\ ((Znth k_4 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  ((Zlength (diff_l)) = (n_pre + 1 ))
.

Definition solver_return_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out_2: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out_2 )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out_2 0)) /\ ((Znth k_4 out_2 0) <= (j * (m_pre + 1 ) ))))) ,
  (Spec text tries out_2 )
.

Definition solver_partial_solve_wit_1_pure := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
|--
  “ (0 <= (sizeof(INT64) * (n_pre + 1 ) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) )) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
|--
  “ (0 <= (sizeof(INT64) * (n_pre + 1 ) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (aligned_4 (( &( "diff" ) ) + (0 * sizeof(INT64))) ) ”
  &&  (UCharArray.undef_full (( &( "diff" ) ) + (0 * sizeof(INT64))) (sizeof(INT64) * (n_pre + 1 ) ) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (i < m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((( &( "diff" ) ) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 diff_l 0))
  **  (Int64Array.missing_i ( &( "diff" ) ) 0 0 (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_3 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (i < m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((( &( "diff" ) ) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i ( &( "diff" ) ) 0 0 (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_4 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (i < m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((p_pre + (i * sizeof(INT)))) # Int  |-> (Znth i tries 0))
  **  (IntArray.missing_i p_pre i 0 m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_5 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (i < m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((p_pre + (i * sizeof(INT)))) # Int  |-> (Znth i tries 0))
  **  (IntArray.missing_i p_pre i 0 m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_6 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (i < m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((( &( "diff" ) ) + ((Znth i tries 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i tries 0) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) 0))
  **  (Int64Array.missing_i ( &( "diff" ) ) (Znth i tries 0) 0 (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_7 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (i < m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((( &( "diff" ) ) + ((Znth i tries 0) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i ( &( "diff" ) ) (Znth i tries 0) 0 (n_pre + 1 ) (replace_Znth (0) (((Znth 0 diff_l 0) + 1 )) (diff_l)) )
  **  (IntArray.full p_pre m_pre tries )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_8 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (i >= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((( &( "diff" ) ) + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 diff_l 0))
  **  (Int64Array.missing_i ( &( "diff" ) ) 0 0 (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_9 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (DifferencePrefix tries n_pre i diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i)))) ,
  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
|--
  “ (i >= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DifferencePrefix tries n_pre i diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-i) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= i))) ”
  &&  (((( &( "diff" ) ) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i ( &( "diff" ) ) 0 0 (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.undef_full cnt_pre 26 )
.

Definition solver_partial_solve_wit_10_pure := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l )) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
|--
  “ (0 <= (sizeof(INT64) * 26 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (aligned_4 cnt_pre ) ”
.

Definition solver_partial_solve_wit_10_aux := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (DifferenceReady tries n_pre diff_l )) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH11 : (aligned_4 cnt_pre )) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
|--
  “ (0 <= (sizeof(INT64) * 26 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (aligned_4 cnt_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (aligned_4 cnt_pre ) ”
  &&  (UCharArray.undef_full cnt_pre (sizeof(INT64) * 26 ) )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
.

Definition solver_partial_solve_wit_10 := solver_partial_solve_wit_10_pure -> solver_partial_solve_wit_10_aux.

Definition solver_partial_solve_wit_11 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (out: (@list Z)) (cover: Z) (diff_l: (@list Z)) (j: Z) (PreH1 : (j < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (m_pre = (Zlength (tries)))) (PreH10 : (0 <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (DifferenceReady tries n_pre diff_l )) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH14 : (cover = (sum ((sublist (0) (j) (diff_l)))))) (PreH15 : (0 <= cover)) (PreH16 : (cover <= (m_pre + 1 ))) (PreH17 : (PartialSpec text tries j out )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
|--
  “ (j < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (cover = (sum ((sublist (0) (j) (diff_l))))) ” 
  &&  “ (0 <= cover) ” 
  &&  “ (cover <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries j out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) )))) ”
  &&  (((( &( "diff" ) ) + (j * sizeof(INT64)))) # Int64  |-> (Znth j diff_l 0))
  **  (Int64Array.missing_i ( &( "diff" ) ) j 0 (n_pre + 1 ) diff_l )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full cnt_pre 26 out )
.

Definition solver_partial_solve_wit_12 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (cover = (sum ((sublist (0) ((j + 1 )) (diff_l))))) ” 
  &&  “ (0 <= cover) ” 
  &&  “ (cover <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries j out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) )))) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j text 0))
  **  (CharArray.missing_i s_pre j 0 n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
.

Definition solver_partial_solve_wit_13 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
  **  (Int64Array.full cnt_pre 26 out )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (cover = (sum ((sublist (0) ((j + 1 )) (diff_l))))) ” 
  &&  “ (0 <= cover) ” 
  &&  “ (cover <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries j out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) )))) ”
  &&  (((cnt_pre + (((Znth j text 0) - 97 ) * sizeof(INT64)))) # Int64  |-> (Znth ((Znth j text 0) - 97 ) out 0))
  **  (Int64Array.missing_i cnt_pre ((Znth j text 0) - 97 ) 0 26 out )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
.

Definition solver_partial_solve_wit_14 := 
forall (cnt_pre: Z) (m_pre: Z) (p_pre: Z) (n_pre: Z) (s_pre: Z) (tries: (@list Z)) (text: (@list Z)) (diff_l: (@list Z)) (out: (@list Z)) (j: Z) (cover: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (m_pre = (Zlength (tries)))) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (DifferenceReady tries n_pre diff_l )) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 ))))) (PreH13 : (cover = (sum ((sublist (0) ((j + 1 )) (diff_l)))))) (PreH14 : (0 <= cover)) (PreH15 : (cover <= (m_pre + 1 ))) (PreH16 : (PartialSpec text tries j out )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) ))))) ,
  (Int64Array.full cnt_pre 26 out )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((1 <= (Znth k_2 tries 0)) /\ ((Znth k_2 tries 0) < n_pre))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (m_pre = (Zlength (tries))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (DifferenceReady tries n_pre diff_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> (((-m_pre) <= (Znth k_3 diff_l 0)) /\ ((Znth k_3 diff_l 0) <= (m_pre + 1 )))) ” 
  &&  “ (cover = (sum ((sublist (0) ((j + 1 )) (diff_l))))) ” 
  &&  “ (0 <= cover) ” 
  &&  “ (cover <= (m_pre + 1 )) ” 
  &&  “ (PartialSpec text tries j out ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> ((0 <= (Znth k_4 out 0)) /\ ((Znth k_4 out 0) <= (j * (m_pre + 1 ) )))) ”
  &&  (((cnt_pre + (((Znth j text 0) - 97 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i cnt_pre ((Znth j text 0) - 97 ) 0 26 out )
  **  (CharArray.full s_pre n_pre text )
  **  (IntArray.full p_pre m_pre tries )
  **  (Int64Array.full ( &( "diff" ) ) (n_pre + 1 ) diff_l )
.

Module Type VC_Correct.


Axiom proof_of_memset_safety_wit_1 : memset_safety_wit_1.
Axiom proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Axiom proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Axiom proof_of_memset_return_wit_1 : memset_return_wit_1.
Axiom proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10_pure : solver_partial_solve_wit_10_pure.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.

End VC_Correct.
