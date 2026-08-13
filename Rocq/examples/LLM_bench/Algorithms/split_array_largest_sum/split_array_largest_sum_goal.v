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
Require Import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function check -----*)

Definition check_safety_wit_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_2 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 1)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_3 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "cnt" ) )) # Int  |-> 1)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_4 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i l 0) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_5 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i l 0) <= cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
.

Definition check_safety_wit_6 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) > cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cnt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition check_safety_wit_7 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) > cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_8 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) <= cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
.

Definition check_safety_wit_9 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) > cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
  **  ((( &( "cur" ) )) # Int  |-> (Znth i l 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_safety_wit_10 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) <= cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> (cur + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_safety_wit_11 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_12 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_entail_wit_1 := 
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (0 + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre 0 1 0 ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  TT && emp 
|--
  “ (PrefixSplitState l cap_pre 0 1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ”
  &&  emp
).

Definition check_entail_wit_1_split_goal_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  (PrefixSplitState l cap_pre 0 1 0 )
.

Definition check_entail_wit_1_split_goal_2 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : (0 <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))
.

Definition check_entail_wit_2_1 := 
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) > cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) <= ((i + 1 ) + 1 )) ” 
  &&  “ (0 <= (Znth i l 0)) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre (i + 1 ) (cnt + 1 ) (Znth i l 0) ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) > cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  TT && emp 
|--
  “ (PrefixSplitState l cap_pre (i + 1 ) (cnt + 1 ) (Znth i l 0) ) ”
  &&  emp
).

Definition check_entail_wit_2_1_split_goal_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) > cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (PrefixSplitState l cap_pre (i + 1 ) (cnt + 1 ) (Znth i l 0) )
.

Definition check_entail_wit_2_2 := 
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) <= cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= ((i + 1 ) + 1 )) ” 
  &&  “ (0 <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre (i + 1 ) cnt (cur + (Znth i l 0) ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) <= cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  TT && emp 
|--
  “ (PrefixSplitState l cap_pre (i + 1 ) cnt (cur + (Znth i l 0) ) ) ”
  &&  emp
).

Definition check_entail_wit_2_2_split_goal_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((cur + (Znth i l 0) ) <= cap_pre)) (PreH2 : ((Znth i l 0) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : (0 <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1 ))) (PreH16 : (0 <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (PrefixSplitState l cap_pre (i + 1 ) cnt (cur + (Znth i l 0) ) )
.

Definition check_return_wit_1 := 
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 = 1) -> (CanSplit l m_pre cap_pre )) ” 
  &&  “ ((0 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  TT && emp 
|--
  “ ((0 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  emp
).

Definition check_return_wit_1_split_goal_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  ((0 = 0) -> (CannotSplit l m_pre cap_pre ))
.

Definition check_return_wit_2 := 
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 = 1) -> (CanSplit l m_pre cap_pre )) ” 
  &&  “ ((1 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  TT && emp 
|--
  “ ((1 = 1) -> (CanSplit l m_pre cap_pre )) ”
  &&  emp
).

Definition check_return_wit_2_split_goal_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  ((1 = 1) -> (CanSplit l m_pre cap_pre ))
.

Definition check_return_wit_3 := 
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i l 0) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 = 1) -> (CanSplit l m_pre cap_pre )) ” 
  &&  “ ((0 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i l 0) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  TT && emp 
|--
  “ ((0 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  emp
).

Definition check_return_wit_3_split_goal_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : ((Znth i l 0) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : (0 <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1 ))) (PreH15 : (0 <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (PrefixSplitState l cap_pre i cnt cur )) ,
  ((0 = 0) -> (CannotSplit l m_pre cap_pre ))
.

Definition check_partial_solve_wit_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : (0 <= cap_pre)) (PreH7 : (cap_pre <= 1000000000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= cnt)) (PreH13 : (cnt <= (i + 1 ))) (PreH14 : (0 <= cur)) (PreH15 : (cur <= cap_pre)) (PreH16 : (PrefixSplitState l cap_pre i cnt cur )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

(*----- Function splitArrayLargestSum -----*)

Definition splitArrayLargestSum_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans )) (PreH8 : (0 <= ans)) (PreH9 : (ans <= 1000000000)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition splitArrayLargestSum_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans )) (PreH8 : (0 <= ans)) (PreH9 : (ans <= 1000000000)) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition splitArrayLargestSum_safety_wit_3 := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + ((right - left ) ÷ 2 ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + ((right - left ) ÷ 2 ) )) ”
).

Definition splitArrayLargestSum_safety_wit_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition splitArrayLargestSum_safety_wit_3_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((INT_MIN) <= (left + ((right - left ) ÷ 2 ) )) ”
.

Definition splitArrayLargestSum_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (((right - left ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition splitArrayLargestSum_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((right - left ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right - left )) ”
.

Definition splitArrayLargestSum_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition splitArrayLargestSum_safety_wit_7 := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res )) (PreH18 : (retval = 0)) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res )) (PreH18 : (retval = 0)) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ”
).

Definition splitArrayLargestSum_safety_wit_7_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res )) (PreH18 : (retval = 0)) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= INT_MAX) ”
.

Definition splitArrayLargestSum_safety_wit_7_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res )) (PreH18 : (retval = 0)) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((INT_MIN) <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ”
.

Definition splitArrayLargestSum_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res)) (PreH16 : (res <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res )) (PreH18 : (retval = 0)) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition splitArrayLargestSum_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans )) (PreH8 : (0 <= ans)) (PreH9 : (ans <= 1000000000)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1000000000 <= 1000000000) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (m_pre: Z) (n_pre: Z) (l: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH7 : (MinimizedMaxSegmentSum l m_pre ans )) (PreH8 : (0 <= ans)) (PreH9 : (ans <= 1000000000)) ,
  TT && emp 
|--
  EX (res: Z) ,
  “ (0 <= 0) ” 
  &&  “ (1000000000 <= 1000000000) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  emp
).

Definition splitArrayLargestSum_entail_wit_2_1 := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res_2: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2 )) (PreH18 : (retval <> 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (left <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (m_pre: Z) (n_pre: Z) (l: (@list Z)) (res_2: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2 )) (PreH18 : (retval <> 0)) ,
  TT && emp 
|--
  EX (res: Z) ,
  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (left <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  emp
).

Definition splitArrayLargestSum_entail_wit_2_2 := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res_2: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2 )) (PreH18 : (retval = 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= right) ” 
  &&  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (m_pre: Z) (n_pre: Z) (l: (@list Z)) (res_2: Z) (right: Z) (left: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH4 : ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) ))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH12 : (0 <= left)) (PreH13 : (right <= 1000000000)) (PreH14 : (left <= right)) (PreH15 : (left <= res_2)) (PreH16 : (res_2 <= right)) (PreH17 : (MinimizedMaxSegmentSum l m_pre res_2 )) (PreH18 : (retval = 0)) ,
  TT && emp 
|--
  EX (res: Z) ,
  “ (0 <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ” 
  &&  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= right) ” 
  &&  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  emp
).

Definition splitArrayLargestSum_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (MinimizedMaxSegmentSum l m_pre left ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (m_pre: Z) (n_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  TT && emp 
|--
  “ (MinimizedMaxSegmentSum l m_pre left ) ”
  &&  emp
).

Definition splitArrayLargestSum_return_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  (MinimizedMaxSegmentSum l m_pre left )
.

Definition splitArrayLargestSum_partial_solve_wit_1_pure := 
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (0 <= (left + ((right - left ) ÷ 2 ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + ((right - left ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH18 : (0 <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (0 <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ”
).

Definition splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + ((right - left ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH18 : (0 <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (0 <= (left + ((right - left ) ÷ 2 ) )) ”
.

Definition splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + ((right - left ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH18 : (0 <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ”
.

Definition splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + ((right - left ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH18 : (0 <= left)) (PreH19 : (right <= 1000000000)) (PreH20 : (left <= right)) (PreH21 : (left <= res)) (PreH22 : (res <= right)) (PreH23 : (MinimizedMaxSegmentSum l m_pre res )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ”
.

Definition splitArrayLargestSum_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000)))) (PreH8 : (0 <= left)) (PreH9 : (right <= 1000000000)) (PreH10 : (left <= right)) (PreH11 : (left <= res)) (PreH12 : (res <= right)) (PreH13 : (MinimizedMaxSegmentSum l m_pre res )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (0 <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition splitArrayLargestSum_partial_solve_wit_1 := splitArrayLargestSum_partial_solve_wit_1_pure -> splitArrayLargestSum_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_check_safety_wit_1 : check_safety_wit_1.
Axiom proof_of_check_safety_wit_2 : check_safety_wit_2.
Axiom proof_of_check_safety_wit_3 : check_safety_wit_3.
Axiom proof_of_check_safety_wit_4 : check_safety_wit_4.
Axiom proof_of_check_safety_wit_5 : check_safety_wit_5.
Axiom proof_of_check_safety_wit_6 : check_safety_wit_6.
Axiom proof_of_check_safety_wit_7 : check_safety_wit_7.
Axiom proof_of_check_safety_wit_8 : check_safety_wit_8.
Axiom proof_of_check_safety_wit_9 : check_safety_wit_9.
Axiom proof_of_check_safety_wit_10 : check_safety_wit_10.
Axiom proof_of_check_safety_wit_11 : check_safety_wit_11.
Axiom proof_of_check_safety_wit_12 : check_safety_wit_12.
Axiom proof_of_check_entail_wit_1 : check_entail_wit_1.
Axiom proof_of_check_entail_wit_2_1 : check_entail_wit_2_1.
Axiom proof_of_check_entail_wit_2_2 : check_entail_wit_2_2.
Axiom proof_of_check_return_wit_1 : check_return_wit_1.
Axiom proof_of_check_return_wit_2 : check_return_wit_2.
Axiom proof_of_check_return_wit_3 : check_return_wit_3.
Axiom proof_of_check_partial_solve_wit_1 : check_partial_solve_wit_1.
Axiom proof_of_splitArrayLargestSum_safety_wit_1 : splitArrayLargestSum_safety_wit_1.
Axiom proof_of_splitArrayLargestSum_safety_wit_2 : splitArrayLargestSum_safety_wit_2.
Axiom proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3.
Axiom proof_of_splitArrayLargestSum_safety_wit_4 : splitArrayLargestSum_safety_wit_4.
Axiom proof_of_splitArrayLargestSum_safety_wit_5 : splitArrayLargestSum_safety_wit_5.
Axiom proof_of_splitArrayLargestSum_safety_wit_6 : splitArrayLargestSum_safety_wit_6.
Axiom proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7.
Axiom proof_of_splitArrayLargestSum_safety_wit_8 : splitArrayLargestSum_safety_wit_8.
Axiom proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1.
Axiom proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1.
Axiom proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2.
Axiom proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1.
Axiom proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure.
Axiom proof_of_splitArrayLargestSum_partial_solve_wit_1 : splitArrayLargestSum_partial_solve_wit_1.

End VC_Correct.
