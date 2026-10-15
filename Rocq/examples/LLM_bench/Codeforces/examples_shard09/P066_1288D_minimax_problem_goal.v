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
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function feasible -----*)

Definition feasible_safety_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 )) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 )) ”
).

Definition feasible_safety_wit_1_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) <= INT_MAX) ”
.

Definition feasible_safety_wit_1_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 )) ”
.

Definition feasible_safety_wit_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((signed_last_nbits ((1 * (2^m_pre) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^m_pre) )) (32))) ” 
  &&  “ (m_pre <= 31) ” 
  &&  “ (0 <= m_pre) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((signed_last_nbits ((1 * (2^m_pre) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^m_pre) )) (32))) ” 
  &&  “ (m_pre <= 31) ” 
  &&  “ (0 <= m_pre) ”
).

Definition feasible_safety_wit_2_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((signed_last_nbits ((1 * (2^m_pre) )) (32)) <= INT_MAX) ”
.

Definition feasible_safety_wit_2_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^m_pre) )) (32))) ”
.

Definition feasible_safety_wit_2_split_goal_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (m_pre <= 31) ”
.

Definition feasible_safety_wit_2_split_goal_4 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= m_pre) ”
.

Definition feasible_safety_wit_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_4 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_5 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "full" ) )) # Int  |-> ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_6 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps 0) = (-1)))) ,
  (IntArray.full rep_pre 256 (replace_Znth (s) ((-1)) (reps)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition feasible_safety_wit_7 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps 0) = (-1)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition feasible_safety_wit_8 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps 0) = (-1)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_9 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps 0) = (-1)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_10 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  ((( &( "mask" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_11 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "mask" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_12 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= j)) (PreH19 : (j <= m_pre)) (PreH20 : (0 <= ((i * m_pre ) + j ))) (PreH21 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH22 : (0 <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH26 : (RowMaskPrefix rows x_pre i j mask )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (((i * m_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * m_pre ) + j )) ”
.

Definition feasible_safety_wit_13 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= j)) (PreH19 : (j <= m_pre)) (PreH20 : (0 <= ((i * m_pre ) + j ))) (PreH21 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH22 : (0 <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH26 : (RowMaskPrefix rows x_pre i j mask )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((i * m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * m_pre )) ”
.

Definition feasible_safety_wit_14 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((signed_last_nbits ((1 * (2^j) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^j) )) (32))) ” 
  &&  “ (j <= 31) ” 
  &&  “ (0 <= j) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((signed_last_nbits ((1 * (2^j) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^j) )) (32))) ” 
  &&  “ (j <= 31) ” 
  &&  “ (0 <= j) ”
).

Definition feasible_safety_wit_14_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((signed_last_nbits ((1 * (2^j) )) (32)) <= INT_MAX) ”
.

Definition feasible_safety_wit_14_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^j) )) (32))) ”
.

Definition feasible_safety_wit_14_split_goal_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (j <= 31) ”
.

Definition feasible_safety_wit_14_split_goal_4 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= j) ”
.

Definition feasible_safety_wit_15 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_16 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))))
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition feasible_safety_wit_17 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) < x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition feasible_safety_wit_18 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : (j >= m_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= j)) (PreH19 : (j <= m_pre)) (PreH20 : (0 <= ((i * m_pre ) + j ))) (PreH21 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH22 : (0 <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH26 : (RowMaskPrefix rows x_pre i j mask )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_19 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (IntArray.full rep_pre 256 (replace_Znth (mask) (i) (reps)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_20 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps 0) >= 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_21 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_22 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH20 : (NoCoverPrefix reps full s 0 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_23 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps 0) >= 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH21 : (NoCoverPrefix reps full s 0 )) (PreH22 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  ((( &( "u" ) )) # Int  |->_)
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_24 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps)) = 256)) (PreH21 : (0 <= (Znth s reps 0))) (PreH22 : ((Znth s reps 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH24 : (NoCoverPrefix reps full s u )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_25 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ (((Znth s reps 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth s reps 0) + 1 )) ”
.

Definition feasible_safety_wit_26 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_27 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((bi_pre) # Int  |-> ((Znth s reps 0) + 1 ))
  **  ((bj_pre) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ (((Znth u reps 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth u reps 0) + 1 )) ”
.

Definition feasible_safety_wit_28 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((bi_pre) # Int  |-> ((Znth s reps 0) + 1 ))
  **  ((bj_pre) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_29 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((bi_pre) # Int  |-> ((Znth s reps 0) + 1 ))
  **  ((bj_pre) # Int  |-> ((Znth u reps 0) + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_30 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps)) = 256)) (PreH21 : (0 <= (Znth s reps 0))) (PreH22 : ((Znth s reps 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH24 : (NoCoverPrefix reps full s u )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition feasible_safety_wit_31 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps 0) < 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH21 : (NoCoverPrefix reps full s 0 )) (PreH22 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition feasible_safety_wit_32 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth u reps 0) < 0)) (PreH2 : (u <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= full)) (PreH19 : (0 <= u)) (PreH20 : (u <= (full + 1 ))) (PreH21 : ((Zlength (reps)) = 256)) (PreH22 : (0 <= (Znth s reps 0))) (PreH23 : ((Znth s reps 0) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH25 : (NoCoverPrefix reps full s u )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition feasible_safety_wit_33 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) <> full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((u + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u + 1 )) ”
.

Definition feasible_safety_wit_34 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH20 : (NoCoverPrefix reps full s 0 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_entail_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 )) ” 
  &&  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) <= 255) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < 0)) -> ((Znth q reps 0) = (-1))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  (IntArray.full_shape rep_pre 256 )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 )) ” 
  &&  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) <= 255) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1 ) + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < 0)) -> ((Znth q reps 0) = (-1))) ”
  &&  (IntArray.full rep_pre 256 reps )
).

Definition feasible_entail_wit_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps_2 0) = (-1)))) ,
  (IntArray.full rep_pre 256 (replace_Znth (s) ((-1)) (reps_2)) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (s + 1 ))) -> ((Znth q reps 0) = (-1))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps_2 0) = (-1)))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (s) ((-1)) (reps_2)))) = 256) ”
  &&  emp
).

Definition feasible_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps_2 0) = (-1)))) ,
  ((Zlength ((replace_Znth (s) ((-1)) (reps_2)))) = 256)
.

Definition feasible_entail_wit_3 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < s)) -> ((Znth q_2 reps_2 0) = (-1)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre 0 reps ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < 0))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < s)) -> ((Znth q_2 reps_2 0) = (-1)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < 0))) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre 0 reps_2 ) ”
  &&  emp
).

Definition feasible_entail_wit_3_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < s)) -> ((Znth q_2 reps_2 0) = (-1)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < 0)))
.

Definition feasible_entail_wit_3_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < s)) -> ((Znth q_2 reps_2 0) = (-1)))) ,
  (RepresentativePrefix rows x_pre m_pre 0 reps_2 )
.

Definition feasible_entail_wit_4 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= ((i * m_pre ) + 0 )) ” 
  &&  “ (((i * m_pre ) + 0 ) <= (n_pre * m_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= full) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre i reps ) ” 
  &&  “ (RowMaskPrefix rows x_pre i 0 0 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i))) ” 
  &&  “ (RowMaskPrefix rows x_pre i 0 0 ) ” 
  &&  “ (((i * m_pre ) + 0 ) <= (n_pre * m_pre )) ”
  &&  emp
).

Definition feasible_entail_wit_4_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))
.

Definition feasible_entail_wit_4_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (RowMaskPrefix rows x_pre i 0 0 )
.

Definition feasible_entail_wit_4_split_goal_3 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (((i * m_pre ) + 0 ) <= (n_pre * m_pre ))
.

Definition feasible_entail_wit_5_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (0 <= ((i * m_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * m_pre ) + (j + 1 ) ) <= (n_pre * m_pre )) ” 
  &&  “ (0 <= (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ” 
  &&  “ ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) <= full) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre i reps ) ” 
  &&  “ (RowMaskPrefix rows x_pre i (j + 1 ) (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (RowMaskPrefix rows x_pre i (j + 1 ) (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) ) ” 
  &&  “ ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) <= ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ” 
  &&  “ (((i * m_pre ) + (j + 1 ) ) <= (n_pre * m_pre )) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
).

Definition feasible_entail_wit_5_1_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (RowMaskPrefix rows x_pre i (j + 1 ) (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) ) ”
.

Definition feasible_entail_wit_5_1_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) <= ((Z.shiftl 1 m_pre) - 1 )) ”
.

Definition feasible_entail_wit_5_1_split_goal_3 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (0 <= (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ”
.

Definition feasible_entail_wit_5_1_split_goal_4 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (((i * m_pre ) + (j + 1 ) ) <= (n_pre * m_pre )) ”
.

Definition feasible_entail_wit_5_1_split_goal_spatial := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  (IntArray2.full a_pre n_pre m_pre rows )
.

Definition feasible_entail_wit_5_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) < x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (0 <= ((i * m_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * m_pre ) + (j + 1 ) ) <= (n_pre * m_pre )) ” 
  &&  “ (0 <= mask) ” 
  &&  “ (mask <= full) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre i reps ) ” 
  &&  “ (RowMaskPrefix rows x_pre i (j + 1 ) mask ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (RowMaskPrefix rows x_pre i (j + 1 ) mask ) ” 
  &&  “ (((i * m_pre ) + (j + 1 ) ) <= (n_pre * m_pre )) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
).

Definition feasible_entail_wit_5_2_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (RowMaskPrefix rows x_pre i (j + 1 ) mask ) ”
.

Definition feasible_entail_wit_5_2_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  “ (((i * m_pre ) + (j + 1 ) ) <= (n_pre * m_pre )) ”
.

Definition feasible_entail_wit_5_2_split_goal_spatial := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) (0)) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (0 <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH17 : (0 <= full)) (PreH18 : (full <= 255)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= m_pre)) (PreH23 : (0 <= ((i * m_pre ) + j ))) (PreH24 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH25 : (0 <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH29 : (RowMaskPrefix rows x_pre i j mask )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < i)))) ,
  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
|--
  (IntArray2.full a_pre n_pre m_pre rows )
.

Definition feasible_entail_wit_6_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (IntArray.full rep_pre 256 (replace_Znth (mask) (i) (reps_2)) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre (i + 1 ) reps ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < (i + 1 )))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q (replace_Znth (mask) (i) (reps_2)) 0)) /\ ((Znth q (replace_Znth (mask) (i) (reps_2)) 0) < (i + 1 )))) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre (i + 1 ) (replace_Znth (mask) (i) (reps_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (mask) (i) (reps_2)))) = 256) ”
  &&  emp
).

Definition feasible_entail_wit_6_1_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q (replace_Znth (mask) (i) (reps_2)) 0)) /\ ((Znth q (replace_Znth (mask) (i) (reps_2)) 0) < (i + 1 ))))
.

Definition feasible_entail_wit_6_1_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (RepresentativePrefix rows x_pre m_pre (i + 1 ) (replace_Znth (mask) (i) (reps_2)) )
.

Definition feasible_entail_wit_6_1_split_goal_3 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  ((Zlength ((replace_Znth (mask) (i) (reps_2)))) = 256)
.

Definition feasible_entail_wit_6_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) >= 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre (i + 1 ) reps ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < (i + 1 )))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) >= 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < (i + 1 )))) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre (i + 1 ) reps_2 ) ”
  &&  emp
).

Definition feasible_entail_wit_6_2_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) >= 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < (i + 1 ))))
.

Definition feasible_entail_wit_6_2_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps_2 0) >= 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (RepresentativePrefix rows x_pre m_pre (i + 1 ) reps_2 )
.

Definition feasible_entail_wit_7 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full 0 0 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre))) ” 
  &&  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) 0 0 ) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps_2 ) ”
  &&  emp
).

Definition feasible_entail_wit_7_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))
.

Definition feasible_entail_wit_7_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) 0 0 )
.

Definition feasible_entail_wit_7_split_goal_3 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (i: Z) (full: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2 )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < i)))) ,
  (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )
.

Definition feasible_entail_wit_8 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps_2 0) >= 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH21 : (NoCoverPrefix reps_2 full s 0 )) (PreH22 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s 0 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps_2 0) >= 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH21 : (NoCoverPrefix reps_2 full s 0 )) (PreH22 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre))) ”
  &&  emp
).

Definition feasible_entail_wit_8_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps_2 0) >= 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH21 : (NoCoverPrefix reps_2 full s 0 )) (PreH22 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))
.

Definition feasible_entail_wit_9_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : (0 <= (Znth s reps_2 0))) (PreH22 : ((Znth s reps_2 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH24 : (NoCoverPrefix reps_2 full s u )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full (s + 1 ) 0 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : (0 <= (Znth s reps_2 0))) (PreH22 : ((Znth s reps_2 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH24 : (NoCoverPrefix reps_2 full s u )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre))) ” 
  &&  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) (s + 1 ) 0 ) ”
  &&  emp
).

Definition feasible_entail_wit_9_1_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : (0 <= (Znth s reps_2 0))) (PreH22 : ((Znth s reps_2 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH24 : (NoCoverPrefix reps_2 full s u )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))
.

Definition feasible_entail_wit_9_1_split_goal_2 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : (0 <= (Znth s reps_2 0))) (PreH22 : ((Znth s reps_2 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH24 : (NoCoverPrefix reps_2 full s u )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 0)) /\ ((Znth q_2 reps_2 0) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) (s + 1 ) 0 )
.

Definition feasible_entail_wit_9_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps_2 0) < 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH21 : (NoCoverPrefix reps_2 full s 0 )) (PreH22 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full (s + 1 ) 0 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps_2 0) < 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH21 : (NoCoverPrefix reps_2 full s 0 )) (PreH22 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) (s + 1 ) 0 ) ”
  &&  emp
).

Definition feasible_entail_wit_9_2_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth s reps_2 0) < 0)) (PreH2 : (s <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= (full + 1 ))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH21 : (NoCoverPrefix reps_2 full s 0 )) (PreH22 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) (s + 1 ) 0 )
.

Definition feasible_entail_wit_10_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth u reps_2 0) < 0)) (PreH2 : (u <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= full)) (PreH19 : (0 <= u)) (PreH20 : (u <= (full + 1 ))) (PreH21 : ((Zlength (reps_2)) = 256)) (PreH22 : (0 <= (Znth s reps_2 0))) (PreH23 : ((Znth s reps_2 0) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH25 : (NoCoverPrefix reps_2 full s u )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= (u + 1 )) ” 
  &&  “ ((u + 1 ) <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s (u + 1 ) ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth u reps_2 0) < 0)) (PreH2 : (u <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= full)) (PreH19 : (0 <= u)) (PreH20 : (u <= (full + 1 ))) (PreH21 : ((Zlength (reps_2)) = 256)) (PreH22 : (0 <= (Znth s reps_2 0))) (PreH23 : ((Znth s reps_2 0) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH25 : (NoCoverPrefix reps_2 full s u )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) s (u + 1 ) ) ”
  &&  emp
).

Definition feasible_entail_wit_10_1_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth u reps_2 0) < 0)) (PreH2 : (u <= full)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= s)) (PreH18 : (s <= full)) (PreH19 : (0 <= u)) (PreH20 : (u <= (full + 1 ))) (PreH21 : ((Zlength (reps_2)) = 256)) (PreH22 : (0 <= (Znth s reps_2 0))) (PreH23 : ((Znth s reps_2 0) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH25 : (NoCoverPrefix reps_2 full s u )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) s (u + 1 ) )
.

Definition feasible_entail_wit_10_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) <> full)) (PreH2 : ((Znth u reps_2 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : (0 <= (Znth s reps_2 0))) (PreH24 : ((Znth s reps_2 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH26 : (NoCoverPrefix reps_2 full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= (u + 1 )) ” 
  &&  “ ((u + 1 ) <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s (u + 1 ) ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) <> full)) (PreH2 : ((Znth u reps_2 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : (0 <= (Znth s reps_2 0))) (PreH24 : ((Znth s reps_2 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH26 : (NoCoverPrefix reps_2 full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) s (u + 1 ) ) ”
  &&  emp
).

Definition feasible_entail_wit_10_2_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) <> full)) (PreH2 : ((Znth u reps_2 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : (0 <= (Znth s reps_2 0))) (PreH24 : ((Znth s reps_2 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH26 : (NoCoverPrefix reps_2 full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1 ) s (u + 1 ) )
.

Definition feasible_return_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH20 : (NoCoverPrefix reps_2 full s 0 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (reps: (@list Z)) ,
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((FeasibleAtThreshold rows x_pre )) ”
  &&  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
) \/
(
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH20 : (NoCoverPrefix reps_2 full s 0 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ ~((FeasibleAtThreshold rows x_pre )) ”
  &&  emp
).

Definition feasible_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s > full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH20 : (NoCoverPrefix reps_2 full s 0 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  ~((FeasibleAtThreshold rows x_pre ))
.

Definition feasible_return_wit_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps_2 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : (0 <= (Znth s reps_2 0))) (PreH24 : ((Znth s reps_2 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH26 : (NoCoverPrefix reps_2 full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps_2 )
  **  ((bi_pre) # Int  |-> ((Znth s reps_2 0) + 1 ))
  **  ((bj_pre) # Int  |-> ((Znth u reps_2 0) + 1 ))
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  EX (i: Z)  (j: Z)  (reps: (@list Z)) ,
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (1 = 1) ” 
  &&  “ (PairAtLeast rows x_pre i j ) ”
  &&  (IntArray.full bi_pre 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps_2: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (((Znth u reps_2 0) + 1 ) <= INT_MAX)) (PreH2 : (((Znth s reps_2 0) + 1 ) <= INT_MAX)) (PreH3 : (((Znth u reps_2 0) + 1 ) >= INT_MIN)) (PreH4 : (((Znth s reps_2 0) + 1 ) >= INT_MIN)) (PreH5 : ((Z.lor s u) = full)) (PreH6 : ((Znth u reps_2 0) >= 0)) (PreH7 : (u <= full)) (PreH8 : (Pre rows )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (0 <= x_pre)) (PreH14 : (x_pre <= 1000000000)) (PreH15 : (n_pre = (Zlength (rows)))) (PreH16 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH17 : ((Zlength (old_bi)) = 1)) (PreH18 : ((Zlength (old_bj)) = 1)) (PreH19 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH20 : (0 <= full)) (PreH21 : (full <= 255)) (PreH22 : (0 <= s)) (PreH23 : (s <= full)) (PreH24 : (0 <= u)) (PreH25 : (u <= (full + 1 ))) (PreH26 : ((Zlength (reps_2)) = 256)) (PreH27 : (0 <= (Znth s reps_2 0))) (PreH28 : ((Znth s reps_2 0) < n_pre)) (PreH29 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2 )) (PreH30 : (NoCoverPrefix reps_2 full s u )) (PreH31 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps_2 0)) /\ ((Znth q reps_2 0) < n_pre)))) ,
  ((bi_pre) # Int  |-> ((Znth s reps_2 0) + 1 ))
  **  ((bj_pre) # Int  |-> ((Znth u reps_2 0) + 1 ))
|--
  EX (i: Z)  (j: Z) ,
  “ ((Zlength (reps_2)) = 256) ” 
  &&  “ (PairAtLeast rows x_pre i j ) ”
  &&  (IntArray.full bi_pre 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((j + 1 )) ((@nil Z))) )
).

Definition feasible_partial_solve_wit_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps 0) = (-1)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (s <= full) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < s)) -> ((Znth q reps 0) = (-1))) ”
  &&  (((rep_pre + (s * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i rep_pre s 0 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
.

Definition feasible_partial_solve_wit_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= j)) (PreH19 : (j <= m_pre)) (PreH20 : (0 <= ((i * m_pre ) + j ))) (PreH21 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH22 : (0 <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH26 : (RowMaskPrefix rows x_pre i j mask )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (j < m_pre) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (0 <= ((i * m_pre ) + j )) ” 
  &&  “ (((i * m_pre ) + j ) <= (n_pre * m_pre )) ” 
  &&  “ (0 <= mask) ” 
  &&  “ (mask <= full) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre i reps ) ” 
  &&  “ (RowMaskPrefix rows x_pre i j mask ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i))) ”
  &&  (((a_pre + (((i * m_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + ((i * m_pre ) * sizeof(INT))) j 0 m_pre (Znth i rows __default__List_Z) )
  **  (IntArray2.missing_i a_pre i 0 n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
.

Definition feasible_partial_solve_wit_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : (j >= m_pre)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= j)) (PreH19 : (j <= m_pre)) (PreH20 : (0 <= ((i * m_pre ) + j ))) (PreH21 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH22 : (0 <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH26 : (RowMaskPrefix rows x_pre i j mask )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (j >= m_pre) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (0 <= ((i * m_pre ) + j )) ” 
  &&  “ (((i * m_pre ) + j ) <= (n_pre * m_pre )) ” 
  &&  “ (0 <= mask) ” 
  &&  “ (mask <= full) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre i reps ) ” 
  &&  “ (RowMaskPrefix rows x_pre i j mask ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i))) ”
  &&  (((rep_pre + (mask * sizeof(INT)))) # Int  |-> (Znth mask reps 0))
  **  (IntArray.missing_i rep_pre mask 0 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
.

Definition feasible_partial_solve_wit_4 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (mask: Z) (j: Z) (i: Z) (full: Z)  __default__List_Z (PreH1 : ((Znth mask reps 0) < 0)) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (0 <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH15 : (0 <= full)) (PreH16 : (full <= 255)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= m_pre)) (PreH21 : (0 <= ((i * m_pre ) + j ))) (PreH22 : (((i * m_pre ) + j ) <= (n_pre * m_pre ))) (PreH23 : (0 <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps )) (PreH27 : (RowMaskPrefix rows x_pre i j mask )) (PreH28 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i)))) ,
  (IntArray.full rep_pre 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((Znth mask reps 0) < 0) ” 
  &&  “ (j >= m_pre) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (0 <= ((i * m_pre ) + j )) ” 
  &&  “ (((i * m_pre ) + j ) <= (n_pre * m_pre )) ” 
  &&  “ (0 <= mask) ” 
  &&  “ (mask <= full) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre i reps ) ” 
  &&  “ (RowMaskPrefix rows x_pre i j mask ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < i))) ”
  &&  (((rep_pre + (mask * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i rep_pre mask 0 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
.

Definition feasible_partial_solve_wit_5 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (s: Z) (full: Z)  __default__List_Z (PreH1 : (s <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= (full + 1 ))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH20 : (NoCoverPrefix reps full s 0 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (s <= full) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s 0 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (((rep_pre + (s * sizeof(INT)))) # Int  |-> (Znth s reps 0))
  **  (IntArray.missing_i rep_pre s 0 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
.

Definition feasible_partial_solve_wit_6 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : (u <= full)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH14 : (0 <= full)) (PreH15 : (full <= 255)) (PreH16 : (0 <= s)) (PreH17 : (s <= full)) (PreH18 : (0 <= u)) (PreH19 : (u <= (full + 1 ))) (PreH20 : ((Zlength (reps)) = 256)) (PreH21 : (0 <= (Znth s reps 0))) (PreH22 : ((Znth s reps 0) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH24 : (NoCoverPrefix reps full s u )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ (u <= full) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s u ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (((rep_pre + (u * sizeof(INT)))) # Int  |-> (Znth u reps 0))
  **  (IntArray.missing_i rep_pre u 0 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
.

Definition feasible_partial_solve_wit_7 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  “ ((Z.lor s u) = full) ” 
  &&  “ ((Znth u reps 0) >= 0) ” 
  &&  “ (u <= full) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s u ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
.

Definition feasible_partial_solve_wit_8 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ ((Z.lor s u) = full) ” 
  &&  “ ((Znth u reps 0) >= 0) ” 
  &&  “ (u <= full) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s u ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (((rep_pre + (s * sizeof(INT)))) # Int  |-> (Znth s reps 0))
  **  (IntArray.missing_i rep_pre s 0 256 reps )
  **  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
  **  (IntArray2.full a_pre n_pre m_pre rows )
.

Definition feasible_partial_solve_wit_9 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (x_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) (rows: (@list (@list Z))) (reps: (@list Z)) (u: Z) (s: Z) (full: Z)  __default__List_Z (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps 0) >= 0)) (PreH3 : (u <= full)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (0 <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1 ))) (PreH16 : (0 <= full)) (PreH17 : (full <= 255)) (PreH18 : (0 <= s)) (PreH19 : (s <= full)) (PreH20 : (0 <= u)) (PreH21 : (u <= (full + 1 ))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : (0 <= (Znth s reps 0))) (PreH24 : ((Znth s reps 0) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps )) (PreH26 : (NoCoverPrefix reps full s u )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre)))) ,
  (IntArray.full rep_pre 256 reps )
  **  ((bi_pre) # Int  |-> ((Znth s reps 0) + 1 ))
  **  ((bj_pre) # Int  |->_)
  **  (IntArray2.full a_pre n_pre m_pre rows )
|--
  “ ((Z.lor s u) = full) ” 
  &&  “ ((Znth u reps 0) >= 0) ” 
  &&  “ (u <= full) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (old_bi)) = 1) ” 
  &&  “ ((Zlength (old_bj)) = 1) ” 
  &&  “ (full = ((Z.shiftl 1 m_pre) - 1 )) ” 
  &&  “ (0 <= full) ” 
  &&  “ (full <= 255) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= full) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u <= (full + 1 )) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (0 <= (Znth s reps 0)) ” 
  &&  “ ((Znth s reps 0) < n_pre) ” 
  &&  “ (RepresentativePrefix rows x_pre m_pre n_pre reps ) ” 
  &&  “ (NoCoverPrefix reps full s u ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= full)) -> (((-1) <= (Znth q reps 0)) /\ ((Znth q reps 0) < n_pre))) ”
  &&  (((rep_pre + (u * sizeof(INT)))) # Int  |-> (Znth u reps 0))
  **  (IntArray.missing_i rep_pre u 0 256 reps )
  **  ((bi_pre) # Int  |-> ((Znth s reps 0) + 1 ))
  **  ((bj_pre) # Int  |->_)
  **  (IntArray2.full a_pre n_pre m_pre rows )
.

Definition feasible_which_implies_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) ,
  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (old_bj: (@list (@option Z))) (old_bi: (@list (@option Z))) ,
  (IntArray.mixed_full bi_pre 1 old_bi )
  **  (IntArray.mixed_full bj_pre 1 old_bj )
|--
  EX (x_2: Z)  (x: Z) ,
  ((bj_pre) # Int  |-> x_2)
  **  ((bi_pre) # Int  |-> x)
).

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.undef_full bi_pre 1 )
  **  (IntArray.undef_full bj_pre 1 )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition solver_safety_wit_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) ,
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.undef_full bi_pre 1 )
  **  (IntArray.undef_full bj_pre 1 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) ,
  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> 1000000000)
  **  ((( &( "lo" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition solver_safety_wit_4_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition solver_safety_wit_5 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((((hi - lo ) + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_6 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (((hi - lo ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((hi - lo ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hi - lo )) ”
.

Definition solver_safety_wit_8 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_10 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_11 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval <> 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_12 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
).

Definition solver_safety_wit_12_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((INT_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo >= hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z)))  __default__List_Z (PreH1 : ((Zlength (bi_cells)) = 1)) (PreH2 : ((Zlength (bj_cells)) = 1)) (PreH3 : (lo = 0)) (PreH4 : (lo >= hi)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH13 : (0 <= lo)) (PreH14 : (lo <= hi)) (PreH15 : (hi <= 1000000000)) (PreH16 : (0 <= cur_i)) (PreH17 : (cur_i < n_pre)) (PreH18 : (0 <= cur_j)) (PreH19 : (cur_j < n_pre)) (PreH20 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8)))) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) ,
  ((bi_pre) # Int  |-> 1)
  **  ((bj_pre) # Int  |-> 1)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  EX (cur_j: Z)  (cur_i: Z) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (1000000000 <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows 0 1000000000 cur_i cur_j ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) ,
  ((bi_pre) # Int  |-> 1)
  **  ((bj_pre) # Int  |-> 1)
  **  (IntArray.full_shape rep_pre 256 )
|--
  EX (cur_j: Z)  (cur_i: Z) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (1000000000 <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows 0 1000000000 cur_i cur_j ) ”
  &&  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
).

Definition solver_entail_wit_2_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps_2: (@list Z)) (retval_2: Z)  __default__List_Z (PreH1 : ((Zlength (reps_2)) = 256)) (PreH2 : (retval_2 = 1)) (PreH3 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval_2 = 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  EX (reps: (@list Z))  (retval: Z) ,
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) )) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_entail_wit_2_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) )) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_entail_wit_3_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (retval = 1) ” 
  &&  “ (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j ) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_entail_wit_3_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps_2: (@list Z)) (retval_2: Z)  __default__List_Z (PreH1 : ((Zlength (reps_2)) = 256)) (PreH2 : (retval_2 = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval_2 <> 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps_2 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  EX (i: Z)  (j: Z)  (reps: (@list Z))  (retval: Z) ,
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (retval = 1) ” 
  &&  “ (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j ) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_entail_wit_4_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j_2: Z) (cur_i_2: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i_2)) (PreH19 : (cur_i_2 < n_pre)) (PreH20 : (0 <= cur_j_2)) (PreH21 : (cur_j_2 < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2 )) (PreH23 : (retval <> 0)) ,
  ((bi_pre) # Int  |-> (Znth 0 (cons ((i + 1 )) ((@nil Z))) 0))
  **  ((bj_pre) # Int  |-> (Znth 0 (cons ((j + 1 )) ((@nil Z))) 0))
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
|--
  EX (cur_j: Z)  (cur_i: Z) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi cur_i cur_j ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (cur_j_2: Z) (cur_i_2: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Znth 0 (cons ((j + 1 )) ((@nil Z))) 0) <= INT_MAX)) (PreH2 : ((Znth 0 (cons ((i + 1 )) ((@nil Z))) 0) <= INT_MAX)) (PreH3 : ((Znth 0 (cons ((j + 1 )) ((@nil Z))) 0) >= INT_MIN)) (PreH4 : ((Znth 0 (cons ((i + 1 )) ((@nil Z))) 0) >= INT_MIN)) (PreH5 : ((Zlength (reps)) = 256)) (PreH6 : (retval = 1)) (PreH7 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH8 : ((Zlength (ci_cells)) = 1)) (PreH9 : ((Zlength (cj_cells)) = 1)) (PreH10 : (lo < hi)) (PreH11 : (Pre rows )) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 300000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 8)) (PreH16 : (n_pre = (Zlength (rows)))) (PreH17 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi <= 1000000000)) (PreH22 : (0 <= cur_i_2)) (PreH23 : (cur_i_2 < n_pre)) (PreH24 : (0 <= cur_j_2)) (PreH25 : (cur_j_2 < n_pre)) (PreH26 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2 )) (PreH27 : (retval <> 0)) ,
  ((bi_pre) # Int  |-> (Znth 0 (cons ((i + 1 )) ((@nil Z))) 0))
  **  ((bj_pre) # Int  |-> (Znth 0 (cons ((j + 1 )) ((@nil Z))) 0))
  **  (IntArray.full rep_pre 256 reps )
|--
  EX (cur_j: Z)  (cur_i: Z) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) hi cur_i cur_j ) ”
  &&  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
).

Definition solver_entail_wit_4_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j_2: Z) (cur_i_2: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i_2)) (PreH19 : (cur_i_2 < n_pre)) (PreH20 : (0 <= cur_j_2)) (PreH21 : (cur_j_2 < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2 )) (PreH23 : (retval = 0)) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i_2 + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j_2 + 1 )) ((@nil Z))) )
|--
  EX (cur_j: Z)  (cur_i: Z) ,
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) cur_i cur_j ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
) \/
(
forall (rep_pre: Z) (m_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (cur_j_2: Z) (cur_i_2: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i_2)) (PreH19 : (cur_i_2 < n_pre)) (PreH20 : (0 <= cur_j_2)) (PreH21 : (cur_j_2 < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2 )) (PreH23 : (retval = 0)) ,
  (IntArray.full rep_pre 256 reps )
|--
  EX (cur_j: Z)  (cur_i: Z) ,
  “ ((cons ((cur_j_2 + 1 )) ((@nil Z))) = (cons ((cur_j + 1 )) ((@nil Z)))) ” 
  &&  “ ((cons ((cur_i_2 + 1 )) ((@nil Z))) = (cons ((cur_i + 1 )) ((@nil Z)))) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) cur_i cur_j ) ”
  &&  (IntArray.full_shape rep_pre 256 )
).

Definition solver_return_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows 0 i j )) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = 0)) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH16 : (0 <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : (0 <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : (0 <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.full bi_pre 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
|--
  EX (out: (Z * Z)) ,
  “ (Spec rows out ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((fst (out))) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((snd (out))) ((@nil Z))) )
) \/
(
forall (rep_pre: Z) (m_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows 0 i j )) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = 0)) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH16 : (0 <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : (0 <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : (0 <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.full rep_pre 256 reps )
|--
  EX (out: (Z * Z)) ,
  “ ((cons ((j + 1 )) ((@nil Z))) = (cons ((snd (out))) ((@nil Z)))) ” 
  &&  “ ((cons ((i + 1 )) ((@nil Z))) = (cons ((fst (out))) ((@nil Z)))) ” 
  &&  “ (Spec rows out ) ”
  &&  (IntArray.full_shape rep_pre 256 )
).

Definition solver_return_wit_2 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows 0 ))) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = 0)) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH16 : (0 <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : (0 <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : (0 <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
|--
  EX (out: (Z * Z)) ,
  “ (Spec rows out ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((fst (out))) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((snd (out))) ((@nil Z))) )
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows 0 ))) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = 0)) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH16 : (0 <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : (0 <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : (0 <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  (IntArray.full rep_pre 256 reps )
|--
  EX (out: (Z * Z)) ,
  “ (Spec rows out ) ”
  &&  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((fst (out))) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((snd (out))) ((@nil Z))) )
).

Definition solver_return_wit_3 := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo <> 0)) (PreH2 : (lo >= hi)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi <= 1000000000)) (PreH14 : (0 <= cur_i)) (PreH15 : (cur_i < n_pre)) (PreH16 : (0 <= cur_j)) (PreH17 : (cur_j < n_pre)) (PreH18 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  EX (out: (Z * Z)) ,
  “ (Spec rows out ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((fst (out))) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((snd (out))) ((@nil Z))) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo <> 0)) (PreH2 : (lo >= hi)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi <= 1000000000)) (PreH14 : (0 <= cur_i)) (PreH15 : (cur_i < n_pre)) (PreH16 : (0 <= cur_j)) (PreH17 : (cur_j < n_pre)) (PreH18 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  TT && emp 
|--
  EX (out: (Z * Z)) ,
  “ ((cons ((cur_j + 1 )) ((@nil Z))) = (cons ((snd (out))) ((@nil Z)))) ” 
  &&  “ ((cons ((cur_i + 1 )) ((@nil Z))) = (cons ((fst (out))) ((@nil Z)))) ” 
  &&  “ (Spec rows out ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (Pre rows )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.undef_full bi_pre 1 )
  **  (IntArray.undef_full bj_pre 1 )
|--
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= m_pre) /\ (m_pre <= 8))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ”
  &&  (IntArray.undef_full bi_pre 1 )
  **  (IntArray.undef_full bj_pre 1 )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
.

Definition solver_partial_solve_wit_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo < hi)) (PreH2 : (Pre rows )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : (0 <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : (0 <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_partial_solve_wit_3_pure := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z)))  __default__List_Z (PreH1 : ((Zlength (ci_cells)) = 1)) (PreH2 : ((Zlength (cj_cells)) = 1)) (PreH3 : (lo < hi)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 1000000000)) (PreH15 : (0 <= cur_i)) (PreH16 : (cur_i < n_pre)) (PreH17 : (0 <= cur_j)) (PreH18 : (cur_j < n_pre)) (PreH19 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z)))  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : (0 <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : (0 <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ”
).

Definition solver_partial_solve_wit_3_pure_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z)))  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : (0 <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : (0 <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition solver_partial_solve_wit_3_pure_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z)))  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : (0 <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : (0 <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 1000000000) ”
.

Definition solver_partial_solve_wit_3_pure_split_goal_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z)))  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : (0 <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : (0 <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z)))  __default__List_Z (PreH1 : ((Zlength (ci_cells)) = 1)) (PreH2 : ((Zlength (cj_cells)) = 1)) (PreH3 : (lo < hi)) (PreH4 : (Pre rows )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 1000000000)) (PreH15 : (0 <= cur_i)) (PreH16 : (cur_i < n_pre)) (PreH17 : (0 <= cur_j)) (PreH18 : (cur_j < n_pre)) (PreH19 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4_pure := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((cur_j + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((cur_i + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((j + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((i + 1 )) ((@nil Z))))) = 1) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : (0 <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : (0 <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH33 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((i + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((j + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((cur_i + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((cur_j + 1 )) ((@nil Z))))) = 1) ”
).

Definition solver_partial_solve_wit_4_pure_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : (0 <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : (0 <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH33 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((i + 1 )) ((@nil Z))))) = 1) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_2 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : (0 <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : (0 <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH33 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((j + 1 )) ((@nil Z))))) = 1) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_3 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : (0 <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : (0 <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH33 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((cur_i + 1 )) ((@nil Z))))) = 1) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_4 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH25 : (0 <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : (0 <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : (0 <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH33 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((cur_j + 1 )) ((@nil Z))))) = 1) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (i: Z) (j: Z) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j )) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval <> 0)) ,
  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength ((cons ((cur_j + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((cur_i + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((j + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength ((cons ((i + 1 )) ((@nil Z))))) = 1) ” 
  &&  “ ((Zlength (reps)) = 256) ” 
  &&  “ (retval = 1) ” 
  &&  “ (PairAtLeast rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) i j ) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full ( &( "ci" ) ) 1 (cons ((i + 1 )) ((@nil Z))) )
  **  (IntArray.full ( &( "cj" ) ) 1 (cons ((j + 1 )) ((@nil Z))) )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (cj_cells: (@list (@option Z))) (ci_cells: (@list (@option Z))) (reps: (@list Z)) (retval: Z)  __default__List_Z (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 0)) (PreH3 : ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) ))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH15 : (0 <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : (0 <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : (0 <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j )) (PreH23 : (retval = 0)) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ ((Zlength (reps)) = 256) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((FeasibleAtThreshold rows (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) )) ” 
  &&  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ” 
  &&  “ (lo < hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full rep_pre 256 reps )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
.

Definition solver_partial_solve_wit_6 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z)  __default__List_Z (PreH1 : (lo = 0)) (PreH2 : (lo >= hi)) (PreH3 : (Pre rows )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi <= 1000000000)) (PreH14 : (0 <= cur_i)) (PreH15 : (cur_i < n_pre)) (PreH16 : (0 <= cur_j)) (PreH17 : (cur_j < n_pre)) (PreH18 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
|--
  “ (lo = 0) ” 
  &&  “ (lo >= hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ”
  &&  (IntArray.full bi_pre 1 (cons ((cur_i + 1 )) ((@nil Z))) )
  **  (IntArray.full bj_pre 1 (cons ((cur_j + 1 )) ((@nil Z))) )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
.

Definition solver_partial_solve_wit_7_pure := 
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z)))  __default__List_Z (PreH1 : ((Zlength (bi_cells)) = 1)) (PreH2 : ((Zlength (bj_cells)) = 1)) (PreH3 : (lo = 0)) (PreH4 : (lo >= hi)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH13 : (0 <= lo)) (PreH14 : (lo <= hi)) (PreH15 : (hi <= 1000000000)) (PreH16 : (0 <= cur_i)) (PreH17 : (cur_i < n_pre)) (PreH18 : (0 <= cur_j)) (PreH19 : (cur_j < n_pre)) (PreH20 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (bi_cells)) = 1) ” 
  &&  “ ((Zlength (bj_cells)) = 1) ”
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z)))  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (hi >= INT_MIN)) (PreH6 : (lo >= INT_MIN)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : ((Zlength (bi_cells)) = 1)) (PreH10 : ((Zlength (bj_cells)) = 1)) (PreH11 : (lo = 0)) (PreH12 : (lo >= hi)) (PreH13 : (Pre rows )) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 300000)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 8)) (PreH18 : (n_pre = (Zlength (rows)))) (PreH19 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= hi)) (PreH23 : (hi <= 1000000000)) (PreH24 : (0 <= cur_i)) (PreH25 : (cur_i < n_pre)) (PreH26 : (0 <= cur_j)) (PreH27 : (cur_j < n_pre)) (PreH28 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ”
).

Definition solver_partial_solve_wit_7_pure_split_goal_1 := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z)))  __default__List_Z (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (hi >= INT_MIN)) (PreH6 : (lo >= INT_MIN)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : ((Zlength (bi_cells)) = 1)) (PreH10 : ((Zlength (bj_cells)) = 1)) (PreH11 : (lo = 0)) (PreH12 : (lo >= hi)) (PreH13 : (Pre rows )) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 300000)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 8)) (PreH18 : (n_pre = (Zlength (rows)))) (PreH19 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH21 : (0 <= lo)) (PreH22 : (lo <= hi)) (PreH23 : (hi <= 1000000000)) (PreH24 : (0 <= cur_i)) (PreH25 : (cur_i < n_pre)) (PreH26 : (0 <= cur_j)) (PreH27 : (cur_j < n_pre)) (PreH28 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "rep" ) )) # Ptr  |-> rep_pre)
  **  ((( &( "bi" ) )) # Ptr  |-> bi_pre)
  **  ((( &( "bj" ) )) # Ptr  |-> bj_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ”
.

Definition solver_partial_solve_wit_7_aux := 
forall (bj_pre: Z) (bi_pre: Z) (rep_pre: Z) (m_pre: Z) (n_pre: Z) (a_pre: Z) (rows: (@list (@list Z))) (cur_j: Z) (cur_i: Z) (hi: Z) (lo: Z) (bj_cells: (@list (@option Z))) (bi_cells: (@list (@option Z)))  __default__List_Z (PreH1 : ((Zlength (bi_cells)) = 1)) (PreH2 : ((Zlength (bj_cells)) = 1)) (PreH3 : (lo = 0)) (PreH4 : (lo >= hi)) (PreH5 : (Pre rows )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth 0 rows __default__List_Z))))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000)))) (PreH13 : (0 <= lo)) (PreH14 : (lo <= hi)) (PreH15 : (hi <= 1000000000)) (PreH16 : (0 <= cur_i)) (PreH17 : (cur_i < n_pre)) (PreH18 : (0 <= cur_j)) (PreH19 : (cur_j < n_pre)) (PreH20 : (SolverSearchMeaning rows lo hi cur_i cur_j )) ,
  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
  **  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
|--
  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre * m_pre ))) -> ((0 <= (Znth k (concat (rows)) 0)) /\ ((Znth k (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ ((Zlength (bi_cells)) = 1) ” 
  &&  “ ((Zlength (bj_cells)) = 1) ” 
  &&  “ ((Zlength (bi_cells)) = 1) ” 
  &&  “ ((Zlength (bj_cells)) = 1) ” 
  &&  “ (lo = 0) ” 
  &&  “ (lo >= hi) ” 
  &&  “ (Pre rows ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 300000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 8) ” 
  &&  “ (n_pre = (Zlength (rows))) ” 
  &&  “ (m_pre = (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre * m_pre ))) -> ((0 <= (Znth k_2 (concat (rows)) 0)) /\ ((Znth k_2 (concat (rows)) 0) <= 1000000000))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi <= 1000000000) ” 
  &&  “ (0 <= cur_i) ” 
  &&  “ (cur_i < n_pre) ” 
  &&  “ (0 <= cur_j) ” 
  &&  “ (cur_j < n_pre) ” 
  &&  “ (SolverSearchMeaning rows lo hi cur_i cur_j ) ”
  &&  (IntArray2.full a_pre n_pre m_pre rows )
  **  (IntArray.full_shape rep_pre 256 )
  **  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Definition solver_which_implies_wit_1 := 
(
forall (bj_pre: Z) (bi_pre: Z) ,
  (IntArray.undef_full bi_pre 1 )
  **  (IntArray.undef_full bj_pre 1 )
|--
  ((bi_pre) # Int  |->_)
  **  ((bj_pre) # Int  |->_)
) \/
(
forall (bj_pre: Z) (bi_pre: Z) ,
  (IntArray.undef_full bi_pre 1 )
  **  (IntArray.undef_full bj_pre 1 )
|--
  EX (x_2: Z)  (x: Z) ,
  ((bj_pre) # Int  |-> x_2)
  **  ((bi_pre) # Int  |-> x)
).

Definition solver_which_implies_wit_2 := 
(
  ((( &( "ci" ) )) # Int  |->_)
  **  ((( &( "cj" ) )) # Int  |->_)
|--
  EX (cj_cells: (@list (@option Z)))  (ci_cells: (@list (@option Z))) ,
  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ”
  &&  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
) \/
(
  ((( &( "ci" ) )) # Int  |->_)
  **  ((( &( "cj" ) )) # Int  |->_)
|--
  EX (cj_cells: (@list (@option Z)))  (ci_cells: (@list (@option Z))) ,
  “ ((Zlength (ci_cells)) = 1) ” 
  &&  “ ((Zlength (cj_cells)) = 1) ”
  &&  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_cells )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_cells )
).

Definition solver_which_implies_wit_3 := 
(
forall (bj_pre: Z) (bi_pre: Z) (old_js: (@list Z)) (old_is: (@list Z)) (cj_values: (@list Z)) (ci_values: (@list Z)) (PreH1 : ((Zlength (ci_values)) = 1)) (PreH2 : ((Zlength (cj_values)) = 1)) (PreH3 : ((Zlength (old_is)) = 1)) (PreH4 : ((Zlength (old_js)) = 1)) ,
  (IntArray.full ( &( "ci" ) ) 1 ci_values )
  **  (IntArray.full ( &( "cj" ) ) 1 cj_values )
  **  (IntArray.full bi_pre 1 old_is )
  **  (IntArray.full bj_pre 1 old_js )
|--
  ((( &( "ci" ) )) # Int  |-> (Znth 0 ci_values 0))
  **  ((( &( "cj" ) )) # Int  |-> (Znth 0 cj_values 0))
  **  ((bi_pre) # Int  |-> (Znth 0 old_is 0))
  **  ((bj_pre) # Int  |-> (Znth 0 old_js 0))
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (old_js: (@list Z)) (old_is: (@list Z)) (cj_values: (@list Z)) (ci_values: (@list Z)) (PreH1 : ((Zlength (ci_values)) = 1)) (PreH2 : ((Zlength (cj_values)) = 1)) (PreH3 : ((Zlength (old_is)) = 1)) (PreH4 : ((Zlength (old_js)) = 1)) ,
  (IntArray.full ( &( "ci" ) ) 1 ci_values )
  **  (IntArray.full ( &( "cj" ) ) 1 cj_values )
  **  (IntArray.full bi_pre 1 old_is )
  **  (IntArray.full bj_pre 1 old_js )
|--
  ((( &( "ci" ) )) # Int  |-> (Znth 0 ci_values 0))
  **  ((( &( "cj" ) )) # Int  |-> (Znth 0 cj_values 0))
  **  ((bi_pre) # Int  |-> (Znth 0 old_is 0))
  **  ((bj_pre) # Int  |-> (Znth 0 old_js 0))
).

Definition solver_which_implies_wit_3_split_goal_spatial := 
forall (bj_pre: Z) (bi_pre: Z) (old_js: (@list Z)) (old_is: (@list Z)) (cj_values: (@list Z)) (ci_values: (@list Z)) (PreH1 : ((Zlength (ci_values)) = 1)) (PreH2 : ((Zlength (cj_values)) = 1)) (PreH3 : ((Zlength (old_is)) = 1)) (PreH4 : ((Zlength (old_js)) = 1)) ,
  (IntArray.full ( &( "ci" ) ) 1 ci_values )
  **  (IntArray.full ( &( "cj" ) ) 1 cj_values )
  **  (IntArray.full bi_pre 1 old_is )
  **  (IntArray.full bj_pre 1 old_js )
|--
  ((( &( "ci" ) )) # Int  |-> (Znth 0 ci_values 0))
  **  ((( &( "cj" ) )) # Int  |-> (Znth 0 cj_values 0))
  **  ((bi_pre) # Int  |-> (Znth 0 old_is 0))
  **  ((bj_pre) # Int  |-> (Znth 0 old_js 0))
.

Definition solver_which_implies_wit_4 := 
(
forall (cj_values: (@list (@option Z))) (ci_values: (@list (@option Z))) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_values )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_values )
|--
  ((( &( "ci" ) )) # Int  |->_)
  **  ((( &( "cj" ) )) # Int  |->_)
) \/
(
forall (cj_values: (@list (@option Z))) (ci_values: (@list (@option Z))) ,
  (IntArray.mixed_full ( &( "ci" ) ) 1 ci_values )
  **  (IntArray.mixed_full ( &( "cj" ) ) 1 cj_values )
|--
  EX (x_2: Z)  (x: Z) ,
  ((( &( "cj" ) )) # Int  |-> x_2)
  **  ((( &( "ci" ) )) # Int  |-> x)
).

Definition solver_which_implies_wit_5 := 
(
forall (bj_pre: Z) (bi_pre: Z) (bj_values: (@list Z)) (bi_values: (@list Z)) ,
  (IntArray.full bi_pre 1 bi_values )
  **  (IntArray.full bj_pre 1 bj_values )
|--
  EX (bj_cells: (@list (@option Z)))  (bi_cells: (@list (@option Z))) ,
  “ ((Zlength (bi_cells)) = 1) ” 
  &&  “ ((Zlength (bj_cells)) = 1) ”
  &&  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
) \/
(
forall (bj_pre: Z) (bi_pre: Z) (bj_values: (@list Z)) (bi_values: (@list Z)) ,
  (IntArray.full bi_pre 1 bi_values )
  **  (IntArray.full bj_pre 1 bj_values )
|--
  EX (bj_cells: (@list (@option Z)))  (bi_cells: (@list (@option Z))) ,
  “ ((Zlength (bi_cells)) = 1) ” 
  &&  “ ((Zlength (bj_cells)) = 1) ”
  &&  (IntArray.mixed_full bi_pre 1 bi_cells )
  **  (IntArray.mixed_full bj_pre 1 bj_cells )
).

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_feasible_safety_wit_1 : feasible_safety_wit_1.
Axiom proof_of_feasible_safety_wit_2 : feasible_safety_wit_2.
Axiom proof_of_feasible_safety_wit_3 : feasible_safety_wit_3.
Axiom proof_of_feasible_safety_wit_4 : feasible_safety_wit_4.
Axiom proof_of_feasible_safety_wit_5 : feasible_safety_wit_5.
Axiom proof_of_feasible_safety_wit_6 : feasible_safety_wit_6.
Axiom proof_of_feasible_safety_wit_7 : feasible_safety_wit_7.
Axiom proof_of_feasible_safety_wit_8 : feasible_safety_wit_8.
Axiom proof_of_feasible_safety_wit_9 : feasible_safety_wit_9.
Axiom proof_of_feasible_safety_wit_10 : feasible_safety_wit_10.
Axiom proof_of_feasible_safety_wit_11 : feasible_safety_wit_11.
Axiom proof_of_feasible_safety_wit_12 : feasible_safety_wit_12.
Axiom proof_of_feasible_safety_wit_13 : feasible_safety_wit_13.
Axiom proof_of_feasible_safety_wit_14 : feasible_safety_wit_14.
Axiom proof_of_feasible_safety_wit_15 : feasible_safety_wit_15.
Axiom proof_of_feasible_safety_wit_16 : feasible_safety_wit_16.
Axiom proof_of_feasible_safety_wit_17 : feasible_safety_wit_17.
Axiom proof_of_feasible_safety_wit_18 : feasible_safety_wit_18.
Axiom proof_of_feasible_safety_wit_19 : feasible_safety_wit_19.
Axiom proof_of_feasible_safety_wit_20 : feasible_safety_wit_20.
Axiom proof_of_feasible_safety_wit_21 : feasible_safety_wit_21.
Axiom proof_of_feasible_safety_wit_22 : feasible_safety_wit_22.
Axiom proof_of_feasible_safety_wit_23 : feasible_safety_wit_23.
Axiom proof_of_feasible_safety_wit_24 : feasible_safety_wit_24.
Axiom proof_of_feasible_safety_wit_25 : feasible_safety_wit_25.
Axiom proof_of_feasible_safety_wit_26 : feasible_safety_wit_26.
Axiom proof_of_feasible_safety_wit_27 : feasible_safety_wit_27.
Axiom proof_of_feasible_safety_wit_28 : feasible_safety_wit_28.
Axiom proof_of_feasible_safety_wit_29 : feasible_safety_wit_29.
Axiom proof_of_feasible_safety_wit_30 : feasible_safety_wit_30.
Axiom proof_of_feasible_safety_wit_31 : feasible_safety_wit_31.
Axiom proof_of_feasible_safety_wit_32 : feasible_safety_wit_32.
Axiom proof_of_feasible_safety_wit_33 : feasible_safety_wit_33.
Axiom proof_of_feasible_safety_wit_34 : feasible_safety_wit_34.
Axiom proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Axiom proof_of_feasible_entail_wit_2 : feasible_entail_wit_2.
Axiom proof_of_feasible_entail_wit_3 : feasible_entail_wit_3.
Axiom proof_of_feasible_entail_wit_4 : feasible_entail_wit_4.
Axiom proof_of_feasible_entail_wit_5_1 : feasible_entail_wit_5_1.
Axiom proof_of_feasible_entail_wit_5_2 : feasible_entail_wit_5_2.
Axiom proof_of_feasible_entail_wit_6_1 : feasible_entail_wit_6_1.
Axiom proof_of_feasible_entail_wit_6_2 : feasible_entail_wit_6_2.
Axiom proof_of_feasible_entail_wit_7 : feasible_entail_wit_7.
Axiom proof_of_feasible_entail_wit_8 : feasible_entail_wit_8.
Axiom proof_of_feasible_entail_wit_9_1 : feasible_entail_wit_9_1.
Axiom proof_of_feasible_entail_wit_9_2 : feasible_entail_wit_9_2.
Axiom proof_of_feasible_entail_wit_10_1 : feasible_entail_wit_10_1.
Axiom proof_of_feasible_entail_wit_10_2 : feasible_entail_wit_10_2.
Axiom proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Axiom proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Axiom proof_of_feasible_partial_solve_wit_1 : feasible_partial_solve_wit_1.
Axiom proof_of_feasible_partial_solve_wit_2 : feasible_partial_solve_wit_2.
Axiom proof_of_feasible_partial_solve_wit_3 : feasible_partial_solve_wit_3.
Axiom proof_of_feasible_partial_solve_wit_4 : feasible_partial_solve_wit_4.
Axiom proof_of_feasible_partial_solve_wit_5 : feasible_partial_solve_wit_5.
Axiom proof_of_feasible_partial_solve_wit_6 : feasible_partial_solve_wit_6.
Axiom proof_of_feasible_partial_solve_wit_7 : feasible_partial_solve_wit_7.
Axiom proof_of_feasible_partial_solve_wit_8 : feasible_partial_solve_wit_8.
Axiom proof_of_feasible_partial_solve_wit_9 : feasible_partial_solve_wit_9.
Axiom proof_of_feasible_which_implies_wit_1 : feasible_which_implies_wit_1.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Axiom proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2.
Axiom proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3.
Axiom proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4.
Axiom proof_of_solver_which_implies_wit_5 : solver_which_implies_wit_5.

End VC_Correct.
