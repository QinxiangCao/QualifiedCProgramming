import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P066_1288D_minimax_problem_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def feasible_safety_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1)) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1)) ”
)

noncomputable def feasible_safety_wit_1_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) <= INT_MAX) ”

noncomputable def feasible_safety_wit_1_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1)) ”

noncomputable def feasible_safety_wit_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((signed_last_nbits ((1 * (2 ^ m_pre))) (32)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2 ^ m_pre))) (32))) ” &&
  “ (m_pre <= 31) ” &&
  “ ((0 : Int) <= m_pre) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((signed_last_nbits ((1 * (2 ^ m_pre))) (32)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2 ^ m_pre))) (32))) ” &&
  “ (m_pre <= 31) ” &&
  “ ((0 : Int) <= m_pre) ”
)

noncomputable def feasible_safety_wit_2_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((signed_last_nbits ((1 * (2 ^ m_pre))) (32)) <= INT_MAX) ”

noncomputable def feasible_safety_wit_2_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2 ^ m_pre))) (32))) ”

noncomputable def feasible_safety_wit_2_split_goal_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (m_pre <= 31) ”

noncomputable def feasible_safety_wit_2_split_goal_4 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= m_pre) ”

noncomputable def feasible_safety_wit_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_4 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "full" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_5 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  ((( &( "s" ) )) # Int |->_)
  ** ((( &( "full" ) )) # Int |-> (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_6 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps (0 : Int)) = (-1)))) ,
  (intArray.full rep_pre 256 (replace_Znth (s) ((-1)) (reps)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((s + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s + 1)) ”

noncomputable def feasible_safety_wit_7 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps (0 : Int)) = (-1)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def feasible_safety_wit_8 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps (0 : Int)) = (-1)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_9 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps (0 : Int)) = (-1)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_10 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  ((( &( "mask" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_11 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "mask" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_12 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (j < m_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= m_pre)) (PreH20 : ((0 : Int) <= ((i * m_pre) + j))) (PreH21 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH22 : ((0 : Int) <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH26 : (RowMaskPrefix rows x_pre i j mask)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (((i * m_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * m_pre) + j)) ”

noncomputable def feasible_safety_wit_13 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (j < m_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= m_pre)) (PreH20 : ((0 : Int) <= ((i * m_pre) + j))) (PreH21 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH22 : ((0 : Int) <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH26 : (RowMaskPrefix rows x_pre i j mask)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((i * m_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * m_pre)) ”

noncomputable def feasible_safety_wit_14 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((signed_last_nbits ((1 * (2 ^ j))) (32)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2 ^ j))) (32))) ” &&
  “ (j <= 31) ” &&
  “ ((0 : Int) <= j) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((signed_last_nbits ((1 * (2 ^ j))) (32)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2 ^ j))) (32))) ” &&
  “ (j <= 31) ” &&
  “ ((0 : Int) <= j) ”
)

noncomputable def feasible_safety_wit_14_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((signed_last_nbits ((1 * (2 ^ j))) (32)) <= INT_MAX) ”

noncomputable def feasible_safety_wit_14_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2 ^ j))) (32))) ”

noncomputable def feasible_safety_wit_14_split_goal_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (j <= 31) ”

noncomputable def feasible_safety_wit_14_split_goal_4 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= j) ”

noncomputable def feasible_safety_wit_15 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_16 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def feasible_safety_wit_17 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) < x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def feasible_safety_wit_18 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (j >= m_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= m_pre)) (PreH20 : ((0 : Int) <= ((i * m_pre) + j))) (PreH21 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH22 : ((0 : Int) <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH26 : (RowMaskPrefix rows x_pre i j mask)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "mask" ) )) # Int |-> (mask))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_19 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (intArray.full rep_pre 256 (replace_Znth (mask) (i) (reps)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def feasible_safety_wit_20 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps (0 : Int)) >= (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def feasible_safety_wit_21 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH20 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  ((( &( "s" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_22 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH20 : (NoCoverPrefix reps full s (0 : Int))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_23 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps (0 : Int)) >= (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH21 : (NoCoverPrefix reps full s (0 : Int))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  ((( &( "u" ) )) # Int |->_)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_24 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH22 : ((Znth s reps (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH24 : (NoCoverPrefix reps full s u)) (PreH25 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_safety_wit_25 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ (((Znth s reps (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth s reps (0 : Int)) + 1)) ”

noncomputable def feasible_safety_wit_26 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_27 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((bi_pre) # Int |-> (((Znth s reps (0 : Int)) + 1)))
  ** ((bj_pre) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ (((Znth u reps (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth u reps (0 : Int)) + 1)) ”

noncomputable def feasible_safety_wit_28 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((bi_pre) # Int |-> (((Znth s reps (0 : Int)) + 1)))
  ** ((bj_pre) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_29 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((bi_pre) # Int |-> (((Znth s reps (0 : Int)) + 1)))
  ** ((bj_pre) # Int |-> (((Znth u reps (0 : Int)) + 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def feasible_safety_wit_30 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH22 : ((Znth s reps (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH24 : (NoCoverPrefix reps full s u)) (PreH25 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((s + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s + 1)) ”

noncomputable def feasible_safety_wit_31 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps (0 : Int)) < (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH21 : (NoCoverPrefix reps full s (0 : Int))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((s + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s + 1)) ”

noncomputable def feasible_safety_wit_32 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth u reps (0 : Int)) < (0 : Int))) (PreH2 : (u <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= full)) (PreH19 : ((0 : Int) <= u)) (PreH20 : (u <= (full + 1))) (PreH21 : ((Zlength (reps)) = 256)) (PreH22 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH23 : ((Znth s reps (0 : Int)) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH25 : (NoCoverPrefix reps full s u)) (PreH26 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((u + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (u + 1)) ”

noncomputable def feasible_safety_wit_33 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) ≠ full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((u + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (u + 1)) ”

noncomputable def feasible_safety_wit_34 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH20 : (NoCoverPrefix reps full s (0 : Int))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "full" ) )) # Int |-> (full))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def feasible_entail_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1)) ” &&
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) <= 255) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (0 : Int))) -> ((Znth q reps (0 : Int)) = (-1))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 8)) (PreH6 : ((0 : Int) <= x_pre)) (PreH7 : (x_pre <= 1000000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) ,
  (intArray.full_shape rep_pre 256)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= ((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1)) ” &&
  “ (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) <= 255) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (((signed_last_nbits ((Z.shiftl 1 m_pre)) (32)) - 1) + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (0 : Int))) -> ((Znth q reps (0 : Int)) = (-1))) ”
  &&  (intArray.full rep_pre 256 reps)
)

noncomputable def feasible_entail_wit_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps_2 (0 : Int)) = (-1)))) ,
  (intArray.full rep_pre 256 (replace_Znth (s) ((-1)) (reps_2)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (s + 1)) ” &&
  “ ((s + 1) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (s + 1))) -> ((Znth q reps (0 : Int)) = (-1))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps_2 (0 : Int)) = (-1)))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (s) ((-1)) (reps_2)))) = 256) ”
  &&  emp
)

noncomputable def feasible_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps_2 (0 : Int)) = (-1)))) ,
  ((Zlength ((replace_Znth (s) ((-1)) (reps_2)))) = 256)

noncomputable def feasible_entail_wit_3 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < s)) -> ((Znth q_2 reps_2 (0 : Int)) = (-1)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre (0 : Int) reps) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < (0 : Int)))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < s)) -> ((Znth q_2 reps_2 (0 : Int)) = (-1)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < (0 : Int)))) ” &&
  “ (RepresentativePrefix rows x_pre m_pre (0 : Int) reps_2) ”
  &&  emp
)

noncomputable def feasible_entail_wit_3_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < s)) -> ((Znth q_2 reps_2 (0 : Int)) = (-1)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < (0 : Int))))

noncomputable def feasible_entail_wit_3_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < s)) -> ((Znth q_2 reps_2 (0 : Int)) = (-1)))) ,
  (RepresentativePrefix rows x_pre m_pre (0 : Int) reps_2)

noncomputable def feasible_entail_wit_4 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((0 : Int) <= ((i * m_pre) + (0 : Int))) ” &&
  “ (((i * m_pre) + (0 : Int)) <= (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre i reps) ” &&
  “ (RowMaskPrefix rows x_pre i (0 : Int) (0 : Int)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i))) ” &&
  “ (RowMaskPrefix rows x_pre i (0 : Int) (0 : Int)) ” &&
  “ (((i * m_pre) + (0 : Int)) <= (n_pre * m_pre)) ”
  &&  emp
)

noncomputable def feasible_entail_wit_4_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))

noncomputable def feasible_entail_wit_4_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (RowMaskPrefix rows x_pre i (0 : Int) (0 : Int))

noncomputable def feasible_entail_wit_4_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (((i * m_pre) + (0 : Int)) <= (n_pre * m_pre))

noncomputable def feasible_entail_wit_5_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= m_pre) ” &&
  “ ((0 : Int) <= ((i * m_pre) + (j + 1))) ” &&
  “ (((i * m_pre) + (j + 1)) <= (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ” &&
  “ ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) <= full) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre i reps) ” &&
  “ (RowMaskPrefix rows x_pre i (j + 1) (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ (RowMaskPrefix rows x_pre i (j + 1) (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ” &&
  “ ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) <= ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ” &&
  “ (((i * m_pre) + (j + 1)) <= (n_pre * m_pre)) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
)

noncomputable def feasible_entail_wit_5_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ (RowMaskPrefix rows x_pre i (j + 1) (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ”

noncomputable def feasible_entail_wit_5_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ ((Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32))) <= ((Z.shiftl 1 m_pre) - 1)) ”

noncomputable def feasible_entail_wit_5_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ ((0 : Int) <= (Z.lor mask (signed_last_nbits ((Z.shiftl 1 j)) (32)))) ”

noncomputable def feasible_entail_wit_5_1_split_goal_4 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ (((i * m_pre) + (j + 1)) <= (n_pre * m_pre)) ”

noncomputable def feasible_entail_wit_5_1_split_goal_spatial : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  (intArray2.full a_pre n_pre m_pre rows)

noncomputable def feasible_entail_wit_5_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) < x_pre)) (PreH2 : (j < m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= m_pre) ” &&
  “ ((0 : Int) <= ((i * m_pre) + (j + 1))) ” &&
  “ (((i * m_pre) + (j + 1)) <= (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= mask) ” &&
  “ (mask <= full) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre i reps) ” &&
  “ (RowMaskPrefix rows x_pre i (j + 1) mask) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ (RowMaskPrefix rows x_pre i (j + 1) mask) ” &&
  “ (((i * m_pre) + (j + 1)) <= (n_pre * m_pre)) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
)

noncomputable def feasible_entail_wit_5_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ (RowMaskPrefix rows x_pre i (j + 1) mask) ”

noncomputable def feasible_entail_wit_5_2_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  “ (((i * m_pre) + (j + 1)) <= (n_pre * m_pre)) ”

noncomputable def feasible_entail_wit_5_2_split_goal_spatial : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int))) < x_pre)) (PreH4 : (j < m_pre)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : ((0 : Int) <= x_pre)) (PreH11 : (x_pre <= 1000000000)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : ((Zlength (old_bi)) = 1)) (PreH15 : ((Zlength (old_bj)) = 1)) (PreH16 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH17 : ((0 : Int) <= full)) (PreH18 : (full <= 255)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < n_pre)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= m_pre)) (PreH23 : ((0 : Int) <= ((i * m_pre) + j))) (PreH24 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH25 : ((0 : Int) <= mask)) (PreH26 : (mask <= full)) (PreH27 : ((Zlength (reps_2)) = 256)) (PreH28 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH29 : (RowMaskPrefix rows x_pre i j mask)) (PreH30 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < i)))) ,
  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
|--
  (intArray2.full a_pre n_pre m_pre rows)

noncomputable def feasible_entail_wit_6_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (intArray.full rep_pre 256 (replace_Znth (mask) (i) (reps_2)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre (i + 1) reps) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < (i + 1)))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q (replace_Znth (mask) (i) (reps_2)) (0 : Int))) ∧ ((Znth q (replace_Znth (mask) (i) (reps_2)) (0 : Int)) < (i + 1)))) ” &&
  “ (RepresentativePrefix rows x_pre m_pre (i + 1) (replace_Znth (mask) (i) (reps_2))) ” &&
  “ ((Zlength ((replace_Znth (mask) (i) (reps_2)))) = 256) ”
  &&  emp
)

noncomputable def feasible_entail_wit_6_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q (replace_Znth (mask) (i) (reps_2)) (0 : Int))) ∧ ((Znth q (replace_Znth (mask) (i) (reps_2)) (0 : Int)) < (i + 1))))

noncomputable def feasible_entail_wit_6_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (RepresentativePrefix rows x_pre m_pre (i + 1) (replace_Znth (mask) (i) (reps_2)))

noncomputable def feasible_entail_wit_6_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  ((Zlength ((replace_Znth (mask) (i) (reps_2)))) = 256)

noncomputable def feasible_entail_wit_6_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (intArray.full rep_pre 256 reps_2)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre (i + 1) reps) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < (i + 1)))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < (i + 1)))) ” &&
  “ (RepresentativePrefix rows x_pre m_pre (i + 1) reps_2) ”
  &&  emp
)

noncomputable def feasible_entail_wit_6_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < (i + 1))))

noncomputable def feasible_entail_wit_6_2_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps_2)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (RepresentativePrefix rows x_pre m_pre (i + 1) reps_2)

noncomputable def feasible_entail_wit_7 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full (0 : Int) (0 : Int)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre))) ” &&
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) (0 : Int) (0 : Int)) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps_2) ”
  &&  emp
)

noncomputable def feasible_entail_wit_7_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))

noncomputable def feasible_entail_wit_7_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) (0 : Int) (0 : Int))

noncomputable def feasible_entail_wit_7_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i <= n_pre)) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre i reps_2)) (PreH20 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < i)))) ,
  (RepresentativePrefix rows x_pre m_pre n_pre reps_2)

noncomputable def feasible_entail_wit_8 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH21 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH22 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps_2)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s (0 : Int)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH21 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH22 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre))) ”
  &&  emp
)

noncomputable def feasible_entail_wit_8_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps_2 (0 : Int)) >= (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH21 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH22 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))

noncomputable def feasible_entail_wit_9_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH22 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH24 : (NoCoverPrefix reps_2 full s u)) (PreH25 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (s + 1)) ” &&
  “ ((s + 1) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full (s + 1) (0 : Int)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH22 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH24 : (NoCoverPrefix reps_2 full s u)) (PreH25 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre))) ” &&
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) (s + 1) (0 : Int)) ”
  &&  emp
)

noncomputable def feasible_entail_wit_9_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH22 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH24 : (NoCoverPrefix reps_2 full s u)) (PreH25 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))

noncomputable def feasible_entail_wit_9_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps_2)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH22 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH24 : (NoCoverPrefix reps_2 full s u)) (PreH25 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 <= full)) -> (((-1) <= (Znth q_2 reps_2 (0 : Int))) ∧ ((Znth q_2 reps_2 (0 : Int)) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) (s + 1) (0 : Int))

noncomputable def feasible_entail_wit_9_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH21 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps_2)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= (s + 1)) ” &&
  “ ((s + 1) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full (s + 1) (0 : Int)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH21 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) (s + 1) (0 : Int)) ”
  &&  emp
)

noncomputable def feasible_entail_wit_9_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth s reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (s <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= (full + 1))) (PreH19 : ((Zlength (reps_2)) = 256)) (PreH20 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH21 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH22 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) (s + 1) (0 : Int))

noncomputable def feasible_entail_wit_10_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth u reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (u <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= full)) (PreH19 : ((0 : Int) <= u)) (PreH20 : (u <= (full + 1))) (PreH21 : ((Zlength (reps_2)) = 256)) (PreH22 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH23 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH25 : (NoCoverPrefix reps_2 full s u)) (PreH26 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps_2)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= (u + 1)) ” &&
  “ ((u + 1) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s (u + 1)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth u reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (u <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= full)) (PreH19 : ((0 : Int) <= u)) (PreH20 : (u <= (full + 1))) (PreH21 : ((Zlength (reps_2)) = 256)) (PreH22 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH23 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH25 : (NoCoverPrefix reps_2 full s u)) (PreH26 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) s (u + 1)) ”
  &&  emp
)

noncomputable def feasible_entail_wit_10_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth u reps_2 (0 : Int)) < (0 : Int))) (PreH2 : (u <= full)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= s)) (PreH18 : (s <= full)) (PreH19 : ((0 : Int) <= u)) (PreH20 : (u <= (full + 1))) (PreH21 : ((Zlength (reps_2)) = 256)) (PreH22 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH23 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH24 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH25 : (NoCoverPrefix reps_2 full s u)) (PreH26 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) s (u + 1))

noncomputable def feasible_entail_wit_10_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) ≠ full)) (PreH2 : ((Znth u reps_2 (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH24 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH26 : (NoCoverPrefix reps_2 full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps_2)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= (u + 1)) ” &&
  “ ((u + 1) <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s (u + 1)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) ≠ full)) (PreH2 : ((Znth u reps_2 (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH24 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH26 : (NoCoverPrefix reps_2 full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) s (u + 1)) ”
  &&  emp
)

noncomputable def feasible_entail_wit_10_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) ≠ full)) (PreH2 : ((Znth u reps_2 (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH24 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH26 : (NoCoverPrefix reps_2 full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (NoCoverPrefix reps_2 ((Z.shiftl 1 m_pre) - 1) s (u + 1))

noncomputable def feasible_return_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH20 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX reps : (List Int),
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((FeasibleAtThreshold rows x_pre)) ”
  &&  (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
) \/
(
forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH20 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ ¬((FeasibleAtThreshold rows x_pre)) ”
  &&  emp
)

noncomputable def feasible_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s > full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps_2)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH20 : (NoCoverPrefix reps_2 full s (0 : Int))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  ¬((FeasibleAtThreshold rows x_pre))

noncomputable def feasible_return_wit_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps_2 (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps_2)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH24 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH26 : (NoCoverPrefix reps_2 full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps_2)
  ** ((bi_pre) # Int |-> (((Znth s reps_2 (0 : Int)) + 1)))
  ** ((bj_pre) # Int |-> (((Znth u reps_2 (0 : Int)) + 1)))
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  EX i : Int, EX j : Int, EX reps : (List Int),
  “ ((Zlength (reps)) = 256) ” &&
  “ (1 = 1) ” &&
  “ (PairAtLeast rows x_pre i j) ”
  &&  (intArray.full bi_pre 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps_2 : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (((Znth u reps_2 (0 : Int)) + 1) <= INT_MAX)) (PreH2 : (((Znth s reps_2 (0 : Int)) + 1) <= INT_MAX)) (PreH3 : (((Znth u reps_2 (0 : Int)) + 1) >= INT_MIN)) (PreH4 : (((Znth s reps_2 (0 : Int)) + 1) >= INT_MIN)) (PreH5 : ((Z.lor s u) = full)) (PreH6 : ((Znth u reps_2 (0 : Int)) >= (0 : Int))) (PreH7 : (u <= full)) (PreH8 : (Pre rows)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : ((0 : Int) <= x_pre)) (PreH14 : (x_pre <= 1000000000)) (PreH15 : (n_pre = (Zlength (rows)))) (PreH16 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH17 : ((Zlength (old_bi)) = 1)) (PreH18 : ((Zlength (old_bj)) = 1)) (PreH19 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH20 : ((0 : Int) <= full)) (PreH21 : (full <= 255)) (PreH22 : ((0 : Int) <= s)) (PreH23 : (s <= full)) (PreH24 : ((0 : Int) <= u)) (PreH25 : (u <= (full + 1))) (PreH26 : ((Zlength (reps_2)) = 256)) (PreH27 : ((0 : Int) <= (Znth s reps_2 (0 : Int)))) (PreH28 : ((Znth s reps_2 (0 : Int)) < n_pre)) (PreH29 : (RepresentativePrefix rows x_pre m_pre n_pre reps_2)) (PreH30 : (NoCoverPrefix reps_2 full s u)) (PreH31 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps_2 (0 : Int))) ∧ ((Znth q reps_2 (0 : Int)) < n_pre)))) ,
  ((bi_pre) # Int |-> (((Znth s reps_2 (0 : Int)) + 1)))
  ** ((bj_pre) # Int |-> (((Znth u reps_2 (0 : Int)) + 1)))
|--
  EX i : Int, EX j : Int,
  “ ((Zlength (reps_2)) = 256) ” &&
  “ (PairAtLeast rows x_pre i j) ”
  &&  (intArray.full bi_pre 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((j + 1) :: (@List.nil Int)))
)

noncomputable def feasible_partial_solve_wit_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps (0 : Int)) = (-1)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (s <= full) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < s)) -> ((Znth q reps (0 : Int)) = (-1))) ”
  &&  (((rep_pre + (s * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i rep_pre s (0 : Int) 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)

noncomputable def feasible_partial_solve_wit_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (j < m_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= m_pre)) (PreH20 : ((0 : Int) <= ((i * m_pre) + j))) (PreH21 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH22 : ((0 : Int) <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH26 : (RowMaskPrefix rows x_pre i j mask)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (j < m_pre) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= m_pre) ” &&
  “ ((0 : Int) <= ((i * m_pre) + j)) ” &&
  “ (((i * m_pre) + j) <= (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= mask) ” &&
  “ (mask <= full) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre i reps) ” &&
  “ (RowMaskPrefix rows x_pre i j mask) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i))) ”
  &&  (((a_pre + (((i * m_pre) + j) * sizeof(INT)))) # Int |-> ((Znth (j) ((Znth i rows __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (a_pre + ((i * m_pre) * sizeof(INT))) j (0 : Int) m_pre (Znth i rows __default__List_Z))
  ** (intArray2.missing_i a_pre i (0 : Int) n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)

noncomputable def feasible_partial_solve_wit_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (j >= m_pre)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= m_pre)) (PreH20 : ((0 : Int) <= ((i * m_pre) + j))) (PreH21 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH22 : ((0 : Int) <= mask)) (PreH23 : (mask <= full)) (PreH24 : ((Zlength (reps)) = 256)) (PreH25 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH26 : (RowMaskPrefix rows x_pre i j mask)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (j >= m_pre) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= m_pre) ” &&
  “ ((0 : Int) <= ((i * m_pre) + j)) ” &&
  “ (((i * m_pre) + j) <= (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= mask) ” &&
  “ (mask <= full) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre i reps) ” &&
  “ (RowMaskPrefix rows x_pre i j mask) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i))) ”
  &&  (((rep_pre + (mask * sizeof(INT)))) # Int |-> ((Znth mask reps (0 : Int))))
  ** (intArray.missing_i rep_pre mask (0 : Int) 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)

noncomputable def feasible_partial_solve_wit_4 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (mask : Int) (j : Int) (i : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth mask reps (0 : Int)) < (0 : Int))) (PreH2 : (j >= m_pre)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : ((0 : Int) <= x_pre)) (PreH9 : (x_pre <= 1000000000)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : ((Zlength (old_bi)) = 1)) (PreH13 : ((Zlength (old_bj)) = 1)) (PreH14 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH15 : ((0 : Int) <= full)) (PreH16 : (full <= 255)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= m_pre)) (PreH21 : ((0 : Int) <= ((i * m_pre) + j))) (PreH22 : (((i * m_pre) + j) <= (n_pre * m_pre))) (PreH23 : ((0 : Int) <= mask)) (PreH24 : (mask <= full)) (PreH25 : ((Zlength (reps)) = 256)) (PreH26 : (RepresentativePrefix rows x_pre m_pre i reps)) (PreH27 : (RowMaskPrefix rows x_pre i j mask)) (PreH28 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i)))) ,
  (intArray.full rep_pre 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((Znth mask reps (0 : Int)) < (0 : Int)) ” &&
  “ (j >= m_pre) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= m_pre) ” &&
  “ ((0 : Int) <= ((i * m_pre) + j)) ” &&
  “ (((i * m_pre) + j) <= (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= mask) ” &&
  “ (mask <= full) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre i reps) ” &&
  “ (RowMaskPrefix rows x_pre i j mask) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < i))) ”
  &&  (((rep_pre + (mask * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i rep_pre mask (0 : Int) 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)

noncomputable def feasible_partial_solve_wit_5 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (s <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= (full + 1))) (PreH18 : ((Zlength (reps)) = 256)) (PreH19 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH20 : (NoCoverPrefix reps full s (0 : Int))) (PreH21 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (s <= full) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s (0 : Int)) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (((rep_pre + (s * sizeof(INT)))) # Int |-> ((Znth s reps (0 : Int))))
  ** (intArray.missing_i rep_pre s (0 : Int) 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)

noncomputable def feasible_partial_solve_wit_6 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : (u <= full)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : ((0 : Int) <= x_pre)) (PreH8 : (x_pre <= 1000000000)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : ((Zlength (old_bi)) = 1)) (PreH12 : ((Zlength (old_bj)) = 1)) (PreH13 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH14 : ((0 : Int) <= full)) (PreH15 : (full <= 255)) (PreH16 : ((0 : Int) <= s)) (PreH17 : (s <= full)) (PreH18 : ((0 : Int) <= u)) (PreH19 : (u <= (full + 1))) (PreH20 : ((Zlength (reps)) = 256)) (PreH21 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH22 : ((Znth s reps (0 : Int)) < n_pre)) (PreH23 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH24 : (NoCoverPrefix reps full s u)) (PreH25 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ (u <= full) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= u) ” &&
  “ (u <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s u) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (((rep_pre + (u * sizeof(INT)))) # Int |-> ((Znth u reps (0 : Int))))
  ** (intArray.missing_i rep_pre u (0 : Int) 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)

noncomputable def feasible_partial_solve_wit_7 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  “ ((Z.lor s u) = full) ” &&
  “ ((Znth u reps (0 : Int)) >= (0 : Int)) ” &&
  “ (u <= full) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= u) ” &&
  “ (u <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s u) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)

noncomputable def feasible_partial_solve_wit_8 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ ((Z.lor s u) = full) ” &&
  “ ((Znth u reps (0 : Int)) >= (0 : Int)) ” &&
  “ (u <= full) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= u) ” &&
  “ (u <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s u) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (((rep_pre + (s * sizeof(INT)))) # Int |-> ((Znth s reps (0 : Int))))
  ** (intArray.missing_i rep_pre s (0 : Int) 256 reps)
  ** ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
  ** (intArray2.full a_pre n_pre m_pre rows)

noncomputable def feasible_partial_solve_wit_9 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (x_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) (rows : (List (List Int))) (reps : (List Int)) (u : Int) (s : Int) (full : Int) (__default__List_Z : _List_Z) (PreH1 : ((Z.lor s u) = full)) (PreH2 : ((Znth u reps (0 : Int)) >= (0 : Int))) (PreH3 : (u <= full)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : ((0 : Int) <= x_pre)) (PreH10 : (x_pre <= 1000000000)) (PreH11 : (n_pre = (Zlength (rows)))) (PreH12 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH13 : ((Zlength (old_bi)) = 1)) (PreH14 : ((Zlength (old_bj)) = 1)) (PreH15 : (full = ((Z.shiftl 1 m_pre) - 1))) (PreH16 : ((0 : Int) <= full)) (PreH17 : (full <= 255)) (PreH18 : ((0 : Int) <= s)) (PreH19 : (s <= full)) (PreH20 : ((0 : Int) <= u)) (PreH21 : (u <= (full + 1))) (PreH22 : ((Zlength (reps)) = 256)) (PreH23 : ((0 : Int) <= (Znth s reps (0 : Int)))) (PreH24 : ((Znth s reps (0 : Int)) < n_pre)) (PreH25 : (RepresentativePrefix rows x_pre m_pre n_pre reps)) (PreH26 : (NoCoverPrefix reps full s u)) (PreH27 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre)))) ,
  (intArray.full rep_pre 256 reps)
  ** ((bi_pre) # Int |-> (((Znth s reps (0 : Int)) + 1)))
  ** ((bj_pre) # Int |->_)
  ** (intArray2.full a_pre n_pre m_pre rows)
|--
  “ ((Z.lor s u) = full) ” &&
  “ ((Znth u reps (0 : Int)) >= (0 : Int)) ” &&
  “ (u <= full) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (old_bi)) = 1) ” &&
  “ ((Zlength (old_bj)) = 1) ” &&
  “ (full = ((Z.shiftl 1 m_pre) - 1)) ” &&
  “ ((0 : Int) <= full) ” &&
  “ (full <= 255) ” &&
  “ ((0 : Int) <= s) ” &&
  “ (s <= full) ” &&
  “ ((0 : Int) <= u) ” &&
  “ (u <= (full + 1)) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ ((0 : Int) <= (Znth s reps (0 : Int))) ” &&
  “ ((Znth s reps (0 : Int)) < n_pre) ” &&
  “ (RepresentativePrefix rows x_pre m_pre n_pre reps) ” &&
  “ (NoCoverPrefix reps full s u) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q <= full)) -> (((-1) <= (Znth q reps (0 : Int))) ∧ ((Znth q reps (0 : Int)) < n_pre))) ”
  &&  (((rep_pre + (u * sizeof(INT)))) # Int |-> ((Znth u reps (0 : Int))))
  ** (intArray.missing_i rep_pre u (0 : Int) 256 reps)
  ** ((bi_pre) # Int |-> (((Znth s reps (0 : Int)) + 1)))
  ** ((bj_pre) # Int |->_)
  ** (intArray2.full a_pre n_pre m_pre rows)

noncomputable def feasible_which_implies_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) ,
  (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (old_bj : (List (Option Int))) (old_bi : (List (Option Int))) ,
  (intArray.mixed_full bi_pre 1 old_bi)
  ** (intArray.mixed_full bj_pre 1 old_bj)
|--
  EX x_2 : Int, EX x : Int,
  ((bj_pre) # Int |-> (x_2))
  ** ((bi_pre) # Int |-> (x))
)

noncomputable def solver_safety_wit_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) ,
  ((( &( "hi" ) )) # Int |->_)
  ** ((( &( "lo" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.undef_full bi_pre 1)
  ** (intArray.undef_full bj_pre 1)
|--
  “ (1000000000 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000000) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) ,
  ((( &( "lo" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.undef_full bi_pre 1)
  ** (intArray.undef_full bj_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) ,
  ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
  ** ((( &( "hi" ) )) # Int |-> (1000000000))
  ** ((( &( "lo" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_4 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ”
)

noncomputable def solver_safety_wit_4_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX) ”

noncomputable def solver_safety_wit_4_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((INT_MIN) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((((hi - lo) + 1) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (((hi - lo) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((hi - lo) + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((hi - lo) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (hi - lo)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval ≠ (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_12 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1)) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1)) ”
)

noncomputable def solver_safety_wit_12_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_12_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((INT_MIN) <= ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo >= hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (bi_cells)) = 1)) (PreH2 : ((Zlength (bj_cells)) = 1)) (PreH3 : (lo = (0 : Int))) (PreH4 : (lo >= hi)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH13 : ((0 : Int) <= lo)) (PreH14 : (lo <= hi)) (PreH15 : (hi <= 1000000000)) (PreH16 : ((0 : Int) <= cur_i)) (PreH17 : (cur_i < n_pre)) (PreH18 : ((0 : Int) <= cur_j)) (PreH19 : (cur_j < n_pre)) (PreH20 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8)))) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) ,
  ((bi_pre) # Int |-> (1))
  ** ((bj_pre) # Int |-> (1))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  EX cur_j : Int, EX cur_i : Int,
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ (1000000000 <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows (0 : Int) 1000000000 cur_i cur_j) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) ,
  ((bi_pre) # Int |-> (1))
  ** ((bj_pre) # Int |-> (1))
  ** (intArray.full_shape rep_pre 256)
|--
  EX cur_j : Int, EX cur_i : Int,
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ (1000000000 <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows (0 : Int) 1000000000 cur_i cur_j) ”
  &&  (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
)

noncomputable def solver_entail_wit_2_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps_2 : (List Int)) (retval_2 : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps_2)) = 256)) (PreH2 : (retval_2 = 1)) (PreH3 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval_2 = (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  EX reps : (List Int), EX retval : Int,
  “ ((Zlength (reps)) = 256) ” &&
  “ (retval = (0 : Int)) ” &&
  “ ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2)))) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (reps)) = 256) ” &&
  “ (retval = (0 : Int)) ” &&
  “ ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2)))) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_entail_wit_3_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (reps)) = 256) ” &&
  “ (retval = 1) ” &&
  “ (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_entail_wit_3_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps_2 : (List Int)) (retval_2 : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps_2)) = 256)) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval_2 ≠ (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps_2)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  EX i : Int, EX j : Int, EX reps : (List Int), EX retval : Int,
  “ ((Zlength (reps)) = 256) ” &&
  “ (retval = 1) ” &&
  “ (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j_2 : Int) (cur_i_2 : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i_2)) (PreH19 : (cur_i_2 < n_pre)) (PreH20 : ((0 : Int) <= cur_j_2)) (PreH21 : (cur_j_2 < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2)) (PreH23 : (retval ≠ (0 : Int))) ,
  ((bi_pre) # Int |-> ((Znth (0 : Int) ((i + 1) :: (@List.nil Int)) (0 : Int))))
  ** ((bj_pre) # Int |-> ((Znth (0 : Int) ((j + 1) :: (@List.nil Int)) (0 : Int))))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
|--
  EX cur_j : Int, EX cur_i : Int,
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ” &&
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows (lo + (Z.quot ((hi - lo) + 1) 2)) hi cur_i cur_j) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (rows : (List (List Int))) (cur_j_2 : Int) (cur_i_2 : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (0 : Int) ((j + 1) :: (@List.nil Int)) (0 : Int)) <= INT_MAX)) (PreH2 : ((Znth (0 : Int) ((i + 1) :: (@List.nil Int)) (0 : Int)) <= INT_MAX)) (PreH3 : ((Znth (0 : Int) ((j + 1) :: (@List.nil Int)) (0 : Int)) >= INT_MIN)) (PreH4 : ((Znth (0 : Int) ((i + 1) :: (@List.nil Int)) (0 : Int)) >= INT_MIN)) (PreH5 : ((Zlength (reps)) = 256)) (PreH6 : (retval = 1)) (PreH7 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH8 : ((Zlength (ci_cells)) = 1)) (PreH9 : ((Zlength (cj_cells)) = 1)) (PreH10 : (lo < hi)) (PreH11 : (Pre rows)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 300000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 8)) (PreH16 : (n_pre = (Zlength (rows)))) (PreH17 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH19 : ((0 : Int) <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi <= 1000000000)) (PreH22 : ((0 : Int) <= cur_i_2)) (PreH23 : (cur_i_2 < n_pre)) (PreH24 : ((0 : Int) <= cur_j_2)) (PreH25 : (cur_j_2 < n_pre)) (PreH26 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2)) (PreH27 : (retval ≠ (0 : Int))) ,
  ((bi_pre) # Int |-> ((Znth (0 : Int) ((i + 1) :: (@List.nil Int)) (0 : Int))))
  ** ((bj_pre) # Int |-> ((Znth (0 : Int) ((j + 1) :: (@List.nil Int)) (0 : Int))))
  ** (intArray.full rep_pre 256 reps)
|--
  EX cur_j : Int, EX cur_i : Int,
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ” &&
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows (lo + (Z.quot ((hi - lo) + 1) 2)) hi cur_i cur_j) ”
  &&  (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
)

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j_2 : Int) (cur_i_2 : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i_2)) (PreH19 : (cur_i_2 < n_pre)) (PreH20 : ((0 : Int) <= cur_j_2)) (PreH21 : (cur_j_2 < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2)) (PreH23 : (retval = (0 : Int))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i_2 + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j_2 + 1) :: (@List.nil Int)))
|--
  EX cur_j : Int, EX cur_i : Int,
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1)) ” &&
  “ (((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) cur_i cur_j) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
) \/
(
forall (rep_pre : Int) (m_pre : Int) (n_pre : Int) (rows : (List (List Int))) (cur_j_2 : Int) (cur_i_2 : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i_2)) (PreH19 : (cur_i_2 < n_pre)) (PreH20 : ((0 : Int) <= cur_j_2)) (PreH21 : (cur_j_2 < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i_2 cur_j_2)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.full rep_pre 256 reps)
|--
  EX cur_j : Int, EX cur_i : Int,
  “ (((cur_j_2 + 1) :: (@List.nil Int)) = ((cur_j + 1) :: (@List.nil Int))) ” &&
  “ (((cur_i_2 + 1) :: (@List.nil Int)) = ((cur_i + 1) :: (@List.nil Int))) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1)) ” &&
  “ (((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo ((lo + (Z.quot ((hi - lo) + 1) 2)) - 1) cur_i cur_j) ”
  &&  (intArray.full_shape rep_pre 256)
)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (0 : Int) i j)) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = (0 : Int))) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH16 : ((0 : Int) <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : ((0 : Int) <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : ((0 : Int) <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.full bi_pre 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
|--
  EX out : (Int × Int),
  “ (Spec rows out) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((fst (out)) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((snd (out)) :: (@List.nil Int)))
) \/
(
forall (rep_pre : Int) (m_pre : Int) (n_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (0 : Int) i j)) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = (0 : Int))) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH16 : ((0 : Int) <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : ((0 : Int) <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : ((0 : Int) <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.full rep_pre 256 reps)
|--
  EX out : (Int × Int),
  “ (((j + 1) :: (@List.nil Int)) = ((snd (out)) :: (@List.nil Int))) ” &&
  “ (((i + 1) :: (@List.nil Int)) = ((fst (out)) :: (@List.nil Int))) ” &&
  “ (Spec rows out) ”
  &&  (intArray.full_shape rep_pre 256)
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (0 : Int)))) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = (0 : Int))) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH16 : ((0 : Int) <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : ((0 : Int) <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : ((0 : Int) <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
|--
  EX out : (Int × Int),
  “ (Spec rows out) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((fst (out)) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((snd (out)) :: (@List.nil Int)))
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (0 : Int)))) (PreH4 : ((Zlength (bi_cells)) = 1)) (PreH5 : ((Zlength (bj_cells)) = 1)) (PreH6 : (lo = (0 : Int))) (PreH7 : (lo >= hi)) (PreH8 : (Pre rows)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 300000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 8)) (PreH13 : (n_pre = (Zlength (rows)))) (PreH14 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH16 : ((0 : Int) <= lo)) (PreH17 : (lo <= hi)) (PreH18 : (hi <= 1000000000)) (PreH19 : ((0 : Int) <= cur_i)) (PreH20 : (cur_i < n_pre)) (PreH21 : ((0 : Int) <= cur_j)) (PreH22 : (cur_j < n_pre)) (PreH23 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** (intArray.full rep_pre 256 reps)
|--
  EX out : (Int × Int),
  “ (Spec rows out) ”
  &&  (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((fst (out)) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((snd (out)) :: (@List.nil Int)))
)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo ≠ (0 : Int))) (PreH2 : (lo >= hi)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi <= 1000000000)) (PreH14 : ((0 : Int) <= cur_i)) (PreH15 : (cur_i < n_pre)) (PreH16 : ((0 : Int) <= cur_j)) (PreH17 : (cur_j < n_pre)) (PreH18 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  EX out : (Int × Int),
  “ (Spec rows out) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((fst (out)) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((snd (out)) :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo ≠ (0 : Int))) (PreH2 : (lo >= hi)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi <= 1000000000)) (PreH14 : ((0 : Int) <= cur_i)) (PreH15 : (cur_i < n_pre)) (PreH16 : ((0 : Int) <= cur_j)) (PreH17 : (cur_j < n_pre)) (PreH18 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  TT && emp 
|--
  EX out : (Int × Int),
  “ (((cur_j + 1) :: (@List.nil Int)) = ((snd (out)) :: (@List.nil Int))) ” &&
  “ (((cur_i + 1) :: (@List.nil Int)) = ((fst (out)) :: (@List.nil Int))) ” &&
  “ (Spec rows out) ”
  &&  emp
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (Pre rows)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (rows)))) (PreH7 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.undef_full bi_pre 1)
  ** (intArray.undef_full bj_pre 1)
|--
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= m_pre) ∧ (m_pre <= 8))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ”
  &&  (intArray.undef_full bi_pre 1)
  ** (intArray.undef_full bj_pre 1)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo < hi)) (PreH2 : (Pre rows)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 8)) (PreH7 : (n_pre = (Zlength (rows)))) (PreH8 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH10 : ((0 : Int) <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= 1000000000)) (PreH13 : ((0 : Int) <= cur_i)) (PreH14 : (cur_i < n_pre)) (PreH15 : ((0 : Int) <= cur_j)) (PreH16 : (cur_j < n_pre)) (PreH17 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_partial_solve_wit_3_pure : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (ci_cells)) = 1)) (PreH2 : ((Zlength (cj_cells)) = 1)) (PreH3 : (lo < hi)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH12 : ((0 : Int) <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 1000000000)) (PreH15 : ((0 : Int) <= cur_i)) (PreH16 : (cur_i < n_pre)) (PreH17 : ((0 : Int) <= cur_j)) (PreH18 : (cur_j < n_pre)) (PreH19 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= 1000000000) ” &&
  “ ((0 : Int) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH22 : ((0 : Int) <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : ((0 : Int) <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : ((0 : Int) <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((0 : Int) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ” &&
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= 1000000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ”
)

noncomputable def solver_partial_solve_wit_3_pure_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH22 : ((0 : Int) <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : ((0 : Int) <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : ((0 : Int) <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((0 : Int) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ”

noncomputable def solver_partial_solve_wit_3_pure_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH22 : ((0 : Int) <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : ((0 : Int) <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : ((0 : Int) <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= 1000000000) ”

noncomputable def solver_partial_solve_wit_3_pure_split_goal_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (ci_cells)) = 1)) (PreH12 : ((Zlength (cj_cells)) = 1)) (PreH13 : (lo < hi)) (PreH14 : (Pre rows)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 300000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 8)) (PreH19 : (n_pre = (Zlength (rows)))) (PreH20 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH22 : ((0 : Int) <= lo)) (PreH23 : (lo <= hi)) (PreH24 : (hi <= 1000000000)) (PreH25 : ((0 : Int) <= cur_i)) (PreH26 : (cur_i < n_pre)) (PreH27 : ((0 : Int) <= cur_j)) (PreH28 : (cur_j < n_pre)) (PreH29 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ”

noncomputable def solver_partial_solve_wit_3_aux : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (ci_cells)) = 1)) (PreH2 : ((Zlength (cj_cells)) = 1)) (PreH3 : (lo < hi)) (PreH4 : (Pre rows)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 8)) (PreH9 : (n_pre = (Zlength (rows)))) (PreH10 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH12 : ((0 : Int) <= lo)) (PreH13 : (lo <= hi)) (PreH14 : (hi <= 1000000000)) (PreH15 : ((0 : Int) <= cur_i)) (PreH16 : (cur_i < n_pre)) (PreH17 : ((0 : Int) <= cur_j)) (PreH18 : (cur_j < n_pre)) (PreH19 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ ((lo + (Z.quot ((hi - lo) + 1) 2)) <= 1000000000) ” &&
  “ ((0 : Int) <= (lo + (Z.quot ((hi - lo) + 1) 2))) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_partial_solve_wit_3 : Prop := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux

noncomputable def solver_partial_solve_wit_4_pure : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((cur_j + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((cur_i + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((j + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((i + 1) :: (@List.nil Int)))) = 1) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH25 : ((0 : Int) <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : ((0 : Int) <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : ((0 : Int) <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH33 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((i + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((j + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((cur_i + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((cur_j + 1) :: (@List.nil Int)))) = 1) ”
)

noncomputable def solver_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH25 : ((0 : Int) <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : ((0 : Int) <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : ((0 : Int) <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH33 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((i + 1) :: (@List.nil Int)))) = 1) ”

noncomputable def solver_partial_solve_wit_4_pure_split_goal_2 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH25 : ((0 : Int) <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : ((0 : Int) <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : ((0 : Int) <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH33 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((j + 1) :: (@List.nil Int)))) = 1) ”

noncomputable def solver_partial_solve_wit_4_pure_split_goal_3 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH25 : ((0 : Int) <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : ((0 : Int) <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : ((0 : Int) <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH33 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((cur_i + 1) :: (@List.nil Int)))) = 1) ”

noncomputable def solver_partial_solve_wit_4_pure_split_goal_4 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((lo + (Z.quot ((hi - lo) + 1) 2)) <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((lo + (Z.quot ((hi - lo) + 1) 2)) >= INT_MIN)) (PreH11 : ((Zlength (reps)) = 256)) (PreH12 : (retval = 1)) (PreH13 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH14 : ((Zlength (ci_cells)) = 1)) (PreH15 : ((Zlength (cj_cells)) = 1)) (PreH16 : (lo < hi)) (PreH17 : (Pre rows)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 300000)) (PreH20 : (1 <= m_pre)) (PreH21 : (m_pre <= 8)) (PreH22 : (n_pre = (Zlength (rows)))) (PreH23 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH24 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH25 : ((0 : Int) <= lo)) (PreH26 : (lo <= hi)) (PreH27 : (hi <= 1000000000)) (PreH28 : ((0 : Int) <= cur_i)) (PreH29 : (cur_i < n_pre)) (PreH30 : ((0 : Int) <= cur_j)) (PreH31 : (cur_j < n_pre)) (PreH32 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH33 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** ((( &( "mid" ) )) # Int |-> ((lo + (Z.quot ((hi - lo) + 1) 2))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((cur_j + 1) :: (@List.nil Int)))) = 1) ”

noncomputable def solver_partial_solve_wit_4_aux : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (i : Int) (j : Int) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = 1)) (PreH3 : (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j)) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval ≠ (0 : Int))) ,
  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (((cur_j + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((cur_i + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((j + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (((i + 1) :: (@List.nil Int)))) = 1) ” &&
  “ ((Zlength (reps)) = 256) ” &&
  “ (retval = 1) ” &&
  “ (PairAtLeast rows (lo + (Z.quot ((hi - lo) + 1) 2)) i j) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full ( &( "ci" ) ) 1 ((i + 1) :: (@List.nil Int)))
  ** (intArray.full ( &( "cj" ) ) 1 ((j + 1) :: (@List.nil Int)))
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)

noncomputable def solver_partial_solve_wit_4 : Prop := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (cj_cells : (List (Option Int))) (ci_cells : (List (Option Int))) (reps : (List Int)) (retval : Int) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (reps)) = 256)) (PreH2 : (retval = (0 : Int))) (PreH3 : ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2))))) (PreH4 : ((Zlength (ci_cells)) = 1)) (PreH5 : ((Zlength (cj_cells)) = 1)) (PreH6 : (lo < hi)) (PreH7 : (Pre rows)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 300000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 8)) (PreH12 : (n_pre = (Zlength (rows)))) (PreH13 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH15 : ((0 : Int) <= lo)) (PreH16 : (lo <= hi)) (PreH17 : (hi <= 1000000000)) (PreH18 : ((0 : Int) <= cur_i)) (PreH19 : (cur_i < n_pre)) (PreH20 : ((0 : Int) <= cur_j)) (PreH21 : (cur_j < n_pre)) (PreH22 : (SolverSearchMeaning rows lo hi cur_i cur_j)) (PreH23 : (retval = (0 : Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ ((Zlength (reps)) = 256) ” &&
  “ (retval = (0 : Int)) ” &&
  “ ¬((FeasibleAtThreshold rows (lo + (Z.quot ((hi - lo) + 1) 2)))) ” &&
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ” &&
  “ (lo < hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full rep_pre 256 reps)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (__default__List_Z : _List_Z) (PreH1 : (lo = (0 : Int))) (PreH2 : (lo >= hi)) (PreH3 : (Pre rows)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 8)) (PreH8 : (n_pre = (Zlength (rows)))) (PreH9 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi <= 1000000000)) (PreH14 : ((0 : Int) <= cur_i)) (PreH15 : (cur_i < n_pre)) (PreH16 : ((0 : Int) <= cur_j)) (PreH17 : (cur_j < n_pre)) (PreH18 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
|--
  “ (lo = (0 : Int)) ” &&
  “ (lo >= hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ”
  &&  (intArray.full bi_pre 1 ((cur_i + 1) :: (@List.nil Int)))
  ** (intArray.full bj_pre 1 ((cur_j + 1) :: (@List.nil Int)))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)

noncomputable def solver_partial_solve_wit_7_pure : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (bi_cells)) = 1)) (PreH2 : ((Zlength (bj_cells)) = 1)) (PreH3 : (lo = (0 : Int))) (PreH4 : (lo >= hi)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH13 : ((0 : Int) <= lo)) (PreH14 : (lo <= hi)) (PreH15 : (hi <= 1000000000)) (PreH16 : ((0 : Int) <= cur_i)) (PreH17 : (cur_i < n_pre)) (PreH18 : ((0 : Int) <= cur_j)) (PreH19 : (cur_j < n_pre)) (PreH20 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (bi_cells)) = 1) ” &&
  “ ((Zlength (bj_cells)) = 1) ”
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (hi >= INT_MIN)) (PreH6 : (lo >= INT_MIN)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : ((Zlength (bi_cells)) = 1)) (PreH10 : ((Zlength (bj_cells)) = 1)) (PreH11 : (lo = (0 : Int))) (PreH12 : (lo >= hi)) (PreH13 : (Pre rows)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 300000)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 8)) (PreH18 : (n_pre = (Zlength (rows)))) (PreH19 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH21 : ((0 : Int) <= lo)) (PreH22 : (lo <= hi)) (PreH23 : (hi <= 1000000000)) (PreH24 : ((0 : Int) <= cur_i)) (PreH25 : (cur_i < n_pre)) (PreH26 : ((0 : Int) <= cur_j)) (PreH27 : (cur_j < n_pre)) (PreH28 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ”
)

noncomputable def solver_partial_solve_wit_7_pure_split_goal_1 : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (hi >= INT_MIN)) (PreH6 : (lo >= INT_MIN)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : ((Zlength (bi_cells)) = 1)) (PreH10 : ((Zlength (bj_cells)) = 1)) (PreH11 : (lo = (0 : Int))) (PreH12 : (lo >= hi)) (PreH13 : (Pre rows)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 300000)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 8)) (PreH18 : (n_pre = (Zlength (rows)))) (PreH19 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH20 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH21 : ((0 : Int) <= lo)) (PreH22 : (lo <= hi)) (PreH23 : (hi <= 1000000000)) (PreH24 : ((0 : Int) <= cur_i)) (PreH25 : (cur_i < n_pre)) (PreH26 : ((0 : Int) <= cur_j)) (PreH27 : (cur_j < n_pre)) (PreH28 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "rep" ) )) # Ptr |-> (rep_pre))
  ** ((( &( "bi" ) )) # Ptr |-> (bi_pre))
  ** ((( &( "bj" ) )) # Ptr |-> (bj_pre))
  ** ((( &( "lo" ) )) # Int |-> (lo))
  ** ((( &( "hi" ) )) # Int |-> (hi))
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ”

noncomputable def solver_partial_solve_wit_7_aux : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (rep_pre : Int) (m_pre : Int) (n_pre : Int) (a_pre : Int) (rows : (List (List Int))) (cur_j : Int) (cur_i : Int) (hi : Int) (lo : Int) (bj_cells : (List (Option Int))) (bi_cells : (List (Option Int))) (__default__List_Z : _List_Z) (PreH1 : ((Zlength (bi_cells)) = 1)) (PreH2 : ((Zlength (bj_cells)) = 1)) (PreH3 : (lo = (0 : Int))) (PreH4 : (lo >= hi)) (PreH5 : (Pre rows)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 300000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 8)) (PreH10 : (n_pre = (Zlength (rows)))) (PreH11 : (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z))))) (PreH12 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000)))) (PreH13 : ((0 : Int) <= lo)) (PreH14 : (lo <= hi)) (PreH15 : (hi <= 1000000000)) (PreH16 : ((0 : Int) <= cur_i)) (PreH17 : (cur_i < n_pre)) (PreH18 : ((0 : Int) <= cur_j)) (PreH19 : (cur_j < n_pre)) (PreH20 : (SolverSearchMeaning rows lo hi cur_i cur_j)) ,
  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
  ** (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
|--
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k (List.flatten (rows)) (0 : Int))) ∧ ((Znth k (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ ((Zlength (bi_cells)) = 1) ” &&
  “ ((Zlength (bj_cells)) = 1) ” &&
  “ ((Zlength (bi_cells)) = 1) ” &&
  “ ((Zlength (bj_cells)) = 1) ” &&
  “ (lo = (0 : Int)) ” &&
  “ (lo >= hi) ” &&
  “ (Pre rows) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 8) ” &&
  “ (n_pre = (Zlength (rows))) ” &&
  “ (m_pre = (Zlength ((Znth (0 : Int) rows __default__List_Z)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (n_pre * m_pre))) -> (((0 : Int) <= (Znth k_2 (List.flatten (rows)) (0 : Int))) ∧ ((Znth k_2 (List.flatten (rows)) (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= lo) ” &&
  “ (lo <= hi) ” &&
  “ (hi <= 1000000000) ” &&
  “ ((0 : Int) <= cur_i) ” &&
  “ (cur_i < n_pre) ” &&
  “ ((0 : Int) <= cur_j) ” &&
  “ (cur_j < n_pre) ” &&
  “ (SolverSearchMeaning rows lo hi cur_i cur_j) ”
  &&  (intArray2.full a_pre n_pre m_pre rows)
  ** (intArray.full_shape rep_pre 256)
  ** (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)

noncomputable def solver_partial_solve_wit_7 : Prop := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux

noncomputable def solver_which_implies_wit_1 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) ,
  (intArray.undef_full bi_pre 1)
  ** (intArray.undef_full bj_pre 1)
|--
  ((bi_pre) # Int |->_)
  ** ((bj_pre) # Int |->_)
) \/
(
forall (bj_pre : Int) (bi_pre : Int) ,
  (intArray.undef_full bi_pre 1)
  ** (intArray.undef_full bj_pre 1)
|--
  EX x_2 : Int, EX x : Int,
  ((bj_pre) # Int |-> (x_2))
  ** ((bi_pre) # Int |-> (x))
)

noncomputable def solver_which_implies_wit_2 : Prop :=
  (
  ((( &( "ci" ) )) # Int |->_)
  ** ((( &( "cj" ) )) # Int |->_)
|--
  EX cj_cells : (List (Option Int)), EX ci_cells : (List (Option Int)),
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ”
  &&  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
) \/
(
  ((( &( "ci" ) )) # Int |->_)
  ** ((( &( "cj" ) )) # Int |->_)
|--
  EX cj_cells : (List (Option Int)), EX ci_cells : (List (Option Int)),
  “ ((Zlength (ci_cells)) = 1) ” &&
  “ ((Zlength (cj_cells)) = 1) ”
  &&  (intArray.mixed_full ( &( "ci" ) ) 1 ci_cells)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_cells)
)

noncomputable def solver_which_implies_wit_3 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (old_js : (List Int)) (old_is : (List Int)) (cj_values : (List Int)) (ci_values : (List Int)) (PreH1 : ((Zlength (ci_values)) = 1)) (PreH2 : ((Zlength (cj_values)) = 1)) (PreH3 : ((Zlength (old_is)) = 1)) (PreH4 : ((Zlength (old_js)) = 1)) ,
  (intArray.full ( &( "ci" ) ) 1 ci_values)
  ** (intArray.full ( &( "cj" ) ) 1 cj_values)
  ** (intArray.full bi_pre 1 old_is)
  ** (intArray.full bj_pre 1 old_js)
|--
  ((( &( "ci" ) )) # Int |-> ((Znth (0 : Int) ci_values (0 : Int))))
  ** ((( &( "cj" ) )) # Int |-> ((Znth (0 : Int) cj_values (0 : Int))))
  ** ((bi_pre) # Int |-> ((Znth (0 : Int) old_is (0 : Int))))
  ** ((bj_pre) # Int |-> ((Znth (0 : Int) old_js (0 : Int))))
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (old_js : (List Int)) (old_is : (List Int)) (cj_values : (List Int)) (ci_values : (List Int)) (PreH1 : ((Zlength (ci_values)) = 1)) (PreH2 : ((Zlength (cj_values)) = 1)) (PreH3 : ((Zlength (old_is)) = 1)) (PreH4 : ((Zlength (old_js)) = 1)) ,
  (intArray.full ( &( "ci" ) ) 1 ci_values)
  ** (intArray.full ( &( "cj" ) ) 1 cj_values)
  ** (intArray.full bi_pre 1 old_is)
  ** (intArray.full bj_pre 1 old_js)
|--
  ((( &( "ci" ) )) # Int |-> ((Znth (0 : Int) ci_values (0 : Int))))
  ** ((( &( "cj" ) )) # Int |-> ((Znth (0 : Int) cj_values (0 : Int))))
  ** ((bi_pre) # Int |-> ((Znth (0 : Int) old_is (0 : Int))))
  ** ((bj_pre) # Int |-> ((Znth (0 : Int) old_js (0 : Int))))
)

noncomputable def solver_which_implies_wit_3_split_goal_spatial : Prop :=
  forall (bj_pre : Int) (bi_pre : Int) (old_js : (List Int)) (old_is : (List Int)) (cj_values : (List Int)) (ci_values : (List Int)) (PreH1 : ((Zlength (ci_values)) = 1)) (PreH2 : ((Zlength (cj_values)) = 1)) (PreH3 : ((Zlength (old_is)) = 1)) (PreH4 : ((Zlength (old_js)) = 1)) ,
  (intArray.full ( &( "ci" ) ) 1 ci_values)
  ** (intArray.full ( &( "cj" ) ) 1 cj_values)
  ** (intArray.full bi_pre 1 old_is)
  ** (intArray.full bj_pre 1 old_js)
|--
  ((( &( "ci" ) )) # Int |-> ((Znth (0 : Int) ci_values (0 : Int))))
  ** ((( &( "cj" ) )) # Int |-> ((Znth (0 : Int) cj_values (0 : Int))))
  ** ((bi_pre) # Int |-> ((Znth (0 : Int) old_is (0 : Int))))
  ** ((bj_pre) # Int |-> ((Znth (0 : Int) old_js (0 : Int))))

noncomputable def solver_which_implies_wit_4 : Prop :=
  (
forall (cj_values : (List (Option Int))) (ci_values : (List (Option Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_values)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_values)
|--
  ((( &( "ci" ) )) # Int |->_)
  ** ((( &( "cj" ) )) # Int |->_)
) \/
(
forall (cj_values : (List (Option Int))) (ci_values : (List (Option Int))) ,
  (intArray.mixed_full ( &( "ci" ) ) 1 ci_values)
  ** (intArray.mixed_full ( &( "cj" ) ) 1 cj_values)
|--
  EX x_2 : Int, EX x : Int,
  ((( &( "cj" ) )) # Int |-> (x_2))
  ** ((( &( "ci" ) )) # Int |-> (x))
)

noncomputable def solver_which_implies_wit_5 : Prop :=
  (
forall (bj_pre : Int) (bi_pre : Int) (bj_values : (List Int)) (bi_values : (List Int)) ,
  (intArray.full bi_pre 1 bi_values)
  ** (intArray.full bj_pre 1 bj_values)
|--
  EX bj_cells : (List (Option Int)), EX bi_cells : (List (Option Int)),
  “ ((Zlength (bi_cells)) = 1) ” &&
  “ ((Zlength (bj_cells)) = 1) ”
  &&  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
) \/
(
forall (bj_pre : Int) (bi_pre : Int) (bj_values : (List Int)) (bi_values : (List Int)) ,
  (intArray.full bi_pre 1 bi_values)
  ** (intArray.full bj_pre 1 bj_values)
|--
  EX bj_cells : (List (Option Int)), EX bi_cells : (List (Option Int)),
  “ ((Zlength (bi_cells)) = 1) ” &&
  “ ((Zlength (bj_cells)) = 1) ”
  &&  (intArray.mixed_full bi_pre 1 bi_cells)
  ** (intArray.mixed_full bj_pre 1 bj_cells)
)


structure VC_Correct : Type where
  proof_of_feasible_safety_wit_3 : feasible_safety_wit_3
  proof_of_feasible_safety_wit_4 : feasible_safety_wit_4
  proof_of_feasible_safety_wit_5 : feasible_safety_wit_5
  proof_of_feasible_safety_wit_6 : feasible_safety_wit_6
  proof_of_feasible_safety_wit_7 : feasible_safety_wit_7
  proof_of_feasible_safety_wit_8 : feasible_safety_wit_8
  proof_of_feasible_safety_wit_9 : feasible_safety_wit_9
  proof_of_feasible_safety_wit_10 : feasible_safety_wit_10
  proof_of_feasible_safety_wit_11 : feasible_safety_wit_11
  proof_of_feasible_safety_wit_12 : feasible_safety_wit_12
  proof_of_feasible_safety_wit_13 : feasible_safety_wit_13
  proof_of_feasible_safety_wit_15 : feasible_safety_wit_15
  proof_of_feasible_safety_wit_16 : feasible_safety_wit_16
  proof_of_feasible_safety_wit_17 : feasible_safety_wit_17
  proof_of_feasible_safety_wit_18 : feasible_safety_wit_18
  proof_of_feasible_safety_wit_19 : feasible_safety_wit_19
  proof_of_feasible_safety_wit_20 : feasible_safety_wit_20
  proof_of_feasible_safety_wit_21 : feasible_safety_wit_21
  proof_of_feasible_safety_wit_22 : feasible_safety_wit_22
  proof_of_feasible_safety_wit_23 : feasible_safety_wit_23
  proof_of_feasible_safety_wit_24 : feasible_safety_wit_24
  proof_of_feasible_safety_wit_25 : feasible_safety_wit_25
  proof_of_feasible_safety_wit_26 : feasible_safety_wit_26
  proof_of_feasible_safety_wit_27 : feasible_safety_wit_27
  proof_of_feasible_safety_wit_28 : feasible_safety_wit_28
  proof_of_feasible_safety_wit_29 : feasible_safety_wit_29
  proof_of_feasible_safety_wit_30 : feasible_safety_wit_30
  proof_of_feasible_safety_wit_31 : feasible_safety_wit_31
  proof_of_feasible_safety_wit_32 : feasible_safety_wit_32
  proof_of_feasible_safety_wit_33 : feasible_safety_wit_33
  proof_of_feasible_safety_wit_34 : feasible_safety_wit_34
  proof_of_feasible_partial_solve_wit_1 : feasible_partial_solve_wit_1
  proof_of_feasible_partial_solve_wit_2 : feasible_partial_solve_wit_2
  proof_of_feasible_partial_solve_wit_3 : feasible_partial_solve_wit_3
  proof_of_feasible_partial_solve_wit_4 : feasible_partial_solve_wit_4
  proof_of_feasible_partial_solve_wit_5 : feasible_partial_solve_wit_5
  proof_of_feasible_partial_solve_wit_6 : feasible_partial_solve_wit_6
  proof_of_feasible_partial_solve_wit_7 : feasible_partial_solve_wit_7
  proof_of_feasible_partial_solve_wit_8 : feasible_partial_solve_wit_8
  proof_of_feasible_partial_solve_wit_9 : feasible_partial_solve_wit_9
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1
  proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_feasible_safety_wit_1 : feasible_safety_wit_1
  proof_of_feasible_safety_wit_2 : feasible_safety_wit_2
  proof_of_feasible_safety_wit_14 : feasible_safety_wit_14
  proof_of_feasible_entail_wit_1 : feasible_entail_wit_1
  proof_of_feasible_entail_wit_2 : feasible_entail_wit_2
  proof_of_feasible_entail_wit_3 : feasible_entail_wit_3
  proof_of_feasible_entail_wit_4 : feasible_entail_wit_4
  proof_of_feasible_entail_wit_5_1 : feasible_entail_wit_5_1
  proof_of_feasible_entail_wit_5_2 : feasible_entail_wit_5_2
  proof_of_feasible_entail_wit_6_1 : feasible_entail_wit_6_1
  proof_of_feasible_entail_wit_6_2 : feasible_entail_wit_6_2
  proof_of_feasible_entail_wit_7 : feasible_entail_wit_7
  proof_of_feasible_entail_wit_8 : feasible_entail_wit_8
  proof_of_feasible_entail_wit_9_1 : feasible_entail_wit_9_1
  proof_of_feasible_entail_wit_9_2 : feasible_entail_wit_9_2
  proof_of_feasible_entail_wit_10_1 : feasible_entail_wit_10_1
  proof_of_feasible_entail_wit_10_2 : feasible_entail_wit_10_2
  proof_of_feasible_return_wit_1 : feasible_return_wit_1
  proof_of_feasible_return_wit_2 : feasible_return_wit_2
  proof_of_feasible_which_implies_wit_1 : feasible_which_implies_wit_1
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure
  proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure
  proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure
  proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1
  proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2
  proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3
  proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4
  proof_of_solver_which_implies_wit_5 : solver_which_implies_wit_5

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_goal
