import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P002_1382A_common_subsequence_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solver_safety_wit_1 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH10 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH10 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (retval : Int) (PreH1 : (retval = (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH11 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (charArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 1001))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  (charArray.full ( &( "seen" ) ) 1001 (replace_Znth ((Znth i left (0 : Int))) (1) (seen_l)))
  ** (intArray.full a_pre n_pre left)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full b_pre m_pre right)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  (intArray.full a_pre n_pre left)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) (PreH17 : ((Znth (Znth j right (0 : Int)) seen_l (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "seen" ) ) 1001 seen_l)
  ** (intArray.full b_pre m_pre right)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre left)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i left (0 : Int))) ∧ ((Znth i left (0 : Int)) <= 1000)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right (0 : Int))) ∧ ((Znth i_2 right (0 : Int)) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))) ,
  (charArray.undef_full ( &( "seen" ) ) 1001)
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (sizeof(CHAR) * 1001)) ” &&
  “ ((sizeof(CHAR) * 1001) < INT_MAX) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
) \/
(
forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i left (0 : Int))) ∧ ((Znth i left (0 : Int)) <= 1000)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right (0 : Int))) ∧ ((Znth i_2 right (0 : Int)) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))) ,
  (charArray.undef_full ( &( "seen" ) ) 1001)
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ”
  &&  (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i left (0 : Int))) ∧ ((Znth i left (0 : Int)) <= 1000)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right (0 : Int))) ∧ ((Znth i_2 right (0 : Int)) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))) ,
  (charArray.undef_full ( &( "seen" ) ) 1001)
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ”

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i left (0 : Int))) ∧ ((Znth i left (0 : Int)) <= 1000)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right (0 : Int))) ∧ ((Znth i_2 right (0 : Int)) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))) ,
  (charArray.undef_full ( &( "seen" ) ) 1001)
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ”

noncomputable def solver_entail_wit_1_split_goal_spatial : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i left (0 : Int))) ∧ ((Znth i left (0 : Int)) <= 1000)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((1 <= (Znth i_2 right (0 : Int))) ∧ ((Znth i_2 right (0 : Int)) <= 1000)))) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : (m_pre = (Zlength (right)))) ,
  (charArray.undef_full ( &( "seen" ) ) 1001)
|--
  (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (retval : Int) (k_4 : Int) (PreH1 : (retval = (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> ((1 <= (Znth k_5 left (0 : Int))) ∧ ((Znth k_5 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < m_pre)) -> ((1 <= (Znth k_6 right (0 : Int))) ∧ ((Znth k_6 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH11 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  (charArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 1001))))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
|--
  EX seen_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < (0 : Int))) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
) \/
(
forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (retval : Int) (k_4 : Int) (PreH1 : (retval = (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < n_pre)) -> ((1 <= (Znth k_5 left (0 : Int))) ∧ ((Znth k_5 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < m_pre)) -> ((1 <= (Znth k_6 right (0 : Int))) ∧ ((Znth k_6 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH11 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  (charArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 1001))))
|--
  EX seen_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < (0 : Int))) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ”
  &&  (charArray.full ( &( "seen" ) ) 1001 seen_l)
)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l_2 (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  (charArray.full ( &( "seen" ) ) 1001 (replace_Znth ((Znth i left (0 : Int))) (1) (seen_l_2)))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
|--
  EX seen_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < (i + 1))) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
) \/
(
forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l_2 (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth ((Znth i left (0 : Int))) (1) (seen_l_2)))) = 1001) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l_2 (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  ((Zlength ((replace_Znth ((Znth i left (0 : Int))) (1) (seen_l_2)))) = 1001)

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (k_4 : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l_2)
|--
  EX seen_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ” &&
  “ forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < (0 : Int))) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int))) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
) \/
(
forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (k_4 : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  TT && emp 
|--
  “ forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < (0 : Int))) -> ((Znth (Znth k_5 right (0 : Int)) seen_l_2 (0 : Int)) = (0 : Int))) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l_2 (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l_2 (0 : Int)) = 1)) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l_2 (0 : Int)) = 1))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < (0 : Int))) -> ((Znth (Znth k_5 right (0 : Int)) seen_l_2 (0 : Int)) = (0 : Int)))

noncomputable def solver_entail_wit_4_split_goal_2 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (k_4 : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l_2 (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))

noncomputable def solver_entail_wit_4_split_goal_3 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l_2 (0 : Int)) = 1))

noncomputable def solver_entail_wit_4_split_goal_4 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l_2 (0 : Int)) = 1)))

noncomputable def solver_entail_wit_4_split_goal_5 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))

noncomputable def solver_entail_wit_4_split_goal_6 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (n_pre : Int) (m_pre : Int) (k_9 : Int) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k_6 : Int) , ((((0 : Int) <= k_6) ∧ (k_6 < n_pre)) -> ((1 <= (Znth k_6 left (0 : Int))) ∧ ((Znth k_6 left (0 : Int)) <= 1000)))) (PreH9 : forall (k_7 : Int) , ((((0 : Int) <= k_7) ∧ (k_7 < m_pre)) -> ((1 <= (Znth k_7 right (0 : Int))) ∧ ((Znth k_7 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v_3 : Int) , ((((0 : Int) <= v_3) ∧ (v_3 < 1001)) -> (((Znth v_3 seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v_3 seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_8 : Int) , ((((0 : Int) <= k_8) ∧ (k_8 < i)) -> ((Znth (Znth k_8 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_4 : Int) , (((((0 : Int) <= v_4) ∧ (v_4 < 1001)) ∧ ((Znth v_4 seen_l_2 (0 : Int)) = 1)) -> exists (k_9 : Int) , ((((0 : Int) <= k_9) ∧ (k_9 < i)) ∧ ((Znth k_9 left (0 : Int)) = v_4)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))

noncomputable def solver_entail_wit_5 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l_2 : (List Int)) (j : Int) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l_2)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l_2 (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l_2 (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l_2 (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l_2 (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l_2 (0 : Int)) = (0 : Int)))) (PreH17 : ((Znth (Znth j right (0 : Int)) seen_l_2 (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "seen" ) ) 1001 seen_l_2)
  ** (intArray.full b_pre m_pre right)
  ** (intArray.full a_pre n_pre left)
|--
  EX seen_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= m_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ” &&
  “ forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < (j + 1))) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int))) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)

noncomputable def solver_return_wit_1 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) ,
  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
|--
  (EX out : (Option (List Int)),
  “ (Spec left right out) ” &&
  “ (out = None) ” &&
  “ ((0 : Int) = (0 : Int)) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right))
  ||
  (EX out : (Option (List Int)),
  “ (Spec left right out) ” &&
  “ (out = (Some (((0 : Int) :: (@List.nil Int))))) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right))

noncomputable def solver_return_wit_2 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) (PreH17 : ((Znth (Znth j right (0 : Int)) seen_l (0 : Int)) ≠ (0 : Int))) ,
  (intArray.full b_pre m_pre right)
  ** (intArray.full a_pre n_pre left)
|--
  (EX out : (Option (List Int)),
  “ (Spec left right out) ” &&
  “ (out = None) ” &&
  “ ((Znth j right (0 : Int)) = (0 : Int)) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right))
  ||
  (EX out : (Option (List Int)),
  “ (Spec left right out) ” &&
  “ (out = (Some (((Znth j right (0 : Int)) :: (@List.nil Int))))) ”
  &&  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right))

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH10 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
|--
  “ ((0 : Int) <= (sizeof(CHAR) * 1001)) ” &&
  “ ((sizeof(CHAR) * 1001) < INT_MAX) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 127) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : (m_pre = (Zlength (right)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 1001))) (PreH10 : ((sizeof(CHAR) * 1001) < INT_MAX)) ,
  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
|--
  “ ((0 : Int) <= (sizeof(CHAR) * 1001)) ” &&
  “ ((sizeof(CHAR) * 1001) < INT_MAX) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 127) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= (sizeof(CHAR) * 1001)) ” &&
  “ ((sizeof(CHAR) * 1001) < INT_MAX) ”
  &&  (charArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 1001))
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i left (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) ,
  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < i)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ”
  &&  (((( &( "seen" ) ) + ((Znth i left (0 : Int)) * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i ( &( "seen" ) ) (Znth i left (0 : Int)) (0 : Int) 1001 seen_l)
  ** (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) ,
  (intArray.full a_pre n_pre left)
  ** (intArray.full b_pre m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ (j < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= m_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ” &&
  “ forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int))) ”
  &&  (((b_pre + (j * sizeof(INT)))) # Int |-> ((Znth j right (0 : Int))))
  ** (intArray.missing_i b_pre j (0 : Int) m_pre right)
  ** (intArray.full a_pre n_pre left)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) ,
  (intArray.full b_pre m_pre right)
  ** (intArray.full a_pre n_pre left)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
|--
  “ (j < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= m_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ” &&
  “ forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int))) ”
  &&  (((( &( "seen" ) ) + ((Znth j right (0 : Int)) * sizeof(CHAR)))) # Char |-> ((Znth (Znth j right (0 : Int)) seen_l (0 : Int))))
  ** (charArray.missing_i ( &( "seen" ) ) (Znth j right (0 : Int)) (0 : Int) 1001 seen_l)
  ** (intArray.full b_pre m_pre right)
  ** (intArray.full a_pre n_pre left)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (right : (List Int)) (left : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (m_pre : Int) (k_4 : Int) (seen_l : (List Int)) (j : Int) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000)) (PreH6 : (n_pre = (Zlength (left)))) (PreH7 : (m_pre = (Zlength (right)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000)))) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000)))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= m_pre)) (PreH12 : ((Zlength (seen_l)) = 1001)) (PreH13 : forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1)))) (PreH14 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1))) (PreH15 : forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2)))) (PreH16 : forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int)))) (PreH17 : ((Znth (Znth j right (0 : Int)) seen_l (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "seen" ) ) 1001 seen_l)
  ** (intArray.full b_pre m_pre right)
  ** (intArray.full a_pre n_pre left)
|--
  “ (j < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000) ” &&
  “ (n_pre = (Zlength (left))) ” &&
  “ (m_pre = (Zlength (right))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k left (0 : Int))) ∧ ((Znth k left (0 : Int)) <= 1000))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < m_pre)) -> ((1 <= (Znth k_2 right (0 : Int))) ∧ ((Znth k_2 right (0 : Int)) <= 1000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= m_pre) ” &&
  “ ((Zlength (seen_l)) = 1001) ” &&
  “ forall (v : Int) , ((((0 : Int) <= v) ∧ (v < 1001)) -> (((Znth v seen_l (0 : Int)) = (0 : Int)) ∨ ((Znth v seen_l (0 : Int)) = 1))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((Znth (Znth k_3 left (0 : Int)) seen_l (0 : Int)) = 1)) ” &&
  “ forall (v_2 : Int) , (((((0 : Int) <= v_2) ∧ (v_2 < 1001)) ∧ ((Znth v_2 seen_l (0 : Int)) = 1)) -> exists (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) ∧ ((Znth k_4 left (0 : Int)) = v_2))) ” &&
  “ forall (k_5 : Int) , ((((0 : Int) <= k_5) ∧ (k_5 < j)) -> ((Znth (Znth k_5 right (0 : Int)) seen_l (0 : Int)) = (0 : Int))) ” &&
  “ ((Znth (Znth j right (0 : Int)) seen_l (0 : Int)) ≠ (0 : Int)) ”
  &&  (((b_pre + (j * sizeof(INT)))) # Int |-> ((Znth j right (0 : Int))))
  ** (intArray.missing_i b_pre j (0 : Int) m_pre right)
  ** (charArray.full ( &( "seen" ) ) 1001 seen_l)
  ** (intArray.full a_pre n_pre left)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_goal
