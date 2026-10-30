import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P005_707A_brains_photos_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : (n_pre = (Zlength (photo)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH7 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH8 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (n_pre * m_pre))) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ ((n_pre * m_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * m_pre)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : (i < (n_pre * m_pre))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH9 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre * m_pre))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (67 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 67) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH2 : (i < (n_pre * m_pre))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH10 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre * m_pre))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (77 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 77) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH3 : (i < (n_pre * m_pre))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH11 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (n_pre * m_pre))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (89 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 89) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 77)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH3 : (i < (n_pre * m_pre))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH11 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (n_pre * m_pre))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 67)) (PreH2 : (i < (n_pre * m_pre))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH10 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre * m_pre))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 89)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH3 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH4 : (i < (n_pre * m_pre))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH12 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre * m_pre))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= (n_pre * m_pre))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH9 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre * m_pre))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 89)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH3 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH4 : (i < (n_pre * m_pre))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH12 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre * m_pre))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
  ** ((( &( "px" ) )) # Ptr |-> (px_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ (n_pre = (Zlength (photo))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” &&
  “ forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66)))) ” &&
  “ ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre * m_pre)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89))) ”
  &&  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
) \/
(
forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89))) ” &&
  “ ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre)) ” &&
  “ forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66)))) ” &&
  “ forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))

noncomputable def solver_entail_wit_1_split_goal_4 : Prop :=
  forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> forall (j : Int) , ((((0 : Int) <= j) ∧ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth j (Znth i_2 photo __default__List_Z) (0 : Int)) = 66))))) ,
  forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))

noncomputable def solver_entail_wit_2 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 89)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH3 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH4 : (i < (n_pre * m_pre))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH12 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre * m_pre))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ (n_pre = (Zlength (photo))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” &&
  “ forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66)))) ” &&
  “ ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre * m_pre)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (i + 1))) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89))) ”
  &&  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= (n_pre * m_pre))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH9 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre * m_pre))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
) \/
(
forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : (i >= (n_pre * m_pre))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH9 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre * m_pre))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  TT && emp 
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 77)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH3 : (i < (n_pre * m_pre))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH11 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (n_pre * m_pre))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
) \/
(
forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 77)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH3 : (i < (n_pre * m_pre))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH11 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (n_pre * m_pre))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  TT && emp 
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  emp
)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 67)) (PreH2 : (i < (n_pre * m_pre))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH10 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre * m_pre))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
) \/
(
forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 67)) (PreH2 : (i < (n_pre * m_pre))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH10 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre * m_pre))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  TT && emp 
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  emp
)

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 89)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH3 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH4 : (i < (n_pre * m_pre))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH12 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre * m_pre))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
) \/
(
forall (photo : (List (List Int))) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) = 89)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH3 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH4 : (i < (n_pre * m_pre))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH12 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre * m_pre))) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  TT && emp 
|--
  EX out : Bool,
  “ (Spec photo out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  emp
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : (i < (n_pre * m_pre))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH9 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (n_pre * m_pre))) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ (i < (n_pre * m_pre)) ” &&
  “ (n_pre = (Zlength (photo))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” &&
  “ forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66)))) ” &&
  “ ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre * m_pre)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89))) ”
  &&  (((px_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (List.flatten (photo)) (0 : Int))))
  ** (charArray.missing_i px_pre i (0 : Int) (n_pre * m_pre) (List.flatten (photo)))

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH2 : (i < (n_pre * m_pre))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH10 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre * m_pre))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67) ” &&
  “ (i < (n_pre * m_pre)) ” &&
  “ (n_pre = (Zlength (photo))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” &&
  “ forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66)))) ” &&
  “ ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre * m_pre)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89))) ”
  &&  (((px_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (List.flatten (photo)) (0 : Int))))
  ** (charArray.missing_i px_pre i (0 : Int) (n_pre * m_pre) (List.flatten (photo)))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (photo : (List (List Int))) (px_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77)) (PreH2 : ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67)) (PreH3 : (i < (n_pre * m_pre))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66))))) (PreH11 : ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (n_pre * m_pre))) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89)))) ,
  (charArray.full px_pre (n_pre * m_pre) (List.flatten (photo)))
|--
  “ ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 77) ” &&
  “ ((Znth i (List.flatten (photo)) (0 : Int)) ≠ 67) ” &&
  “ (i < (n_pre * m_pre)) ” &&
  “ (n_pre = (Zlength (photo))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 100) ” &&
  “ forall (r : Int) , ((((0 : Int) <= r) ∧ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” &&
  “ forall (r_2 : Int) , ((((0 : Int) <= r_2) ∧ (r_2 < n_pre)) -> forall (c : Int) , ((((0 : Int) <= c) ∧ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 67) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 77)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 89)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 87)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 71)) ∨ ((Znth c (Znth r_2 photo __default__List_Z) (0 : Int)) = 66)))) ” &&
  “ ((Zlength ((List.flatten (photo)))) = (n_pre * m_pre)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre * m_pre)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((((Znth k (List.flatten (photo)) (0 : Int)) ≠ 67) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 77)) ∧ ((Znth k (List.flatten (photo)) (0 : Int)) ≠ 89))) ”
  &&  (((px_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (List.flatten (photo)) (0 : Int))))
  ** (charArray.missing_i px_pre i (0 : Int) (n_pre * m_pre) (List.flatten (photo)))


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_goal
