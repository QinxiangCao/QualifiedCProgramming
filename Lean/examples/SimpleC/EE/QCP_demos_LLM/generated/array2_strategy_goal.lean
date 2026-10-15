import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance array2StrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def array2_strategy1 : Prop :=
  forall (j : Int) (m : Int) (i : Int) (n : Int) (__default_app1_Z : (List Int)) (p : Int) (rows : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((intArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.missing_i (p + (i * m) * sizeof(INT)) j (0 : Int) m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (@Znth Int j (Znth i rows __default_app1_Z) (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      ((((p + (i * m) * sizeof(INT)) + j * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def array2_strategy6 : Prop :=
  forall (j : Int) (m : Int) (i : Int) (n : Int) (__default_app1_Z : (List Int)) (p : Int) (rows : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((intArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.missing_i (p + (i * m) * sizeof(INT)) j (0 : Int) m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (@Znth Int j (Znth i rows __default_app1_Z) (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + ((i * m) + j) * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def array2_strategy7 : Prop :=
  forall (w : Int) (m : Int) (n : Int) (i : Int) (j : Int) (__default_app1_Z : (List Int)) (p : Int) (rows : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((intArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.missing_i (p + i * (sizeof(INT) * w)) j (0 : Int) m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (@Znth Int j (Znth i rows __default_app1_Z) (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      ((((p + i * (sizeof(INT) * w)) + j * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def array2_strategy4 : Prop :=
  forall (p : Int) (m : Int) (rows1 : (List (List Int))) (n : Int),
    TT &&
    emp **
    ((intArray2.full p n m rows1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL rows2 : (List (List Int)), 
(
      TT &&
      (“ (rows1 = rows2) ”) &&
      emp) -* (
      TT &&
      emp **
      ((intArray2.full p n m rows2)))
      )

noncomputable def array2_strategy5 : Prop :=
  forall (p : Int) (lo : Int) (m : Int) (rows : (List (List Int))) (hi : Int) (i : Int),
    TT &&
    emp **
    ((intArray2.missing_i p i lo hi m rows))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((intArray2.missing_i p i lo hi m rows)))
    )

noncomputable def array2_strategy2 : Prop :=
  forall (i : Int) (n : Int) (m : Int) (p : Int) (__default_app1_Z : (List Int)) (rows : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.full (p + (i * m) * sizeof(INT)) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((intArray2.full p n m rows))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array2_strategy8 : Prop :=
  forall (w : Int) (m : Int) (n : Int) (i : Int) (p : Int) (__default_app1_Z : (List Int)) (rows : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.full (p + i * (sizeof(INT) * w)) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((intArray2.full p n m rows))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array2_strategy9 : Prop :=
  forall (i : Int) (n : Int) (m : Int) (p : Int) (__default_app1_Z : (List Int)) (rows : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.full (p + (i * m) * sizeof(INT)) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((intArray2.full p n m rows))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array2_strategy10 : Prop :=
  forall (i : Int) (n : Int) (rows : (List (List Int))) (m : Int) (p : Int) (row : (List Int)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.full (p + (i * m) * sizeof(INT)) m row))
    |--
    (
    TT &&
    emp **
    ((intArray2.full p n m (@replace_Znth (List Int) i row rows)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array2_strategy11 : Prop :=
  forall (w : Int) (m : Int) (n : Int) (i : Int) (rows : (List (List Int))) (p : Int) (row : (List Int)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.full (p + i * (sizeof(INT) * w)) m row))
    |--
    (
    TT &&
    emp **
    ((intArray2.full p n m (@replace_Znth (List Int) i row rows)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array2_strategy12 : Prop :=
  forall (i : Int) (n : Int) (rows : (List (List Int))) (m : Int) (p : Int) (row : (List Int)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n m rows)) **
    ((intArray.full (p + (i * m) * sizeof(INT)) m row))
    |--
    (
    TT &&
    emp **
    ((intArray2.full p n m (@replace_Znth (List Int) i row rows)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure array2_Strategy_Correct : Type where
  array2_strategy1_correctness : array2_strategy1
  array2_strategy6_correctness : array2_strategy6
  array2_strategy7_correctness : array2_strategy7
  array2_strategy4_correctness : array2_strategy4
  array2_strategy5_correctness : array2_strategy5
  array2_strategy2_correctness : array2_strategy2
  array2_strategy8_correctness : array2_strategy8
  array2_strategy9_correctness : array2_strategy9
  array2_strategy10_correctness : array2_strategy10
  array2_strategy11_correctness : array2_strategy11
  array2_strategy12_correctness : array2_strategy12

end SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal
