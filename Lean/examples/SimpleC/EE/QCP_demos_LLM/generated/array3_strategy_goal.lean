import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance array3StrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def array3_strategy1 : Prop :=
  forall (ak : Int) (k : Int) (i : Int) (n : Int) (m : Int) (am : Int) (p : Int) (cubes : (List (List (List Int)))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    emp **
    ((intArray3.full p n m k cubes))
    |--
    (
    TT &&
    emp **
    ((intArray3.missing_i p i (0 : Int) n m k cubes))
    ) ** (
    ALL plane : (List (List Int)), ALL __default_app1_app1_Z : (List (List Int)), 
(
      TT &&
      (“ (plane = (Znth i cubes __default_app1_app1_Z)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((intArray2.full (p + i * ((sizeof(INT) * ak) * am)) m k plane)))
      )

noncomputable def array3_strategy2 : Prop :=
  forall (ak2 : Int) (k : Int) (am : Int) (m : Int) (n : Int) (i : Int) (j : Int) (l : Int) (ak : Int) (__default_app1_app1_Z : (List (List Int))) (p : Int) (cubes : (List (List (List Int)))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < m) ”) &&
    (“ ((0 : Int) <= l) ”) &&
    (“ (l < k) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((intArray3.full p n m k cubes))
    |--
    (
    TT &&
    emp **
    ((intArray3.missing_i p i (0 : Int) n m k cubes)) **
    ((intArray2.full (p + i * ((sizeof(INT) * ak) * am)) m k (Znth i cubes __default_app1_app1_Z)))
    ) ** (
    ALL v : Int, 
(
      TT &&
      emp **
      (((((p + i * ((sizeof(INT) * ak) * am)) + j * (sizeof(INT) * ak2)) + l * sizeof(INT)) # INT |-> (v)))) -* (
      TT &&
      emp **
      (((((p + i * ((sizeof(INT) * ak) * am)) + j * (sizeof(INT) * ak2)) + l * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def array3_strategy6 : Prop :=
  forall (ak2 : Int) (k : Int) (am : Int) (m : Int) (n : Int) (i : Int) (ak : Int) (p : Int) (cubes : (List (List (List Int)))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((intArray3.full p n m k cubes))
    |--
    (
    TT &&
    emp **
    ((intArray3.missing_i p i (0 : Int) n m k cubes))
    ) ** (
    ALL plane : (List (List Int)), ALL __default_app1_app1_Z : (List (List Int)), 
(
      TT &&
      (“ (plane = (Znth i cubes __default_app1_app1_Z)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((intArray2.full ((p + i * ((sizeof(INT) * ak) * am)) + (0 : Int) * (sizeof(INT) * ak2)) m k plane)))
      )

noncomputable def array3_strategy4 : Prop :=
  forall (p : Int) (m : Int) (cubes1 : (List (List (List Int)))) (k : Int) (n : Int),
    TT &&
    emp **
    ((intArray3.full p n m k cubes1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL cubes2 : (List (List (List Int))), 
(
      TT &&
      (“ (cubes1 = cubes2) ”) &&
      emp) -* (
      TT &&
      emp **
      ((intArray3.full p n m k cubes2)))
      )

noncomputable def array3_strategy5 : Prop :=
  forall (p : Int) (lo : Int) (m : Int) (cubes : (List (List (List Int)))) (k : Int) (hi : Int) (i : Int),
    TT &&
    emp **
    ((intArray3.missing_i p i lo hi m k cubes))
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
    ((intArray3.missing_i p i lo hi m k cubes)))
    )

noncomputable def array3_strategy3 : Prop :=
  forall (ak : Int) (k : Int) (i : Int) (n : Int) (m : Int) (am : Int) (p : Int) (cubes : (List (List (List Int)))) (__default_app1_app1_Z : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    emp **
    ((intArray3.missing_i p i (0 : Int) n m k cubes)) **
    ((intArray2.full (p + i * ((sizeof(INT) * ak) * am)) m k (Znth i cubes __default_app1_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((intArray3.full p n m k cubes))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array3_strategy7 : Prop :=
  forall (ak2 : Int) (k : Int) (am : Int) (m : Int) (n : Int) (i : Int) (ak : Int) (p : Int) (cubes : (List (List (List Int)))) (__default_app1_app1_Z : (List (List Int))),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((intArray3.missing_i p i (0 : Int) n m k cubes)) **
    ((intArray2.full ((p + i * ((sizeof(INT) * ak) * am)) + (0 : Int) * (sizeof(INT) * ak2)) m k (Znth i cubes __default_app1_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((intArray3.full p n m k cubes))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure array3_Strategy_Correct : Type where
  array3_strategy1_correctness : array3_strategy1
  array3_strategy2_correctness : array3_strategy2
  array3_strategy6_correctness : array3_strategy6
  array3_strategy4_correctness : array3_strategy4
  array3_strategy5_correctness : array3_strategy5
  array3_strategy3_correctness : array3_strategy3
  array3_strategy7_correctness : array3_strategy7

end SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal
