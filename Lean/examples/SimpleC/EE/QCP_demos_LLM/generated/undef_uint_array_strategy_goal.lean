import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance undef_uint_arrayStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def undef_uint_array_strategy3 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((uintArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((uintArray.undef_seg p (x + (1 : Int)) y))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + x * sizeof(UINT)) # UINT |->_)))
    )

noncomputable def undef_uint_array_strategy4 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((uintArray.undef_seg p x y)) **
    ((uintArray.undef_seg p y z))
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
    ((uintArray.undef_seg p x z)))
    )

noncomputable def undef_uint_array_strategy5 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((uintArray.undef_seg p x z))
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
    ((uintArray.undef_seg p x y)) **
    ((uintArray.undef_seg p y z)))
    )

noncomputable def undef_uint_array_strategy6 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL p : Int, ALL x : Int, 
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((uintArray.undef_seg p x x)))
    )

noncomputable def undef_uint_array_strategy7 : Prop :=
  forall (p : Int) (n : Int),
    TT &&
    emp **
    ((uintArray.undef_full p n))
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
    ((uintArray.undef_seg p (0 : Int) n)))
    )

noncomputable def undef_uint_array_strategy8 : Prop :=
  forall (n : Int),
    TT &&
    (“ (n = (0 : Int)) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL p : Int, 
(
      TT &&
      emp) -* (
      TT &&
      emp **
      ((uintArray.undef_full p n)))
      )

noncomputable def undef_uint_array_strategy9 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((uintArray.undef_seg p x y))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def undef_uint_array_strategy10 : Prop :=
  forall (x1 : Int) (x : Int) (y : Int) (y1 : Int) (p : Int),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((uintArray.undef_seg p x y))
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
    ((uintArray.undef_seg p x1 y1)))
    )

noncomputable def undef_uint_array_strategy13 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((intArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((intArray.undef_seg p (x + (1 : Int)) y))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + x * sizeof(INT)) # INT |->_)))
    )

noncomputable def undef_uint_array_strategy14 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((intArray.undef_seg p x y)) **
    ((intArray.undef_seg p y z))
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
    ((intArray.undef_seg p x z)))
    )

noncomputable def undef_uint_array_strategy15 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((intArray.undef_seg p x z))
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
    ((intArray.undef_seg p x y)) **
    ((intArray.undef_seg p y z)))
    )

noncomputable def undef_uint_array_strategy16 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL p : Int, ALL x : Int, 
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((intArray.undef_seg p x x)))
    )

noncomputable def undef_uint_array_strategy17 : Prop :=
  forall (p : Int) (n : Int),
    TT &&
    emp **
    ((intArray.undef_full p n))
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
    ((intArray.undef_seg p (0 : Int) n)))
    )

noncomputable def undef_uint_array_strategy18 : Prop :=
  forall (n : Int),
    TT &&
    (“ (n = (0 : Int)) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL p : Int, 
(
      TT &&
      emp) -* (
      TT &&
      emp **
      ((intArray.undef_full p n)))
      )

noncomputable def undef_uint_array_strategy19 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((intArray.undef_seg p x y))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def undef_uint_array_strategy20 : Prop :=
  forall (x1 : Int) (x : Int) (y : Int) (y1 : Int) (p : Int),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((intArray.undef_seg p x y))
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
    ((intArray.undef_seg p x1 y1)))
    )

noncomputable def undef_uint_array_strategy21 : Prop :=
  forall (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) < n) ”) &&
    emp **
    ((uintArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((uintArray.undef_seg p (1 : Int) n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + (0 : Int) * sizeof(UINT)) # UINT |->_)))
    )

noncomputable def undef_uint_array_strategy22 : Prop :=
  forall (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) < n) ”) &&
    emp **
    ((intArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((intArray.undef_seg p (1 : Int) n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + (0 : Int) * sizeof(INT)) # INT |->_)))
    )

noncomputable def undef_uint_array_strategy2 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.undef_missing_i p i (0 : Int) n)) **
    (((p + i * sizeof(UINT)) # UINT |->_))
    |--
    (
    TT &&
    emp **
    ((uintArray.undef_full p n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def undef_uint_array_strategy12 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.undef_missing_i p i (0 : Int) n)) **
    (((p + i * sizeof(INT)) # INT |->_))
    |--
    (
    TT &&
    emp **
    ((intArray.undef_full p n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def undef_uint_array_strategy1 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((uintArray.undef_missing_i p i (0 : Int) n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + i * sizeof(UINT)) # UINT |->_)))
    )

noncomputable def undef_uint_array_strategy11 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((intArray.undef_missing_i p i (0 : Int) n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + i * sizeof(INT)) # INT |->_)))
    )

structure undef_uint_array_Strategy_Correct : Type where
  undef_uint_array_strategy3_correctness : undef_uint_array_strategy3
  undef_uint_array_strategy4_correctness : undef_uint_array_strategy4
  undef_uint_array_strategy5_correctness : undef_uint_array_strategy5
  undef_uint_array_strategy6_correctness : undef_uint_array_strategy6
  undef_uint_array_strategy7_correctness : undef_uint_array_strategy7
  undef_uint_array_strategy8_correctness : undef_uint_array_strategy8
  undef_uint_array_strategy9_correctness : undef_uint_array_strategy9
  undef_uint_array_strategy10_correctness : undef_uint_array_strategy10
  undef_uint_array_strategy13_correctness : undef_uint_array_strategy13
  undef_uint_array_strategy14_correctness : undef_uint_array_strategy14
  undef_uint_array_strategy15_correctness : undef_uint_array_strategy15
  undef_uint_array_strategy16_correctness : undef_uint_array_strategy16
  undef_uint_array_strategy17_correctness : undef_uint_array_strategy17
  undef_uint_array_strategy18_correctness : undef_uint_array_strategy18
  undef_uint_array_strategy19_correctness : undef_uint_array_strategy19
  undef_uint_array_strategy20_correctness : undef_uint_array_strategy20
  undef_uint_array_strategy21_correctness : undef_uint_array_strategy21
  undef_uint_array_strategy22_correctness : undef_uint_array_strategy22
  undef_uint_array_strategy2_correctness : undef_uint_array_strategy2
  undef_uint_array_strategy12_correctness : undef_uint_array_strategy12
  undef_uint_array_strategy1_correctness : undef_uint_array_strategy1
  undef_uint_array_strategy11_correctness : undef_uint_array_strategy11

end SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal
