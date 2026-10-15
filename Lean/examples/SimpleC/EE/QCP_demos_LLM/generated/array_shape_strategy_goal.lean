import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance array_shapeStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def array_shape_strategy1 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.full_shape p n))
    |--
    EX x : Int, 
      (
      TT &&
      emp **
      ((uintArray.missing_i_shape p i (0 : Int) n)) **
      (((p + i * sizeof(UINT)) # UINT |-> (x)))
      ) ** (
      ALL v : Int, 
(
        TT &&
        emp **
        (((p + i * sizeof(UINT)) # UINT |-> (v)))) -* (
        TT &&
        emp **
        (((p + i * sizeof(UINT)) # UINT |-> (v))))
        )

noncomputable def array_shape_strategy3 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((uintArray.seg_shape p x y))
    |--
    EX v0 : Int, 
      (
      TT &&
      emp **
      ((uintArray.seg_shape p (x + (1 : Int)) y)) **
      (((p + x * sizeof(UINT)) # UINT |-> (v0)))
      ) ** (
      ALL v : Int, 
(
        TT &&
        emp **
        (((p + x * sizeof(UINT)) # UINT |-> (v)))) -* (
        TT &&
        emp **
        (((p + x * sizeof(UINT)) # UINT |-> (v))))
        )

noncomputable def array_shape_strategy6 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((uintArray.seg_shape p x y))
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

noncomputable def array_shape_strategy7 : Prop :=
  forall (x : Int) (y : Int),
    TT &&
    (“ (x = y) ”) &&
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
      ((uintArray.seg_shape p x y)))
      )

noncomputable def array_shape_strategy8 : Prop :=
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
      ((uintArray.full_shape p n)))
      )

noncomputable def array_shape_strategy9 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((uintArray.seg_shape p (0 : Int) i))
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
    ((uintArray.full_shape p n)))
    )

noncomputable def array_shape_strategy10 : Prop :=
  forall (y1 : Int) (y : Int) (p : Int) (x : Int),
    TT &&
    (“ (y1 = y) ”) &&
    emp **
    ((uintArray.seg_shape p x y))
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
    ((uintArray.seg_shape p x y1)))
    )

noncomputable def array_shape_strategy11 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.full_shape p n))
    |--
    EX x : Int, 
      (
      TT &&
      emp **
      ((intArray.missing_i_shape p i (0 : Int) n)) **
      (((p + i * sizeof(INT)) # INT |-> (x)))
      ) ** (
      ALL v : Int, 
(
        TT &&
        emp **
        (((p + i * sizeof(INT)) # INT |-> (v)))) -* (
        TT &&
        emp **
        (((p + i * sizeof(INT)) # INT |-> (v))))
        )

noncomputable def array_shape_strategy13 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((intArray.seg_shape p x y))
    |--
    EX v0 : Int, 
      (
      TT &&
      emp **
      (((p + x * sizeof(INT)) # INT |-> (v0))) **
      ((intArray.seg_shape p (x + (1 : Int)) y))
      ) ** (
      ALL v : Int, 
(
        TT &&
        emp **
        (((p + x * sizeof(INT)) # INT |-> (v)))) -* (
        TT &&
        emp **
        (((p + x * sizeof(INT)) # INT |-> (v))))
        )

noncomputable def array_shape_strategy16 : Prop :=
  forall (x : Int) (y : Int) (p : Int),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((intArray.seg_shape p x y))
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

noncomputable def array_shape_strategy17 : Prop :=
  forall (x : Int) (y : Int),
    TT &&
    (“ (x = y) ”) &&
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
      ((intArray.seg_shape p x y)))
      )

noncomputable def array_shape_strategy18 : Prop :=
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
      ((intArray.full_shape p n)))
      )

noncomputable def array_shape_strategy19 : Prop :=
  forall (i : Int) (n : Int) (p : Int),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((intArray.seg_shape p (0 : Int) i))
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
    ((intArray.full_shape p n)))
    )

noncomputable def array_shape_strategy20 : Prop :=
  forall (y1 : Int) (y : Int) (p : Int) (x : Int),
    TT &&
    (“ (y1 = y) ”) &&
    emp **
    ((intArray.seg_shape p x y))
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
    ((intArray.seg_shape p x y1)))
    )

noncomputable def array_shape_strategy2 : Prop :=
  forall (i : Int) (n : Int) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.missing_i_shape p i (0 : Int) n)) **
    (((p + i * sizeof(UINT)) # UINT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((uintArray.full_shape p n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array_shape_strategy4 : Prop :=
  forall (x : Int) (i : Int) (y : Int) (v : Int) (p : Int),
    TT &&
    (“ (x = (i + (1 : Int))) ”) &&
    emp **
    ((uintArray.seg_shape p x y)) **
    (((p + i * sizeof(UINT)) # UINT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((uintArray.seg_shape p i y))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array_shape_strategy5 : Prop :=
  forall (y : Int) (v : Int) (p : Int) (z : Int),
    TT &&
    emp **
    ((uintArray.seg_shape p y z)) **
    (((p + z * sizeof(UINT)) # UINT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((uintArray.seg_shape p y (z + (1 : Int))))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array_shape_strategy12 : Prop :=
  forall (i : Int) (n : Int) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.missing_i_shape p i (0 : Int) n)) **
    (((p + i * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.full_shape p n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array_shape_strategy14 : Prop :=
  forall (x : Int) (i : Int) (y : Int) (v : Int) (p : Int),
    TT &&
    (“ (x = (i + (1 : Int))) ”) &&
    emp **
    ((intArray.seg_shape p x y)) **
    (((p + i * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.seg_shape p i y))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def array_shape_strategy15 : Prop :=
  forall (y : Int) (v : Int) (p : Int) (z : Int),
    TT &&
    emp **
    ((intArray.seg_shape p y z)) **
    (((p + z * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.seg_shape p y (z + (1 : Int))))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure array_shape_Strategy_Correct : Type where
  array_shape_strategy1_correctness : array_shape_strategy1
  array_shape_strategy3_correctness : array_shape_strategy3
  array_shape_strategy6_correctness : array_shape_strategy6
  array_shape_strategy7_correctness : array_shape_strategy7
  array_shape_strategy8_correctness : array_shape_strategy8
  array_shape_strategy9_correctness : array_shape_strategy9
  array_shape_strategy10_correctness : array_shape_strategy10
  array_shape_strategy11_correctness : array_shape_strategy11
  array_shape_strategy13_correctness : array_shape_strategy13
  array_shape_strategy16_correctness : array_shape_strategy16
  array_shape_strategy17_correctness : array_shape_strategy17
  array_shape_strategy18_correctness : array_shape_strategy18
  array_shape_strategy19_correctness : array_shape_strategy19
  array_shape_strategy20_correctness : array_shape_strategy20
  array_shape_strategy2_correctness : array_shape_strategy2
  array_shape_strategy4_correctness : array_shape_strategy4
  array_shape_strategy5_correctness : array_shape_strategy5
  array_shape_strategy12_correctness : array_shape_strategy12
  array_shape_strategy14_correctness : array_shape_strategy14
  array_shape_strategy15_correctness : array_shape_strategy15

end SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal
