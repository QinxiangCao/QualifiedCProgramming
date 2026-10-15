import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance uint_arrayStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def uint_array_strategy1 : Prop :=
  forall (i : Int) (n : Int) (p : Int) (l : (List Int)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((uintArray.missing_i p i (0 : Int) n l))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (Znth i l (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(UINT)) # UINT |-> (v))))
      )

noncomputable def uint_array_strategy4 : Prop :=
  forall (p : Int) (l1 : (List Int)) (n : Int),
    TT &&
    emp **
    ((uintArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l2 : (List Int), 
(
      TT &&
      (“ (l1 = l2) ”) &&
      emp) -* (
      TT &&
      emp **
      ((uintArray.full p n l2)))
      )

noncomputable def uint_array_strategy5 : Prop :=
  forall (p : Int) (v : Int) (l : (List Int)) (n : Int) (i : Int),
    TT &&
    emp **
    ((uintArray.missing_i p i v n l))
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
    ((uintArray.missing_i p i v n l)))
    )

noncomputable def uint_array_strategy6 : Prop :=
  forall (p : Int) (y : Int) (l1 : (List Int)) (x : Int),
    TT &&
    emp **
    ((uintArray.seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l2 : (List Int), 
(
      TT &&
      (“ (l1 = l2) ”) &&
      emp) -* (
      TT &&
      emp **
      ((uintArray.seg p x y l2)))
      )

noncomputable def uint_array_strategy7 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (p : Int) (l : (List Int)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((uintArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((uintArray.missing_i p i x y l))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (Znth (i - x) l (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(UINT)) # UINT |-> (v))))
      )

noncomputable def uint_array_strategy8 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (l1 : (List Int)) (p : Int) (l2 : (List Int)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((uintArray.seg p x y l1)) **
    ((uintArray.seg p y z l2))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l3 : (List Int), 
(
      TT &&
      (“ (l3 = (@List.append Int l1 l2)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((uintArray.seg p x z l3)))
      )

noncomputable def uint_array_strategy9 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int) (l3 : (List Int)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((uintArray.seg p x z l3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List Int), ALL l2 : (List Int), 
(
      TT &&
      (“ (l3 = (@List.append Int l1 l2)) ”) &&
      (“ ((@Zlength Int l1) = (y - x)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((uintArray.seg p x y l1)) **
      ((uintArray.seg p y z l2)))
      )

noncomputable def uint_array_strategy10 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL p : Int, ALL x : Int, 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp) -* (
    TT &&
    emp **
    ((uintArray.seg p x x l)))
    )

noncomputable def uint_array_strategy13 : Prop :=
  forall (n : Int),
    TT &&
    (“ (n = (0 : Int)) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l : (List Int), ALL p : Int, 
(
      TT &&
      (“ (l = (@List.nil Int)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((uintArray.full p n l)))
      )

noncomputable def uint_array_strategy14 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL l1 : (List Int), ALL a : Int, ALL p : Int, ALL n : Int, 
(
    TT &&
    (“ (l = (@List.append Int l1 (@List.cons Int a (@List.nil Int)))) ”) &&
    emp **
    (((p + n * sizeof(UINT)) # UINT |-> (a))) **
    ((uintArray.full p n l1))) -* (
    TT &&
    emp **
    ((uintArray.full p (n + (1 : Int)) l)))
    )

noncomputable def uint_array_strategy2 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(UINT)) # UINT |-> ((Znth i l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((uintArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def uint_array_strategy11 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((uintArray.missing_i p i x y l)) **
    (((p + i * sizeof(UINT)) # UINT |-> ((Znth (i - x) l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((uintArray.seg p x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def uint_array_strategy3 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((uintArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(UINT)) # UINT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((uintArray.full p n (@replace_Znth Int i v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def uint_array_strategy12 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((uintArray.missing_i p i x y l)) **
    (((p + i * sizeof(UINT)) # UINT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((uintArray.seg p x y (@replace_Znth Int (i - x) v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure uint_array_Strategy_Correct : Type where
  uint_array_strategy1_correctness : uint_array_strategy1
  uint_array_strategy4_correctness : uint_array_strategy4
  uint_array_strategy5_correctness : uint_array_strategy5
  uint_array_strategy6_correctness : uint_array_strategy6
  uint_array_strategy7_correctness : uint_array_strategy7
  uint_array_strategy8_correctness : uint_array_strategy8
  uint_array_strategy9_correctness : uint_array_strategy9
  uint_array_strategy10_correctness : uint_array_strategy10
  uint_array_strategy13_correctness : uint_array_strategy13
  uint_array_strategy14_correctness : uint_array_strategy14
  uint_array_strategy2_correctness : uint_array_strategy2
  uint_array_strategy11_correctness : uint_array_strategy11
  uint_array_strategy3_correctness : uint_array_strategy3
  uint_array_strategy12_correctness : uint_array_strategy12

end SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal
