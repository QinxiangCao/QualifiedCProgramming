import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.int_array_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance int_arrayStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def int_array_strategy101 : Prop :=
  forall (l : (List Int)) (n : Int) (p : Int),
    TT &&
    emp **
    ((intArray.full p n l))
    |--
    (
    TT &&
    (“ ((@Zlength Int l) = n) ”) &&
    emp **
    ((intArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy102 : Prop :=
  forall (l : (List Int)) (x : Int) (y : Int) (p : Int),
    TT &&
    emp **
    ((intArray.seg p x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Int l) = (y - x)) ”) &&
    emp **
    ((intArray.seg p x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy103 : Prop :=
  forall (l : (List Int)) (x : Int) (y : Int) (p : Int) (i : Int),
    TT &&
    emp **
    ((intArray.missing_i p i x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Int l) = (y - x)) ”) &&
    emp **
    ((intArray.missing_i p i x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy1 : Prop :=
  forall (i : Int) (n : Int) (p : Int) (l : (List Int)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((intArray.missing_i p i (0 : Int) n l))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (Znth i l (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def int_array_strategy4 : Prop :=
  forall (p : Int) (l1 : (List Int)) (n : Int),
    TT &&
    emp **
    ((intArray.full p n l1))
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
      ((intArray.full p n l2)))
      )

noncomputable def int_array_strategy5 : Prop :=
  forall (p : Int) (v : Int) (l : (List Int)) (n : Int) (i : Int),
    TT &&
    emp **
    ((intArray.missing_i p i v n l))
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
    ((intArray.missing_i p i v n l)))
    )

noncomputable def int_array_strategy6 : Prop :=
  forall (p : Int) (y : Int) (l1 : (List Int)) (x : Int),
    TT &&
    emp **
    ((intArray.seg p x y l1))
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
      ((intArray.seg p x y l2)))
      )

noncomputable def int_array_strategy17 : Prop :=
  forall (i : Int) (n : Int) (p : Int) (l1 : (List Int)),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((intArray.seg p (0 : Int) i l1))
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
      ((intArray.full p n l2)))
      )

noncomputable def int_array_strategy7 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (p : Int) (l : (List Int)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((intArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((intArray.missing_i p i x y l))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (Znth (i - x) l (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def int_array_strategy8 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (l1 : (List Int)) (p : Int) (l2 : (List Int)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((intArray.seg p x y l1)) **
    ((intArray.seg p y z l2))
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
      ((intArray.seg p x z l3)))
      )

noncomputable def int_array_strategy9 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int) (l3 : (List Int)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((intArray.seg p x z l3))
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
      ((intArray.seg p x y l1)) **
      ((intArray.seg p y z l2)))
      )

noncomputable def int_array_strategy10 : Prop :=
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
    ((intArray.seg p x x l)))
    )

noncomputable def int_array_strategy13 : Prop :=
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
      ((intArray.full p n l)))
      )

noncomputable def int_array_strategy2 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(INT)) # INT |-> ((Znth i l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((intArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy11 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((intArray.missing_i p i x y l)) **
    (((p + i * sizeof(INT)) # INT |-> ((Znth (i - x) l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((intArray.seg p x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy31 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(INT)) # INT |-> ((@Znth Int i l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((intArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy3 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((intArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.full p n (@replace_Znth Int i v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy12 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((intArray.missing_i p i x y l)) **
    (((p + i * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.seg p x y (@replace_Znth Int (i - x) v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy14 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((intArray.full p n l)) **
    (((p + i * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.full p (n + (1 : Int)) (@List.append Int l (@List.cons Int v (@List.nil Int)))))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy15 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (i = y) ”) &&
    emp **
    ((intArray.seg p x y l)) **
    (((p + i * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.seg p x (y + (1 : Int)) (@List.append Int l (@List.cons Int v (@List.nil Int)))))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def int_array_strategy16 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) < i) ”) &&
    emp **
    ((intArray.full (p + i * sizeof(INT)) n l)) **
    (((p + (i - (1 : Int)) * sizeof(INT)) # INT |-> (v)))
    |--
    (
    TT &&
    emp **
    ((intArray.full (p + (i - (1 : Int)) * sizeof(INT)) (n + (1 : Int)) (@List.cons Int v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure int_array_Strategy_Correct : Type where
  int_array_strategy101_correctness : int_array_strategy101
  int_array_strategy102_correctness : int_array_strategy102
  int_array_strategy103_correctness : int_array_strategy103
  int_array_strategy1_correctness : int_array_strategy1
  int_array_strategy4_correctness : int_array_strategy4
  int_array_strategy5_correctness : int_array_strategy5
  int_array_strategy6_correctness : int_array_strategy6
  int_array_strategy17_correctness : int_array_strategy17
  int_array_strategy7_correctness : int_array_strategy7
  int_array_strategy8_correctness : int_array_strategy8
  int_array_strategy9_correctness : int_array_strategy9
  int_array_strategy10_correctness : int_array_strategy10
  int_array_strategy13_correctness : int_array_strategy13
  int_array_strategy2_correctness : int_array_strategy2
  int_array_strategy11_correctness : int_array_strategy11
  int_array_strategy31_correctness : int_array_strategy31
  int_array_strategy3_correctness : int_array_strategy3
  int_array_strategy12_correctness : int_array_strategy12
  int_array_strategy14_correctness : int_array_strategy14
  int_array_strategy15_correctness : int_array_strategy15
  int_array_strategy16_correctness : int_array_strategy16

end SimpleC.EE.QCP_demos_LLM.generated.int_array_strategy_goal
