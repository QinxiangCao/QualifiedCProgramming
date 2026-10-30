import SimpleC.SL.LeanPrinterPrelude

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance char_arrayStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def char_array_strategy101 : Prop :=
  forall (l : (List Int)) (n : Int) (p : Int),
    TT &&
    emp **
    ((charArray.full p n l))
    |--
    (
    TT &&
    (“ ((@Zlength Int l) = n) ”) &&
    emp **
    ((charArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy102 : Prop :=
  forall (l : (List Int)) (x : Int) (y : Int) (p : Int),
    TT &&
    emp **
    ((charArray.seg p x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Int l) = (y - x)) ”) &&
    emp **
    ((charArray.seg p x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy103 : Prop :=
  forall (l : (List Int)) (x : Int) (y : Int) (p : Int) (i : Int),
    TT &&
    emp **
    ((charArray.missing_i p i x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Int l) = (y - x)) ”) &&
    emp **
    ((charArray.missing_i p i x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy1 : Prop :=
  forall (i : Int) (n : Int) (p : Int) (l : (List Int)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((charArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((charArray.missing_i p i (0 : Int) n l))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (Znth i l (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(CHAR)) # CHAR |-> (v))))
      )

noncomputable def char_array_strategy4 : Prop :=
  forall (p : Int) (l1 : (List Int)) (n : Int),
    TT &&
    emp **
    ((charArray.full p n l1))
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
      ((charArray.full p n l2)))
      )

noncomputable def char_array_strategy5 : Prop :=
  forall (p : Int) (v : Int) (l : (List Int)) (n : Int) (i : Int),
    TT &&
    emp **
    ((charArray.missing_i p i v n l))
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
    ((charArray.missing_i p i v n l)))
    )

noncomputable def char_array_strategy6 : Prop :=
  forall (p : Int) (y : Int) (l1 : (List Int)) (x : Int),
    TT &&
    emp **
    ((charArray.seg p x y l1))
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
      ((charArray.seg p x y l2)))
      )

noncomputable def char_array_strategy17 : Prop :=
  forall (i : Int) (n : Int) (p : Int) (l1 : (List Int)),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((charArray.seg p (0 : Int) i l1))
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
      ((charArray.full p n l2)))
      )

noncomputable def char_array_strategy7 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (p : Int) (l : (List Int)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((charArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((charArray.missing_i p i x y l))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (Znth (i - x) l (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(CHAR)) # CHAR |-> (v))))
      )

noncomputable def char_array_strategy8 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (l1 : (List Int)) (p : Int) (l2 : (List Int)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((charArray.seg p x y l1)) **
    ((charArray.seg p y z l2))
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
      ((charArray.seg p x z l3)))
      )

noncomputable def char_array_strategy9 : Prop :=
  forall (x : Int) (y : Int) (z : Int) (p : Int) (l3 : (List Int)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((charArray.seg p x z l3))
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
      ((charArray.seg p x y l1)) **
      ((charArray.seg p y z l2)))
      )

noncomputable def char_array_strategy10 : Prop :=
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
    ((charArray.seg p x x l)))
    )

noncomputable def char_array_strategy13 : Prop :=
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
      ((charArray.full p n l)))
      )

noncomputable def char_array_strategy2 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((charArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> ((Znth i l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((charArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy11 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((charArray.missing_i p i x y l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> ((Znth (i - x) l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((charArray.seg p x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy31 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((charArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> ((@Znth Int i l (0 : Int)))))
    |--
    (
    TT &&
    emp **
    ((charArray.full p n l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy3 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((charArray.missing_i p i (0 : Int) n l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> (v)))
    |--
    (
    TT &&
    emp **
    ((charArray.full p n (@replace_Znth Int i v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy12 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((charArray.missing_i p i x y l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> (v)))
    |--
    (
    TT &&
    emp **
    ((charArray.seg p x y (@replace_Znth Int (i - x) v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy14 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((charArray.full p n l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> (v)))
    |--
    (
    TT &&
    emp **
    ((charArray.full p (n + (1 : Int)) (@List.append Int l (@List.cons Int v (@List.nil Int)))))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy15 : Prop :=
  forall (i : Int) (y : Int) (x : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ (i = y) ”) &&
    emp **
    ((charArray.seg p x y l)) **
    (((p + i * sizeof(CHAR)) # CHAR |-> (v)))
    |--
    (
    TT &&
    emp **
    ((charArray.seg p x (y + (1 : Int)) (@List.append Int l (@List.cons Int v (@List.nil Int)))))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy16 : Prop :=
  forall (i : Int) (n : Int) (l : (List Int)) (v : Int) (p : Int),
    TT &&
    (“ ((0 : Int) < i) ”) &&
    emp **
    ((charArray.full (p + i * sizeof(CHAR)) n l)) **
    (((p + (i - (1 : Int)) * sizeof(CHAR)) # CHAR |-> (v)))
    |--
    (
    TT &&
    emp **
    ((charArray.full (p + (i - (1 : Int)) * sizeof(CHAR)) (n + (1 : Int)) (@List.cons Int v l)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure char_array_Strategy_Correct : Type where
  char_array_strategy101_correctness : char_array_strategy101
  char_array_strategy102_correctness : char_array_strategy102
  char_array_strategy103_correctness : char_array_strategy103
  char_array_strategy1_correctness : char_array_strategy1
  char_array_strategy4_correctness : char_array_strategy4
  char_array_strategy5_correctness : char_array_strategy5
  char_array_strategy6_correctness : char_array_strategy6
  char_array_strategy17_correctness : char_array_strategy17
  char_array_strategy7_correctness : char_array_strategy7
  char_array_strategy8_correctness : char_array_strategy8
  char_array_strategy9_correctness : char_array_strategy9
  char_array_strategy10_correctness : char_array_strategy10
  char_array_strategy13_correctness : char_array_strategy13
  char_array_strategy2_correctness : char_array_strategy2
  char_array_strategy11_correctness : char_array_strategy11
  char_array_strategy31_correctness : char_array_strategy31
  char_array_strategy3_correctness : char_array_strategy3
  char_array_strategy12_correctness : char_array_strategy12
  char_array_strategy14_correctness : char_array_strategy14
  char_array_strategy15_correctness : char_array_strategy15
  char_array_strategy16_correctness : char_array_strategy16

end SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal
