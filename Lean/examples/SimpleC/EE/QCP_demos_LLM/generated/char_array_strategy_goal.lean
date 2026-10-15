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
  forall (n : Int) (p : Int) (l1 : (List Int)),
    TT &&
    emp **
    ((charArray.full p n l1))
    |--
    (
    TT &&
    (“ ((0 : Int) <= n) ”) &&
    emp **
    ((charArray.full p n l1))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def char_array_strategy7 : Prop :=
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

noncomputable def char_array_strategy8 : Prop :=
  forall (l : Int),
    TT &&
    (“ (l = (0 : Int)) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL p : Int, ALL r : Int, 
(
      TT &&
      emp **
      ((charArray.undef_full p r))) -* (
      TT &&
      emp **
      ((charArray.undef_seg p l r)))
      )

noncomputable def char_array_strategy9 : Prop :=
  forall (i : Int) (n : Int) (l : Int) (p : Int),
    TT &&
    (“ (l <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((charArray.undef_seg p l n))
    |--
    (
    TT &&
    emp **
    ((charArray.undef_missing_i p i l n))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    (((p + i * sizeof(CHAR)) # CHAR |->_)))
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
  forall (r : Int) (n : Int) (l : Int) (p : Int),
    TT &&
    (“ (l = r) ”) &&
    (“ (r < n) ”) &&
    emp **
    ((charArray.undef_missing_i p l r n))
    |--
    (
    TT &&
    emp **
    ((charArray.undef_seg p (l + (1 : Int)) n))
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

noncomputable def char_array_strategy10 : Prop :=
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

structure char_array_Strategy_Correct : Type where
  char_array_strategy1_correctness : char_array_strategy1
  char_array_strategy4_correctness : char_array_strategy4
  char_array_strategy5_correctness : char_array_strategy5
  char_array_strategy6_correctness : char_array_strategy6
  char_array_strategy7_correctness : char_array_strategy7
  char_array_strategy8_correctness : char_array_strategy8
  char_array_strategy9_correctness : char_array_strategy9
  char_array_strategy2_correctness : char_array_strategy2
  char_array_strategy11_correctness : char_array_strategy11
  char_array_strategy3_correctness : char_array_strategy3
  char_array_strategy10_correctness : char_array_strategy10

end SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal
