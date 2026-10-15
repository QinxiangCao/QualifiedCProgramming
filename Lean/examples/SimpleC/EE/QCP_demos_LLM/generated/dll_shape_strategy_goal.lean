import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.dll_shape_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.dll_shape_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance dll_shapeStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def dll_shape_strategy1 : Prop :=
  forall (x : Int),
    TT &&
    emp **
    ((dlistrep_shape (0 : Int) x))
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

noncomputable def dll_shape_strategy2 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL x : Int, 
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((dlistrep_shape (0 : Int) x)))
    )

noncomputable def dll_shape_strategy3 : Prop :=
  forall (p : Int),
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp
    |--
    (
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp
    ) ** (
    ALL x : Int, 
(
      TT &&
      emp) -* (
      TT &&
      emp **
      ((dlistrep_shape p x)))
      )

noncomputable def dll_shape_strategy4 : Prop :=
  forall (p : Int) (x : Int),
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp **
    ((dlistrep_shape p x))
    |--
    (
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def dll_shape_strategy12 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL x : Int, ALL q : Int, ALL r : Int, ALL p : Int, 
(
    TT &&
    (“ (q = r) ”) &&
    (“ (x = q) ”) &&
    emp **
    ((dlistrep_shape p x))) -* (
    TT &&
    emp **
    ((dllseg_shape p q r p)) **
    ((dlistrep_shape p x)))
    )

noncomputable def dll_shape_strategy7 : Prop :=
  forall (q : Int) (x : Int) (p : Int) (r : Int) (s : Int),
    TT &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg_shape p q r s))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp **
    ((dlistrep_shape s r))) -* (
    TT &&
    emp **
    ((dlistrep_shape p x)))
    )

noncomputable def dll_shape_strategy13 : Prop :=
  forall (s : Int) (n : Int) (m : Int),
    TT &&
    (“ (m = n) ”) &&
    (“ (Not (s = (0 : Int))) ”) &&
    emp **
    ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (n)))
    |--
    (
    TT &&
    emp **
    ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (n)))
    ) ** (
    ALL x : Int, ALL p : Int, ALL y : Int, ALL q : Int, 
(
      TT &&
      emp **
      ((&( ((s)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (m))) **
      ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (y))) **
      ((dllseg_shape p q y s))) -* (
      TT &&
      emp **
      ((dllseg_shape p q s m)))
      )

noncomputable def dll_shape_strategy14 : Prop :=
  forall (m : Int) (p : Int) (s : Int) (q : Int),
    TT &&
    (“ (Not (m = p)) ”) &&
    emp **
    ((dllseg_shape p q s m))
    |--
    EX x : Int, EX y : Int, 
      (
      TT &&
      (“ (Not (s = (0 : Int))) ”) &&
      emp **
      ((&( ((s)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (m))) **
      ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (y))) **
      ((dllseg_shape p q y s))
      ) ** (
      ALL n : Int, 
(
        TT &&
        emp **
        ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (n)))) -* (
        TT &&
        emp **
        ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (n))))
        )

noncomputable def dll_shape_strategy15 : Prop :=
  forall (q : Int) (x : Int) (t : Int) (p : Int) (r : Int) (s : Int),
    TT &&
    (“ (p = t) ”) &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg_shape p q r s))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp **
    ((dlistrep_shape s r))) -* (
    TT &&
    emp **
    ((dlistrep_shape t x)))
    )

noncomputable def dll_shape_strategy16 : Prop :=
  forall (s : Int) (q : Int) (p : Int) (m : Int),
    TT &&
    (“ (Not (s = q)) ”) &&
    emp **
    ((dllseg_shape p q s m))
    |--
    EX x : Int, EX y : Int, 
      (
      TT &&
      emp **
      ((&( ((s)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (m))) **
      ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (y))) **
      ((dllseg_shape p q y s))
      ) ** (
      ALL n : Int, 
(
        TT &&
        emp **
        ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (n)))) -* (
        TT &&
        emp **
        ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (n))))
        )

noncomputable def dll_shape_strategy8 : Prop :=
  forall (p : Int) (x : Int),
    TT &&
    emp **
    ((dlistrep_shape p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL y : Int, 
(
      TT &&
      (“ (x = y) ”) &&
      emp) -* (
      TT &&
      emp **
      ((dlistrep_shape p y)))
      )

noncomputable def dll_shape_strategy11 : Prop :=
  forall (p : Int) (s : Int) (r : Int) (q : Int),
    TT &&
    (“ (q = r) ”) &&
    (“ (p = s) ”) &&
    emp
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
    ((dllseg_shape p q r s)))
    )

noncomputable def dll_shape_strategy5 : Prop :=
  forall (p : Int) (prev : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((dlistrep_shape p prev))
    |--
    EX x : Int, EX y : Int, 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((&( ((p)) # "list" ->ₛ "prev") # PTR |-> (prev))) **
      ((dlistrep_shape y p))
      ) ** (
      ALL q : Int, 
(
        TT &&
        emp **
        ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)) || (&( ((p)) # "list" ->ₛ "prev") # PTR |-> (q)))) -* (
        TT &&
        emp **
        ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)) || (&( ((p)) # "list" ->ₛ "prev") # PTR |-> (q))))
        )

noncomputable def dll_shape_strategy6 : Prop :=
  forall (p : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp
    ) ** (
    ALL prev : Int, ALL x : Int, ALL y : Int, 
(
      TT &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((&( ((p)) # "list" ->ₛ "prev") # PTR |-> (prev))) **
      ((dlistrep_shape y p))) -* (
      TT &&
      emp **
      ((dlistrep_shape p prev)))
      )

structure dll_shape_Strategy_Correct : Type where
  dll_shape_strategy1_correctness : dll_shape_strategy1
  dll_shape_strategy2_correctness : dll_shape_strategy2
  dll_shape_strategy3_correctness : dll_shape_strategy3
  dll_shape_strategy4_correctness : dll_shape_strategy4
  dll_shape_strategy12_correctness : dll_shape_strategy12
  dll_shape_strategy7_correctness : dll_shape_strategy7
  dll_shape_strategy13_correctness : dll_shape_strategy13
  dll_shape_strategy14_correctness : dll_shape_strategy14
  dll_shape_strategy15_correctness : dll_shape_strategy15
  dll_shape_strategy16_correctness : dll_shape_strategy16
  dll_shape_strategy8_correctness : dll_shape_strategy8
  dll_shape_strategy11_correctness : dll_shape_strategy11
  dll_shape_strategy5_correctness : dll_shape_strategy5
  dll_shape_strategy6_correctness : dll_shape_strategy6

end SimpleC.EE.QCP_demos_LLM.generated.dll_shape_strategy_goal
