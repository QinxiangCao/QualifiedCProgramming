import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.poly_sll_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance poly_sllStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def poly_sll_strategy1 : Prop :=
  forall (A : Type) (storeA : (Int -> (A -> Assertion))) (l : (List A)) (x : Int),
    TT &&
    emp **
    ((sll storeA x l))
    |--
    (
    TT &&
    (“ (sll_para storeA) ”) &&
    emp **
    ((sll storeA x l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def poly_sll_strategy2 : Prop :=
  forall (A : Type) (storeA : (Int -> (A -> Assertion))) (y : Int) (l : (List A)) (x : Int),
    TT &&
    emp **
    ((sllseg storeA x y l))
    |--
    (
    TT &&
    (“ (sll_para storeA) ”) &&
    emp **
    ((sllseg storeA x y l))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def poly_sll_strategy4 : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))),
    TT &&
    emp **
    ((sll storeA (0 : Int) l))
    |--
    (
    TT &&
    (“ (l = (@List.nil A)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def poly_sll_strategy5 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL A : Type, ALL l : (List A), ALL storeA : (Int -> (A -> Assertion)), 
(
    TT &&
    (“ (l = (@List.nil A)) ”) &&
    emp) -* (
    TT &&
    emp **
    ((sll storeA (0 : Int) l)))
    )

noncomputable def poly_sll_strategy16 : Prop :=
  forall (A : Type) (p : Int) (x : A) (storeA : (Int -> (A -> Assertion))),
    TT &&
    emp **
    ((storeA p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL y : A, 
(
      TT &&
      (“ (x = y) ”) &&
      emp) -* (
      TT &&
      emp **
      ((storeA p y)))
      )

noncomputable def poly_sll_strategy17 : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (l0 : (List A)) (p : Int),
    TT &&
    emp **
    ((sllseg storeA p p l)) **
    ((sll storeA p l0))
    |--
    (
    TT &&
    (“ (l = (@List.nil A)) ”) &&
    emp **
    ((sll storeA p l0))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def poly_sll_strategy18 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL A : Type, ALL l : (List A), ALL storeA : (Int -> (A -> Assertion)), ALL l0 : (List A), ALL p : Int, 
(
    TT &&
    (“ (l = (@List.nil A)) ”) &&
    emp **
    ((sll storeA p l0))) -* (
    TT &&
    emp **
    ((sllseg storeA p p l)) **
    ((sll storeA p l0)))
    )

noncomputable def poly_sll_strategy19 : Prop :=
  forall (A : Type) (storeA : (Int -> (A -> Assertion))),
    TT &&
    (“ (sll_para storeA) ”) &&
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
    emp)
    )

noncomputable def poly_sll_strategy7 : Prop :=
  forall (A : Type) (storeA : (Int -> (A -> Assertion))) (l0 : (List A)) (p : Int),
    TT &&
    emp **
    ((sll storeA p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List A), 
(
      TT &&
      (“ (l0 = l1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((sll storeA p l1)))
      )

noncomputable def poly_sll_strategy10 : Prop :=
  forall (A : Type) (storeA : (Int -> (A -> Assertion))) (l : (List A)) (x : A) (p : Int),
    TT &&
    emp **
    ((sll storeA p (@List.cons A x l)))
    |--
    EX y : Int, EX h : Int, 
      (
      TT &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # PTR |-> (h))) **
      ((storeA h x)) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sll storeA y l))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def poly_sll_strategy11 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL A : Type, ALL p : Int, ALL h : Int, ALL x : A, ALL storeA : (Int -> (A -> Assertion)), ALL l : (List A), ALL y : Int, 
(
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # PTR |-> (h))) **
    ((storeA h x)) **
    ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
    ((sll storeA y l))) -* (
    TT &&
    emp **
    ((sll storeA p (@List.cons A x l))))
    )

noncomputable def poly_sll_strategy12 : Prop :=
  forall (A : Type) (storeA : (Int -> (A -> Assertion))) (q : Int) (l0 : (List A)) (p : Int),
    TT &&
    emp **
    ((sllseg storeA p q l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List A), ALL l2 : (List A), 
(
      TT &&
      (“ (l1 = (@List.append A l0 l2)) ”) &&
      emp **
      ((sll storeA q l2))) -* (
      TT &&
      emp **
      ((sll storeA p l1)))
      )

noncomputable def poly_sll_strategy8 : Prop :=
  forall (A : Type) (p : Int) (l : (List A)) (storeA : (Int -> (A -> Assertion))),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((sll storeA p l))
    |--
    EX x : A, EX l0 : (List A), 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons A x l0)) ”) &&
      emp **
      ((sll storeA p (@List.cons A x l0)))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def poly_sll_strategy9 : Prop :=
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
    ALL A : Type, ALL l : (List A), ALL x : A, ALL l0 : (List A), ALL storeA : (Int -> (A -> Assertion)), 
(
      TT &&
      (“ (l = (@List.cons A x l0)) ”) &&
      emp **
      ((sll storeA p (@List.cons A x l0)))) -* (
      TT &&
      emp **
      ((sll storeA p l)))
      )

structure poly_sll_Strategy_Correct : Type where
  poly_sll_strategy1_correctness : poly_sll_strategy1
  poly_sll_strategy2_correctness : poly_sll_strategy2
  poly_sll_strategy4_correctness : poly_sll_strategy4
  poly_sll_strategy5_correctness : poly_sll_strategy5
  poly_sll_strategy16_correctness : poly_sll_strategy16
  poly_sll_strategy17_correctness : poly_sll_strategy17
  poly_sll_strategy18_correctness : poly_sll_strategy18
  poly_sll_strategy19_correctness : poly_sll_strategy19
  poly_sll_strategy7_correctness : poly_sll_strategy7
  poly_sll_strategy10_correctness : poly_sll_strategy10
  poly_sll_strategy11_correctness : poly_sll_strategy11
  poly_sll_strategy12_correctness : poly_sll_strategy12
  poly_sll_strategy8_correctness : poly_sll_strategy8
  poly_sll_strategy9_correctness : poly_sll_strategy9

end SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal
