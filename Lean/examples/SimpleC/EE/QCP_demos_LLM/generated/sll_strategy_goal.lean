import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.sll_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance sllStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def sll_strategy3 : Prop :=
  forall (p : Int),
    TT &&
    emp **
    ((sll p (@List.nil Int)))
    |--
    (
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def sll_strategy4 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL p : Int, 
(
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp) -* (
    TT &&
    emp **
    ((sll p (@List.nil Int))))
    )

noncomputable def sll_strategy5 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp) -* (
    TT &&
    emp **
    ((sll (0 : Int) l)))
    )

noncomputable def sll_strategy6 : Prop :=
  forall (p : Int) (x0 : Int) (l0 : (List Int)),
    TT &&
    emp **
    ((sll p (@List.cons Int x0 l0)))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List Int), ALL x1 : Int, 
(
      TT &&
      (“ (x0 = x1) ”) &&
      (“ (l0 = l1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((sll p (@List.cons Int x1 l1))))
      )

noncomputable def sll_strategy21 : Prop :=
  forall (p : Int) (l : (List Int)),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((sll p l))
    |--
    EX d : Int, EX q : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons Int d l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (d))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (q))) **
      ((sll q l0))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def sll_strategy22 : Prop :=
  forall (p : Int) (l0 : (List Int)) (d : Int) (q : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (d))) **
    ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (q))) **
    ((sll q l0))
    |--
    EX l : (List Int), 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons Int d l0)) ”) &&
      emp **
      ((sll p l))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def sll_strategy14 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL p : Int, ALL l0 : (List Int), 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp **
    ((sll p l0))) -* (
    TT &&
    emp **
    ((sllseg p p l)) **
    ((sll p l0)))
    )

noncomputable def sll_strategy15 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL h : Int, ALL p : Int, 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (h)))) -* (
    TT &&
    emp **
    ((sllseg p p l)) **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (h))))
    )

noncomputable def sll_strategy16 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL q : Int, ALL p : Int, 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp **
    ((p # PTR |-> (q)))) -* (
    TT &&
    emp **
    ((sllbseg p p l)) **
    ((p # PTR |-> (q))))
    )

noncomputable def sll_strategy17 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL ty : front_end_type, ALL l : (List Int), ALL p : Int, 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp **
    ((p # ty |->_))) -* (
    TT &&
    emp **
    ((sllbseg p p l)) **
    ((p # ty |->_)))
    )

noncomputable def sll_strategy18 : Prop :=
  forall (l1 : (List Int)) (p : Int) (v1 : Int) (q : Int),
    TT &&
    emp **
    ((sllbseg p q l1)) **
    ((q # PTR |-> (v1)))
    |--
    (
    TT &&
    emp **
    ((q # PTR |-> (v1)))
    ) ** (
    ALL l2 : (List Int), ALL v2 : Int, 
(
      TT &&
      (“ (l1 = l2) ”) &&
      emp **
      ((q # PTR |-> (v2)))) -* (
      TT &&
      emp **
      ((sllbseg p q l2)) **
      ((q # PTR |-> (v2))))
      )

noncomputable def sll_strategy19 : Prop :=
  forall (ty : front_end_type) (l1 : (List Int)) (p : Int) (q : Int),
    TT &&
    emp **
    ((sllbseg p q l1)) **
    ((q # ty |->_))
    |--
    (
    TT &&
    emp **
    ((q # ty |->_))
    ) ** (
    ALL l2 : (List Int), ALL r : Int, 
(
      TT &&
      (“ (q = r) ”) &&
      (“ (l1 = l2) ”) &&
      emp **
      ((r # ty |->_))) -* (
      TT &&
      emp **
      ((sllbseg p r l2)) **
      ((r # ty |->_)))
      )

noncomputable def sll_strategy20 : Prop :=
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
    ALL l : (List Int), 
(
      TT &&
      (“ (l = (@List.nil Int)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((sll p l)))
      )

noncomputable def sll_strategy7 : Prop :=
  forall (p : Int) (l0 : (List Int)),
    TT &&
    emp **
    ((sll p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List Int), 
(
      TT &&
      (“ (l0 = l1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((sll p l1)))
      )

noncomputable def sll_strategy10 : Prop :=
  forall (p : Int) (x : Int) (l : (List Int)),
    TT &&
    emp **
    ((sll p (@List.cons Int x l)))
    |--
    EX y : Int, 
      (
      TT &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sll y l))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def sll_strategy11 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL p : Int, ALL x : Int, ALL y : Int, ALL l : (List Int), 
(
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
    ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
    ((sll y l))) -* (
    TT &&
    emp **
    ((sll p (@List.cons Int x l))))
    )

noncomputable def sll_strategy8 : Prop :=
  forall (p : Int) (l : (List Int)),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((sll p l))
    |--
    EX x : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((sll p (@List.cons Int x l0)))
      ) ** (
      ALL q : Int, 
(
        TT &&
        emp **
        ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))) -* (
        TT &&
        emp **
        ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q))))
        )

noncomputable def sll_strategy9 : Prop :=
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
    ALL l : (List Int), ALL x : Int, ALL l0 : (List Int), 
(
      TT &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((sll p (@List.cons Int x l0)))) -* (
      TT &&
      emp **
      ((sll p l)))
      )

structure sll_Strategy_Correct : Type where
  sll_strategy3_correctness : sll_strategy3
  sll_strategy4_correctness : sll_strategy4
  sll_strategy5_correctness : sll_strategy5
  sll_strategy6_correctness : sll_strategy6
  sll_strategy21_correctness : sll_strategy21
  sll_strategy22_correctness : sll_strategy22
  sll_strategy14_correctness : sll_strategy14
  sll_strategy15_correctness : sll_strategy15
  sll_strategy16_correctness : sll_strategy16
  sll_strategy17_correctness : sll_strategy17
  sll_strategy18_correctness : sll_strategy18
  sll_strategy19_correctness : sll_strategy19
  sll_strategy20_correctness : sll_strategy20
  sll_strategy7_correctness : sll_strategy7
  sll_strategy10_correctness : sll_strategy10
  sll_strategy11_correctness : sll_strategy11
  sll_strategy8_correctness : sll_strategy8
  sll_strategy9_correctness : sll_strategy9

end SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal
