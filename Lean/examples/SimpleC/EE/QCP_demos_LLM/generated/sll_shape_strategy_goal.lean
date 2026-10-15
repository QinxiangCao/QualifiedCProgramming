import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.sll_shape_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance sll_shapeStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def sll_shape_strategy3 : Prop :=
  TT &&
  emp **
  ((listrep (0 : Int)))
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

noncomputable def sll_shape_strategy4 : Prop :=
  TT &&
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
  ((listrep (0 : Int))))
  )

noncomputable def sll_shape_strategy5 : Prop :=
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
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((listrep p)))
    )

noncomputable def sll_shape_strategy14 : Prop :=
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
    emp **
    ((listrep p))) -* (
    TT &&
    emp **
    ((lseg p p)) **
    ((listrep p)))
    )

noncomputable def sll_shape_strategy15 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL q : Int, ALL p : Int, 
(
    TT &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))) -* (
    TT &&
    emp **
    ((lseg p p)) **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q))))
    )

noncomputable def sll_shape_strategy23 : Prop :=
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
    emp) -* (
    TT &&
    emp **
    ((lseg p p)))
    )

noncomputable def sll_shape_strategy25 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((lseg p q)) **
    ((listrep q))
    |--
    (
    TT &&
    emp **
    ((listrep q))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def sll_shape_strategy6 : Prop :=
  forall (p : Int),
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp **
    ((listrep p))
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

noncomputable def sll_shape_strategy10 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    emp **
    ((lseg p q))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp **
    ((listrep q))) -* (
    TT &&
    emp **
    ((listrep p)))
    )

noncomputable def sll_shape_strategy16 : Prop :=
  forall (q : Int) (p : Int) (z : Int),
    TT &&
    (“ (Not (q = (0 : Int))) ” || “ (Not ((0 : Int) = q)) ”) &&
    emp **
    ((lseg p q)) **
    ((&( ((q)) # "list" ->ₛ "next") # PTR |-> (z)))
    |--
    (
    TT &&
    (“ (Not (q = (0 : Int))) ” || “ (Not ((0 : Int) = q)) ”) &&
    emp
    ) ** (
    ALL h : Int, 
(
      TT &&
      emp **
      ((&( ((q)) # "list" ->ₛ "data") # INT |-> (h)))) -* (
      TT &&
      emp **
      ((lseg p z)))
      )

noncomputable def sll_shape_strategy21 : Prop :=
  forall (q : Int) (p : Int),
    TT &&
    (“ (q = (0 : Int)) ”) &&
    emp **
    ((listrep p))
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
    ((lseg p q)))
    )

noncomputable def sll_shape_strategy11 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))
    ) ** (
    ALL x : Int, ALL y : Int, 
(
      TT &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((listrep y))) -* (
      TT &&
      emp **
      ((listrep p)))
      )

noncomputable def sll_shape_strategy17 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))
    ) ** (
    ALL x : Int, ALL y : Int, ALL z : Int, 
(
      TT &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((lseg y z))) -* (
      TT &&
      emp **
      ((lseg p z)))
      )

noncomputable def sll_shape_strategy18 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    emp **
    ((lseg p q))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL z : Int, 
(
      TT &&
      emp **
      ((lseg q z))) -* (
      TT &&
      emp **
      ((lseg p z)))
      )

noncomputable def sll_shape_strategy19 : Prop :=
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
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp) -* (
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((lseg p p)))
    )

noncomputable def sll_shape_strategy20 : Prop :=
  forall (q : Int) (p : Int),
    TT &&
    (“ (p = (0 : Int)) ”) &&
    (“ (q = (0 : Int)) ”) &&
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
    ((lseg p q)))
    )

noncomputable def sll_shape_strategy24 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp **
    ((lseg p q))
    |--
    (
    TT &&
    (“ (q = (0 : Int)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def sll_shape_strategy7 : Prop :=
  forall (p : Int),
    TT &&
    emp **
    ((listrep p))
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
    ((listrep p)))
    )

noncomputable def sll_shape_strategy8 : Prop :=
  forall (p : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((listrep p))
    |--
    EX x : Int, EX y : Int, 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((listrep y))
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

noncomputable def sll_shape_strategy9 : Prop :=
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
    ALL x : Int, ALL y : Int, 
(
      TT &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((listrep y))) -* (
      TT &&
      emp **
      ((listrep p)))
      )

noncomputable def sll_shape_strategy22 : Prop :=
  forall (p : Int) (q : Int),
    TT &&
    (“ (Not (p = q)) ” || “ (Not (q = p)) ”) &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((lseg p q))
    |--
    EX x : Int, EX y : Int, 
      (
      TT &&
      (“ (Not (p = q)) ” || “ (Not (q = p)) ”) &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((lseg y q))
      ) ** (
      ALL v : Int, ALL n : Int, 
(
        TT &&
        emp **
        ((&( ((p)) # "list" ->ₛ "data") # INT |-> (v)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (n)))) -* (
        TT &&
        emp **
        ((&( ((p)) # "list" ->ₛ "data") # INT |-> (v)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (n))))
        )

structure sll_shape_Strategy_Correct : Type where
  sll_shape_strategy3_correctness : sll_shape_strategy3
  sll_shape_strategy4_correctness : sll_shape_strategy4
  sll_shape_strategy5_correctness : sll_shape_strategy5
  sll_shape_strategy14_correctness : sll_shape_strategy14
  sll_shape_strategy15_correctness : sll_shape_strategy15
  sll_shape_strategy23_correctness : sll_shape_strategy23
  sll_shape_strategy25_correctness : sll_shape_strategy25
  sll_shape_strategy6_correctness : sll_shape_strategy6
  sll_shape_strategy10_correctness : sll_shape_strategy10
  sll_shape_strategy16_correctness : sll_shape_strategy16
  sll_shape_strategy21_correctness : sll_shape_strategy21
  sll_shape_strategy11_correctness : sll_shape_strategy11
  sll_shape_strategy17_correctness : sll_shape_strategy17
  sll_shape_strategy18_correctness : sll_shape_strategy18
  sll_shape_strategy19_correctness : sll_shape_strategy19
  sll_shape_strategy20_correctness : sll_shape_strategy20
  sll_shape_strategy24_correctness : sll_shape_strategy24
  sll_shape_strategy7_correctness : sll_shape_strategy7
  sll_shape_strategy8_correctness : sll_shape_strategy8
  sll_shape_strategy9_correctness : sll_shape_strategy9
  sll_shape_strategy22_correctness : sll_shape_strategy22

end SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal
