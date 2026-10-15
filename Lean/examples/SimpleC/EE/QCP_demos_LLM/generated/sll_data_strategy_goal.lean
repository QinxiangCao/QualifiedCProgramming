import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.sll_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance sll_dataStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def sll_data_strategy3 : Prop :=
  forall (l : (List Int)),
    TT &&
    emp **
    ((sll (0 : Int) l))
    |--
    (
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def sll_data_strategy4 : Prop :=
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

noncomputable def sll_data_strategy5 : Prop :=
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

noncomputable def sll_data_strategy14 : Prop :=
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

noncomputable def sll_data_strategy15 : Prop :=
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
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q)))) -* (
    TT &&
    emp **
    ((sllseg p p l)) **
    ((&( ((p)) # "list" ->ₛ "data") # INT |-> (q)) || (&( ((p)) # "list" ->ₛ "next") # PTR |-> (q))))
    )

noncomputable def sll_data_strategy25 : Prop :=
  forall (p : Int) (q : Int) (l2 : (List Int)) (l1 : (List Int)),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((sllseg p q l1)) **
    ((sll q l2))
    |--
    EX l3 : (List Int), 
      (
      TT &&
      (“ (l3 = (@List.append Int l1 l2)) ”) &&
      emp **
      ((sll q l3))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def sll_data_strategy23 : Prop :=
  TT &&
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
    ((sllseg p p l)))
    )

noncomputable def sll_data_strategy6 : Prop :=
  forall (p : Int) (l : (List Int)),
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp **
    ((sll p l))
    |--
    (
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    (“ (l = (@List.nil Int)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def sll_data_strategy10 : Prop :=
  forall (p : Int) (l1 : (List Int)) (q : Int),
    TT &&
    emp **
    ((sllseg p q l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l2 : (List Int), ALL l3 : (List Int), 
(
      TT &&
      (“ (l2 = (@List.append Int l1 l3)) ”) &&
      emp **
      ((sll q l3))) -* (
      TT &&
      emp **
      ((sll p l2)))
      )

noncomputable def sll_data_strategy16 : Prop :=
  forall (q : Int) (l1 : (List Int)) (p : Int) (z : Int),
    TT &&
    (“ (Not (q = (0 : Int))) ” || “ (Not ((0 : Int) = q)) ”) &&
    emp **
    ((sllseg p q l1)) **
    ((&( ((q)) # "list" ->ₛ "next") # PTR |-> (z)))
    |--
    (
    TT &&
    (“ (Not (q = (0 : Int))) ” || “ (Not ((0 : Int) = q)) ”) &&
    emp
    ) ** (
    ALL l2 : (List Int), ALL h : Int, 
(
      TT &&
      (“ (l2 = (@List.append Int l1 (@List.cons Int h (@List.nil Int)))) ”) &&
      emp **
      ((&( ((q)) # "list" ->ₛ "data") # INT |-> (h)))) -* (
      TT &&
      emp **
      ((sllseg p z l2)))
      )

noncomputable def sll_data_strategy21 : Prop :=
  forall (q : Int) (p : Int) (l1 : (List Int)),
    TT &&
    (“ (q = (0 : Int)) ”) &&
    emp **
    ((sll p l1))
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
      ((sllseg p q l2)))
      )

noncomputable def sll_data_strategy11 : Prop :=
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
    ALL l : (List Int), ALL x : Int, ALL l0 : (List Int), ALL y : Int, 
(
      TT &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sll y l0))) -* (
      TT &&
      emp **
      ((sll p l)))
      )

noncomputable def sll_data_strategy17 : Prop :=
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
    ALL l : (List Int), ALL x : Int, ALL l0 : (List Int), ALL y : Int, ALL z : Int, 
(
      TT &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sllseg y z l0))) -* (
      TT &&
      emp **
      ((sllseg p z l)))
      )

noncomputable def sll_data_strategy18 : Prop :=
  forall (p : Int) (l1 : (List Int)) (q : Int),
    TT &&
    emp **
    ((sllseg p q l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l2 : (List Int), ALL l3 : (List Int), ALL z : Int, 
(
      TT &&
      (“ (l2 = (@List.append Int l1 l3)) ”) &&
      emp **
      ((sllseg q z l3))) -* (
      TT &&
      emp **
      ((sllseg p z l2)))
      )

noncomputable def sll_data_strategy19 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL p : Int, 
(
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    (“ (l = (@List.nil Int)) ”) &&
    emp) -* (
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((sllseg p p l)))
    )

noncomputable def sll_data_strategy20 : Prop :=
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
    ALL l : (List Int), 
(
      TT &&
      (“ (l = (@List.nil Int)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((sllseg p q l)))
      )

noncomputable def sll_data_strategy24 : Prop :=
  forall (p : Int) (q : Int) (l : (List Int)),
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp **
    ((sllseg p q l))
    |--
    (
    TT &&
    (“ (q = (0 : Int)) ”) &&
    (“ (l = (@List.nil Int)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def sll_data_strategy7 : Prop :=
  forall (p : Int) (l1 : (List Int)),
    TT &&
    emp **
    ((sll p l1))
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
      ((sll p l2)))
      )

noncomputable def sll_data_strategy8 : Prop :=
  forall (p : Int) (l : (List Int)),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((sll p l))
    |--
    EX x : Int, EX y : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sll y l0))
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

noncomputable def sll_data_strategy9 : Prop :=
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
    ALL l : (List Int), ALL x : Int, ALL l0 : (List Int), ALL y : Int, 
(
      TT &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sll y l0))) -* (
      TT &&
      emp **
      ((sll p l)))
      )

noncomputable def sll_data_strategy22 : Prop :=
  forall (p : Int) (l : (List Int)) (q : Int),
    TT &&
    (“ (Not (p = q)) ” || “ (Not (q = p)) ”) &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((sllseg p q l))
    |--
    EX x : Int, EX y : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (Not (p = q)) ” || “ (Not (q = p)) ”) &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((sllseg y q l0))
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

structure sll_data_Strategy_Correct : Type where
  sll_data_strategy3_correctness : sll_data_strategy3
  sll_data_strategy4_correctness : sll_data_strategy4
  sll_data_strategy5_correctness : sll_data_strategy5
  sll_data_strategy14_correctness : sll_data_strategy14
  sll_data_strategy15_correctness : sll_data_strategy15
  sll_data_strategy25_correctness : sll_data_strategy25
  sll_data_strategy23_correctness : sll_data_strategy23
  sll_data_strategy6_correctness : sll_data_strategy6
  sll_data_strategy10_correctness : sll_data_strategy10
  sll_data_strategy16_correctness : sll_data_strategy16
  sll_data_strategy21_correctness : sll_data_strategy21
  sll_data_strategy11_correctness : sll_data_strategy11
  sll_data_strategy17_correctness : sll_data_strategy17
  sll_data_strategy18_correctness : sll_data_strategy18
  sll_data_strategy19_correctness : sll_data_strategy19
  sll_data_strategy20_correctness : sll_data_strategy20
  sll_data_strategy24_correctness : sll_data_strategy24
  sll_data_strategy7_correctness : sll_data_strategy7
  sll_data_strategy8_correctness : sll_data_strategy8
  sll_data_strategy9_correctness : sll_data_strategy9
  sll_data_strategy22_correctness : sll_data_strategy22

end SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal
