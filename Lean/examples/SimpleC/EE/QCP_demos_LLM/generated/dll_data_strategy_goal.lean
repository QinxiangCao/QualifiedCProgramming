import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.dll_queue_lib
import SimpleC.EE.QCP_demos_LLM.dll_shape_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance dll_dataStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def dll_data_strategy1 : Prop :=
  forall (l : (List Int)) (prev : Int),
    TT &&
    emp **
    ((dlistrep (0 : Int) prev l))
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

noncomputable def dll_data_strategy2 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : (List Int), ALL prev : Int, 
(
    TT &&
    (“ (l = (@List.nil Int)) ”) &&
    emp) -* (
    TT &&
    emp **
    ((dlistrep (0 : Int) prev l)))
    )

noncomputable def dll_data_strategy3 : Prop :=
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
    ALL l : (List Int), ALL prev : Int, 
(
      TT &&
      (“ (l = (@List.nil Int)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((dlistrep p prev l)))
      )

noncomputable def dll_data_strategy4 : Prop :=
  forall (p : Int) (l : (List Int)) (prev : Int),
    TT &&
    (“ (p = (0 : Int)) ” || “ ((0 : Int) = p) ”) &&
    emp **
    ((dlistrep p prev l))
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

noncomputable def dll_data_strategy12 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l1 : (List Int), ALL r : Int, ALL q : Int, ALL x : Int, ALL p : Int, ALL l2 : (List Int), 
(
    TT &&
    (“ (q = r) ”) &&
    (“ (x = q) ”) &&
    (“ (l1 = (@List.nil Int)) ”) &&
    emp **
    ((dlistrep p x l2))) -* (
    TT &&
    emp **
    ((dllseg p p q r l1)) **
    ((dlistrep p x l2)))
    )

noncomputable def dll_data_strategy7 : Prop :=
  forall (q : Int) (x : Int) (p : Int) (l1 : (List Int)) (r : Int) (s : Int),
    TT &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg p s q r l1))
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
      ((dlistrep s r l3))) -* (
      TT &&
      emp **
      ((dlistrep p x l2)))
      )

noncomputable def dll_data_strategy13 : Prop :=
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
    ALL l : (List Int), ALL l0 : (List Int), ALL x : Int, ALL p : Int, ALL q : Int, ALL y : Int, 
(
      TT &&
      (“ (l = (@List.append Int l0 (@List.cons Int x (@List.nil Int)))) ”) &&
      emp **
      ((&( ((s)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (m))) **
      ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (y))) **
      ((dllseg p s q y l0))) -* (
      TT &&
      emp **
      ((dllseg p m q s l)))
      )

noncomputable def dll_data_strategy14 : Prop :=
  forall (m : Int) (p : Int) (l : (List Int)) (s : Int) (q : Int),
    TT &&
    (“ (Not (m = p)) ”) &&
    emp **
    ((dllseg p m q s l))
    |--
    EX x : Int, EX y : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (l = (@List.append Int l0 (@List.cons Int x (@List.nil Int)))) ”) &&
      (“ (Not (s = (0 : Int))) ”) &&
      emp **
      ((&( ((s)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (m))) **
      ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (y))) **
      ((dllseg p s q y l0))
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

noncomputable def dll_data_strategy15 : Prop :=
  forall (q : Int) (x : Int) (t : Int) (p : Int) (l1 : (List Int)) (r : Int) (s : Int),
    TT &&
    (“ (p = t) ”) &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg p s q r l1))
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
      ((dlistrep s r l3))) -* (
      TT &&
      emp **
      ((dlistrep t x l2)))
      )

noncomputable def dll_data_strategy16 : Prop :=
  forall (s : Int) (q : Int) (l : (List Int)) (p : Int) (m : Int),
    TT &&
    (“ (Not (s = q)) ”) &&
    emp **
    ((dllseg p m q s l))
    |--
    EX x : Int, EX y : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (l = (@List.append Int l0 (@List.cons Int x (@List.nil Int)))) ”) &&
      emp **
      ((&( ((s)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((s)) # "list" ->ₛ "next") # PTR |-> (m))) **
      ((&( ((s)) # "list" ->ₛ "prev") # PTR |-> (y))) **
      ((dllseg p s q y l0))
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

noncomputable def dll_data_strategy8 : Prop :=
  forall (p : Int) (l1 : (List Int)) (x : Int),
    TT &&
    emp **
    ((dlistrep p x l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l2 : (List Int), ALL y : Int, 
(
      TT &&
      (“ (x = y) ”) &&
      (“ (l1 = l2) ”) &&
      emp) -* (
      TT &&
      emp **
      ((dlistrep p y l2)))
      )

noncomputable def dll_data_strategy11 : Prop :=
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
    ALL l : (List Int), 
(
      TT &&
      (“ (l = (@List.nil Int)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((dllseg p s q r l)))
      )

noncomputable def dll_data_strategy5 : Prop :=
  forall (p : Int) (l : (List Int)) (prev : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
    emp **
    ((dlistrep p prev l))
    |--
    EX x : Int, EX y : Int, EX l0 : (List Int), 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ” || “ (Not ((0 : Int) = p)) ”) &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((&( ((p)) # "list" ->ₛ "prev") # PTR |-> (prev))) **
      ((dlistrep y p l0))
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

noncomputable def dll_data_strategy6 : Prop :=
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
    ALL l : (List Int), ALL x : Int, ALL l0 : (List Int), ALL prev : Int, ALL y : Int, 
(
      TT &&
      (“ (l = (@List.cons Int x l0)) ”) &&
      emp **
      ((&( ((p)) # "list" ->ₛ "data") # INT |-> (x))) **
      ((&( ((p)) # "list" ->ₛ "next") # PTR |-> (y))) **
      ((&( ((p)) # "list" ->ₛ "prev") # PTR |-> (prev))) **
      ((dlistrep y p l0))) -* (
      TT &&
      emp **
      ((dlistrep p prev l)))
      )

structure dll_data_Strategy_Correct : Type where
  dll_data_strategy1_correctness : dll_data_strategy1
  dll_data_strategy2_correctness : dll_data_strategy2
  dll_data_strategy3_correctness : dll_data_strategy3
  dll_data_strategy4_correctness : dll_data_strategy4
  dll_data_strategy12_correctness : dll_data_strategy12
  dll_data_strategy7_correctness : dll_data_strategy7
  dll_data_strategy13_correctness : dll_data_strategy13
  dll_data_strategy14_correctness : dll_data_strategy14
  dll_data_strategy15_correctness : dll_data_strategy15
  dll_data_strategy16_correctness : dll_data_strategy16
  dll_data_strategy8_correctness : dll_data_strategy8
  dll_data_strategy11_correctness : dll_data_strategy11
  dll_data_strategy5_correctness : dll_data_strategy5
  dll_data_strategy6_correctness : dll_data_strategy6

end SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal
