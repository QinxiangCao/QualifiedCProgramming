import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.bst_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

open SimpleC.EE.QCP_demos_LLM.Bst

local instance bstStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def bst_strategy0 : Prop :=
  forall (p : Int) (tr0 : tree),
    TT &&
    emp **
    ((store_tree p tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL tr1 : tree, 
(
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((store_tree p tr1)))
      )

noncomputable def bst_strategy1 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL pt : partial_tree, ALL q : Int, ALL p : Int, 
(
    TT &&
    (“ (pt = (empty_partial_tree)) ”) &&
    emp **
    ((p # PTR |-> (q)))) -* (
    TT &&
    emp **
    ((store_ptb p p pt)) **
    ((p # PTR |-> (q))))
    )

noncomputable def bst_strategy2 : Prop :=
  forall (p : Int) (tr0 : partial_tree) (rt : Int),
    TT &&
    emp **
    ((store_ptb p rt tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL tr1 : partial_tree, 
(
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((store_ptb p rt tr1)))
      )

noncomputable def bst_strategy4 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL pt : partial_tree, ALL q : Int, ALL p : Int, 
(
    TT &&
    (“ (pt = (empty_partial_tree)) ”) &&
    emp **
    ((p # PTR |-> (q)))) -* (
    TT &&
    emp **
    ((store_pt p p pt)) **
    ((p # PTR |-> (q))))
    )

noncomputable def bst_strategy5 : Prop :=
  forall (p : Int) (tr0 : partial_tree) (rt : Int),
    TT &&
    emp **
    ((store_pt p rt tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL tr1 : partial_tree, 
(
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((store_pt p rt tr1)))
      )

structure bst_Strategy_Correct : Type where
  bst_strategy0_correctness : bst_strategy0
  bst_strategy1_correctness : bst_strategy1
  bst_strategy2_correctness : bst_strategy2
  bst_strategy4_correctness : bst_strategy4
  bst_strategy5_correctness : bst_strategy5

end SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal
