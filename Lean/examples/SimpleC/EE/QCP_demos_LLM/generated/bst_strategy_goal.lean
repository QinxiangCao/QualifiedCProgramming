import SimpleC.SL.SeparationLogic
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
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_tree p tr1))
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
    TT &&
    (“ (pt = (empty_partial_tree)) ”) &&
    emp **
    ((p # PTR |-> (q))) -*
    TT &&
    emp **
    ((store_ptb p p pt)) **
    ((p # PTR |-> (q)))
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
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_ptb p rt tr1))
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
    TT &&
    (“ (pt = (empty_partial_tree)) ”) &&
    emp **
    ((p # PTR |-> (q))) -*
    TT &&
    emp **
    ((store_pt p p pt)) **
    ((p # PTR |-> (q)))
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
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_pt p rt tr1))
      )

structure bst_Strategy_Correct : Type where
  bst_strategy0_correctness : bst_strategy0
  bst_strategy1_correctness : bst_strategy1
  bst_strategy2_correctness : bst_strategy2
  bst_strategy4_correctness : bst_strategy4
  bst_strategy5_correctness : bst_strategy5

end SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal
