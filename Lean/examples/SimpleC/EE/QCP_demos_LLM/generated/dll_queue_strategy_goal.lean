import SimpleC.SL.SeparationLogic
import SimpleC.EE.QCP_demos_LLM.dll_queue_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.dll_queue_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance dll_queueStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }


noncomputable def dll_queue_strategy0 : Prop :=
  forall (p : Int) (l0 : (List Int)),
    TT &&
    emp **
    ((store_queue p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List Int), 
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_queue p l1))
      )

noncomputable def dll_queue_strategy1 : Prop :=
  forall (p : Int) (q : Int) (l0 : (List Int)) (r : Int),
    TT &&
    emp **
    ((dllseg p (0 : Int) q r l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL l1 : (List Int), 
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg p (0 : Int) q r l1))
      )

structure dll_queue_Strategy_Correct : Type where
  dll_queue_strategy0_correctness : dll_queue_strategy0
  dll_queue_strategy1_correctness : dll_queue_strategy1

end SimpleC.EE.QCP_demos_LLM.generated.dll_queue_strategy_goal
