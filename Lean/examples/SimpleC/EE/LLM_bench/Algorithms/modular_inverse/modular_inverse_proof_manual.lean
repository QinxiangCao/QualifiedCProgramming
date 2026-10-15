import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_goal
import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1 := by
  pre_process
  have hr := rem_bounds x_callee_v modulus_pre (by omega)
  have hq := Z.quot_rem x_callee_v modulus_pre (by omega)
  entailer!
  all_goals first | (unfold ModularInverse; refine ⟨a_pre * Z.quot x_callee_v modulus_pre + y_callee_v - a_pre, ?_⟩; grind) | grind

theorem proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2 := by
  pre_process
  have hr := rem_bounds x_callee_v modulus_pre (by omega)
  have hq := Z.quot_rem x_callee_v modulus_pre (by omega)
  entailer!
  all_goals first | (unfold ModularInverse; refine ⟨a_pre * Z.quot x_callee_v modulus_pre + y_callee_v, ?_⟩; grind) | grind

end SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_proof_manual
