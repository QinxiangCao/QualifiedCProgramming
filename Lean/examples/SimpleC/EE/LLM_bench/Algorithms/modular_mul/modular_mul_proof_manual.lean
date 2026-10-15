import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_goal
import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open modular_mul_lib

theorem proof_of_modular_mul_entail_wit_1_1 : modular_mul_entail_wit_1_1 := by
  pre_process
  have hp : ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) 0 (-1) := by
    refine ⟨0, ?_⟩
    grind
  entailer!

theorem proof_of_modular_mul_entail_wit_1_2 : modular_mul_entail_wit_1_2 := by
  pre_process
  have hp : ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre 0 1 := by
    refine ⟨0, ?_⟩
    grind
  entailer!

theorem proof_of_modular_mul_entail_wit_2_1 : modular_mul_entail_wit_2_1 := by
  pre_process
  have ha := rem_bounds (a+a) modulus_pre (by omega)
  have hr := rem_bounds (res+a) modulus_pre (by omega)
  have hq0 := Z.quot_pos b 2 (by omega) (by decide)
  have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
  have hp : ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a+a) modulus_pre)
      (Z.quot b 2) (Z.rem (res+a) modulus_pre) flag := by
    rw [zdiv_equiv b 2 (by omega) (by decide)]
    apply modular_mul_progress_odd_step__odd_transition
    · simpa only [rem_eq_mod b 2 (by omega) (by decide)] using PreH1
    · omega
    · exact PreH12
  entailer!

theorem proof_of_modular_mul_entail_wit_2_2 : modular_mul_entail_wit_2_2 := by
  pre_process
  have ha := rem_bounds (a+a) modulus_pre (by omega)
  have hr := rem_bounds (res+a) modulus_pre (by omega)
  have hq0 := Z.quot_pos b 2 (by omega) (by decide)
  have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
  have hp : ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a+a) modulus_pre)
      (Z.quot b 2) (Z.rem (res+a) modulus_pre) flag := by
    rw [zdiv_equiv b 2 (by omega) (by decide)]
    apply modular_mul_progress_odd_step__odd_transition
    · simpa only [rem_eq_mod b 2 (by omega) (by decide)] using PreH1
    · omega
    · exact PreH12
  entailer!

theorem proof_of_modular_mul_entail_wit_2_3 : modular_mul_entail_wit_2_3 := by
  pre_process
  have ha := rem_bounds (a+a) modulus_pre (by omega)
  have hr := rem_bounds (res+a) modulus_pre (by omega)
  have hq0 := Z.quot_pos b 2 (by omega) (by decide)
  have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
  have hb := rem_nonneg_bounds b 2 (by omega) (by decide)
  have heven : Z.rem b 2 = 0 := by omega
  have hp : ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a+a) modulus_pre)
      (Z.quot b 2) res flag := by
    apply modular_mul_progress_even_step__even_transition <;> first | assumption | omega
  entailer!

theorem proof_of_modular_mul_entail_wit_2_4 : modular_mul_entail_wit_2_4 := by
  pre_process
  have ha := rem_bounds (a+a) modulus_pre (by omega)
  have hr := rem_bounds (res+a) modulus_pre (by omega)
  have hq0 := Z.quot_pos b 2 (by omega) (by decide)
  have hq1 := Z.quot_le_upper_bound b 2 b (by decide) (by omega)
  have hb := rem_nonneg_bounds b 2 (by omega) (by decide)
  have heven : Z.rem b 2 = 0 := by omega
  have hp : ModularMulProgress a_pre b_pre modulus_pre (Z.rem (a+a) modulus_pre)
      (Z.quot b 2) res flag := by
    apply modular_mul_progress_even_step__even_transition <;> first | assumption | omega
  entailer!

theorem proof_of_modular_mul_return_wit_1 : modular_mul_return_wit_1 := by
  pre_process
  have hp := modular_mul_progress_finish__final_result a_pre b_pre modulus_pre a b res flag
    (by omega) (by right; omega) (by omega) PreH11
  entailer!

theorem proof_of_modular_mul_return_wit_2 : modular_mul_return_wit_2 := by
  pre_process
  have hp := modular_mul_progress_finish__final_result a_pre b_pre modulus_pre a b res flag
    (by omega) (by left; omega) (by omega) PreH11
  entailer!

end SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_proof_manual
