import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_goal
import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open modular_power_lib

-- Remainders are below 100000, so the C cast to signed int is exact.
private theorem cast_rem (x m : Int) (hx : 0 ≤ x) (hm : 0 < m) (hb : m ≤ 100000) :
    signed_last_nbits (Z.rem x m) 32 = Z.rem x m := by
  have h := rem_nonneg_bounds x m hx hm
  apply signed_last_nbits_eq _ 32 (by decide)
  change -2147483648 ≤ _ ∧ _ < 2147483648
  omega

theorem proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1 := by
  pre_process
  entailer!
  simp [ModularPowerProgress]

theorem proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1 := by
  pre_process
  have ha := rem_nonneg_bounds (a*a) modulus_pre (Int.mul_nonneg PreH5 PreH5) (by omega)
  have hr := rem_nonneg_bounds (result*a) modulus_pre (Int.mul_nonneg PreH8 PreH5) (by omega)
  have hq := Z.quot_pos b 2 (by omega) (by decide)
  have hs := cast_rem (a*a) modulus_pre (Int.mul_nonneg PreH5 PreH5) (by omega) PreH4
  have ht := cast_rem (result*a) modulus_pre (Int.mul_nonneg PreH8 PreH5) (by omega) PreH4
  have hp : ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a*a) modulus_pre)
      (Z.quot b 2) (Z.rem (result*a) modulus_pre) := by
    simp only [rem_eq_mod b 2 (by omega) (by decide), rem_eq_mod (a*a) modulus_pre (by positivity) (by omega), rem_eq_mod (result*a) modulus_pre (by positivity) (by omega), zdiv_equiv b 2 (by omega) (by decide)] at *
    apply modular_power_progress_odd_step__loop_transitions <;> first | assumption | omega
  entailer!
  all_goals simp only [hs, ht] at *
  all_goals first | assumption | omega

theorem proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2 := by
  pre_process
  have ha := rem_nonneg_bounds (a*a) modulus_pre (Int.mul_nonneg PreH5 PreH5) (by omega)
  have hq := Z.quot_pos b 2 (by omega) (by decide)
  have hs := cast_rem (a*a) modulus_pre (Int.mul_nonneg PreH5 PreH5) (by omega) PreH4
  have hpar := rem_nonneg_bounds b 2 (by omega) (by decide)
  have heven : Z.rem b 2 = 0 := by omega
  have hp : ModularPowerProgress a_pre b_pre modulus_pre (Z.rem (a*a) modulus_pre) (Z.quot b 2) result := by
    simp only [rem_eq_mod b 2 (by omega) (by decide), rem_eq_mod (a*a) modulus_pre (by positivity) (by omega), zdiv_equiv b 2 (by omega) (by decide)] at *
    apply modular_power_progress_even_step__loop_transitions <;> first | assumption | omega
  entailer!
  all_goals simp only [hs] at *
  all_goals first | assumption | omega

theorem proof_of_modular_power_return_wit_1 : modular_power_return_wit_1 := by
  pre_process
  have hb : b = 0 := by omega
  subst b
  entailer!
  unfold ModularPowerProgress at PreH9
  unfold ModularPower
  simpa only [Z.pow, Int.pow_zero, Int.mul_one, Z.modulo, Int.fmod_eq_of_lt (show 0 ≤ result by omega) (show result < modulus_pre by omega)] using PreH9

end SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_proof_manual
