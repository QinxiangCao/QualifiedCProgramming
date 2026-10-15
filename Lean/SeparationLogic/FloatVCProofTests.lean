import FloatVCGoalTests

namespace FloatVCProofTests

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.SeparationLogic
open FloatVCGoalTests
open scoped SimpleC.SL.SAC

local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_float_swap_entail_wit_1 : float_swap_entail_wit_1 := by
  pre_process
  cases para_all with
  | float_swap_eq_para x =>
      simp only [float_swap_pre]
      entailer!
      Right
      Exists x
      entailer!
  | float_swap_neq_para x y =>
      simp only [float_swap_pre]
      entailer!
      Left
      Exists y x
      entailer!

theorem proof_of_float_swap_return_wit_1 : float_swap_return_wit_1 := by
  pre_process
  subst_vars
  simp only [float_swap_post]
  entailer!

theorem proof_of_float_swap_return_wit_2 : float_swap_return_wit_2 := by
  pre_process
  subst_vars
  simp only [float_swap_post]
  entailer!

theorem proof_of_double_swap_entail_wit_1 : double_swap_entail_wit_1 := by
  pre_process
  cases para_all with
  | double_swap_eq_para x =>
      simp only [double_swap_pre]
      entailer!
      Right
      Exists x
      entailer!
  | double_swap_neq_para x y =>
      simp only [double_swap_pre]
      entailer!
      Left
      Exists y x
      entailer!

theorem proof_of_double_swap_return_wit_1 : double_swap_return_wit_1 := by
  pre_process
  subst_vars
  simp only [double_swap_post]
  entailer!

theorem proof_of_double_swap_return_wit_2 : double_swap_return_wit_2 := by
  pre_process
  subst_vars
  simp only [double_swap_post]
  entailer!

theorem proof_of_float_add_wit : float_add_wit := by
  pre_process
  Exists (fp32_add x y)
  entailer!

theorem proof_of_float_sub_wit : float_sub_wit := by
  pre_process
  Exists (fp32_sub x y)
  entailer!

theorem proof_of_double_add_wit : double_add_wit := by
  pre_process
  Exists (fp64_add x y)
  entailer!

theorem proof_of_double_sub_wit : double_sub_wit := by
  pre_process
  Exists (fp64_sub x y)
  entailer!

#print axioms proof_of_float_swap_entail_wit_1
#print axioms proof_of_float_add_wit
#print axioms proof_of_double_sub_wit

end FloatVCProofTests
