import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_manual_walk
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5
  exact factor_machine_trial_init m_pre (by omega) PreH2

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5
  rfl

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_1_split_goal_1 x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5
    | exact proof_of_solver_entail_wit_1_split_goal_2 x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5
    | exact proof_of_solver_entail_wit_1_split_goal_3 x_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5


theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hdiv : remainder mod p = 0 := (p090_rem_mod remainder p (by omega) (by omega)).symm.trans PreH1
  have hs := factor_machine_enter_prime m_pre p remainder pr_values_2 pe_values_2 PreH16 PreH2 hdiv
  have hp := hs.2.2
  change p ≤ 10000000 at hp
  Exists remainder (0 : Int) pe_values_2 pr_values_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | exact hs | rfl | omega | simp only [sub_zero]

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro x_pre m_pre original_remainder_2 remainder exponent_2 pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hrem := PreH15.1.2.2.2.2.2
  have hdiv : remainder mod p = 0 := (p090_rem_mod remainder p (by omega) (by omega)).symm.trans PreH1
  have hd := coq_div_factor remainder p hdiv
  have hs := factor_machine_divide_step m_pre p original_remainder_2 remainder (remainder /ᶻ p) exponent_2 pr_values_2 pe_values_2 PreH15 hd
  have he := factor_machine_active_exponent_bounds m_pre p original_remainder_2 (remainder /ᶻ p) (exponent_2+1) pr_values_2 pe_values_2 hs
  rw [p090_quot_div remainder p (by omega) (by omega)]
  Exists original_remainder_2 (exponent_2+1)
  simp only [sub_self]
  change emp |-- “ (replace_Znth 0 (unsigned_last_nbits (exponent_2+1) 64) [exponent_2] = [exponent_2+1]) ” && “ (0 ≤ exponent_2+1) ” && “ (exponent_2+1 ≤ 47) ” && “ (FactorMachineAtPrime m_pre p original_remainder_2 (remainder /ᶻ p) (exponent_2+1) pr_values_2 pe_values_2) ” && emp
  rw [p090_uint64 (exponent_2+1) (by omega) (by omega)]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | exact hs | rfl | omega

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb := PreH15.1.2.2.2.2.2
  apply factor_machine_finish_prime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 PreH15
  · rw [← p090_rem_mod remainder p (by omega) (by omega)]
    exact PreH1
  · omega

theorem proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2 := by
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hrem := PreH15.1.2.2.2.2.2
  have horig := PreH15.1.1.1.2.2.2.1
  omega

theorem proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3 := by
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH15.1.2.2.2.2.2.1

theorem proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4 := by
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simpa only [Zlength_app,Zlength_cons,Zlength_nil,zero_add] using congrArg (fun z : Int => z+1) PreH12

theorem proof_of_solver_entail_wit_4_1_split_goal_5 : solver_entail_wit_4_1_split_goal_5 := by
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simpa only [Zlength_app,Zlength_cons,Zlength_nil,zero_add] using congrArg (fun z : Int => z+1) PreH11

theorem proof_of_solver_entail_wit_4_1_split_goal_6 : solver_entail_wit_4_1_split_goal_6 := by
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hl := strict_factor_prefix_length_lt_47 m_pre p original_remainder pr_values_2 pe_values_2 PreH15.1.1 PreH3
  omega

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_1_split_goal_1 x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_solver_entail_wit_4_1_split_goal_2 x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_solver_entail_wit_4_1_split_goal_3 x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_solver_entail_wit_4_1_split_goal_4 x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_solver_entail_wit_4_1_split_goal_5 x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_solver_entail_wit_4_1_split_goal_6 x_pre m_pre original_remainder remainder exponent pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15


theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply factor_machine_trial_skip m_pre p remainder pr_values_2 pe_values_2 PreH16 PreH2
  rw [← p090_rem_mod remainder p (by omega) (by omega)]
  exact PreH1

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_2_split_goal_1 x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1 := by
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  obtain ⟨final_pr,final_pe,Hvalid,Hcases⟩ := strict_trial_finalize_after_square_exit m_pre p remainder pr_values_2 pe_values_2 PreH16.1 PreH4 PreH2
  rcases Hcases with ⟨hone,hpr,hpe⟩ | ⟨hgt,rfl,rfl⟩
  · omega
  · exact Hvalid

theorem proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2 := by
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simpa only [Zlength_app,Zlength_cons,Zlength_nil,zero_add] using congrArg (fun z : Int => z+1) PreH13

theorem proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3 := by
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simpa only [Zlength_app,Zlength_cons,Zlength_nil,zero_add] using congrArg (fun z : Int => z+1) PreH12

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_5_1_split_goal_1 x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_solver_entail_wit_5_1_split_goal_2 x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_solver_entail_wit_5_1_split_goal_3 x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1 := by
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  obtain ⟨final_pr,final_pe,Hvalid,Hcases⟩ := strict_trial_finalize_after_square_exit m_pre p remainder pr_values_2 pe_values_2 PreH16.1 PreH4 PreH2
  rcases Hcases with ⟨hone,rfl,rfl⟩ | ⟨hgt,hpr,hpe⟩
  · exact Hvalid
  · omega

theorem proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2 := by
  unfold solver_entail_wit_5_2
  right
  intro x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_5_2_split_goal_1 x_pre m_pre remainder pe_values_2 pr_values_2 factor_count_2 p PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have h := valid_factor_table_initial_walk_budget m_pre x_pre pr_values_2 pe_values_2 PreH10
  have hb := h.2.2
  omega

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact walk_suffix_nonnegative pr_values_2 pe_values_2 x_pre 0 1

theorem proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact valid_table_initial_prefix_choice m_pre x_pre pr_values_2 pe_values_2 PreH10

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_6_split_goal_1 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_solver_entail_wit_6_split_goal_2 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_solver_entail_wit_6_split_goal_3 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10


theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  refine ⟨⟨PreH12,PreH13⟩,?_⟩
  exact valid_factor_table_walk_spec_solver_order m_pre x_pre pr_values_2 pe_values_2 PreH1 PreH5 PreH10

theorem proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  omega

theorem proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  omega

theorem proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  omega

theorem proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5 := by
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  omega

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_7_split_goal_1 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_7_split_goal_2 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_7_split_goal_3 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_7_split_goal_4 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_7_split_goal_5 x_pre m_pre factor_count_2 pr_values_2 pe_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13


theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro x_pre m_pre factor_count_2 accumulator_2 pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have hb := PreH12.1
  rw [p090_uint64 (accumulator_2+1) (by omega) (by omega)]
  exact cycle_answer_to_spec m_pre x_pre accumulator_2 PreH12

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  intro x_pre m_pre factor_count_2 accumulator_2 pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  sep_apply (naive_C_Rules.UInt64Array.seg_to_seg_shape (&("pr")) 0 factor_count_2 pr_values)
  sep_apply (naive_C_Rules.UInt64Array.seg_to_seg_shape (&("pe")) 0 factor_count_2 pe_values)
  cancel

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro x_pre m_pre factor_count_2 accumulator_2 pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · exact proof_of_solver_return_wit_1_split_goal_spatial x_pre m_pre factor_count_2 accumulator_2 pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_solver_return_wit_1_split_goal_1 x_pre m_pre factor_count_2 accumulator_2 pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_partial_solve_wit_7_pure_split_goal_1 : solver_partial_solve_wit_7_pure_split_goal_1 := by
  intro x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  exact ⟨⟨PreH11,PreH12⟩,⟨PreH13,PreH14⟩,PreH15⟩

theorem proof_of_solver_partial_solve_wit_7_pure_split_goal_2 : solver_partial_solve_wit_7_pure_split_goal_2 := by
  intro x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  unfold WalkMachineBounds
  omega

theorem proof_of_solver_partial_solve_wit_7_pure_split_goal_3 : solver_partial_solve_wit_7_pure_split_goal_3 := by
  intro x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  unfold WalkBudget
  omega

theorem proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure := by
  unfold solver_partial_solve_wit_7_pure
  right
  intro x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures <;> first
  | exact proof_of_solver_partial_solve_wit_7_pure_split_goal_1 x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  | exact proof_of_solver_partial_solve_wit_7_pure_split_goal_2 x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  | exact proof_of_solver_partial_solve_wit_7_pure_split_goal_3 x_pre m_pre factor_count remainder pr_values pe_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23


end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
