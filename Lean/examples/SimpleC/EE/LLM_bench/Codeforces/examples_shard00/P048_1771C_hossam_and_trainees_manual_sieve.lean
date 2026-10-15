import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_manual_safety

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
open AUXLib MaxMinLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre a PreH1 PreH2 PreH3 PreH4
  refine ⟨by omega,?_,by simp,Forall.nil,by trivial,?_,?_⟩
  · simp only [Zlength,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,List.length_replicate]
    rfl
  · intro p
    simp only [List.not_mem_nil]
    constructor
    · intro hh; exact False.elim hh
    · intro hh; omega
  · intro k hk
    constructor
    · intro _
      rintro ⟨d,hd,_,_⟩
      omega
    · intro _
      exact Znth_repeat 0 31624 k

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre a PreH1 PreH2 PreH3 PreH4
  simp only [Zlength,SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z,List.length_replicate]
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro n_pre a PreH1 PreH2 PreH3 PreH4
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4 := by
  intro n_pre a PreH1 PreH2 PreH3 PreH4
  exact PreH3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre a PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre a PreH1 PreH2 PreH3 PreH4
    | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre a PreH1 PreH2 PreH3 PreH4
    | exact proof_of_solver_entail_wit_1_split_goal_3 n_pre a PreH1 PreH2 PreH3 PreH4
    | exact proof_of_solver_entail_wit_1_split_goal_4 n_pre a PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact prime_prefix_table2_begin_mark__sieve_construction i prime_data_2 composite_data_2 PreH14 ⟨PreH8,PreH3⟩ PreH2 PreH1

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hh := prime_prefix_table2_capacity__sieve_construction i prime_data_2 composite_data_2 PreH14
  omega

theorem proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH7

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_2_split_goal_1 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_2_split_goal_2 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_2_split_goal_3 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_2_split_goal_4 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact prime_mark_table2_replace_step__sieve_marking_exits i j prime_data_2 composite_data_2 PreH1 PreH14

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simpa only [Zlength_replace_Znth] using PreH13

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_3_split_goal_1 n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_3_split_goal_2 n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1 := by
  intro n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact prime_mark_table2_finish__sieve_marking_exits i j prime_data_2 composite_data_2 PreH1 PreH14

theorem proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2 := by
  intro n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact PreH5

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  right
  intro n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_1_split_goal_1 n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_4_1_split_goal_2 n_pre a composite_data_2 j prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact prime_prefix_table2_advance_unmarked__sieve_construction i prime_data_2 composite_data_2 PreH14 ⟨PreH8,PreH3⟩ PreH2 PreH1

theorem proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hh := prime_prefix_table2_capacity__sieve_construction i prime_data_2 composite_data_2 PreH14
  omega

theorem proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  right
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_2_split_goal_1 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_4_2_split_goal_2 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_solver_entail_wit_4_2_split_goal_3 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1 := by
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact prime_prefix_table2_advance_marked__sieve_construction i prime_data_2 composite_data_2 PreH13 ⟨PreH7,PreH2⟩ PreH1

theorem proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3 := by
  unfold solver_entail_wit_4_3
  right
  intro n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_3_split_goal_1 n_pre a composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
