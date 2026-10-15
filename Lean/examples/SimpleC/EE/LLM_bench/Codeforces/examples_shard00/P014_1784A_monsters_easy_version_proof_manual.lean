import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre input sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  refine ⟨by omega,[],?_,rfl,?_,?_⟩
  · change MaximalCascadePreparation [] []
    refine ⟨⟨rfl,?_,?_,?_⟩,?_⟩
    · intro j hj;simp only [Zlength_nil] at hj;omega
    · intro h;simp only [Zlength_nil] at h;omega
    · intro j hj;simp only [Zlength_nil] at hj;omega
    · intro alt ha j hj;simp only [Zlength_nil] at hj;omega
  · rfl
  · intro h;omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre input sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hinput:=Forall_Znth_bounds__greedy_transitions input 1 (Zlength input) PreH8
  have hsorted : Forall (fun x=>1≤x ∧ x≤Zlength input) sorted_2 := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    exact hinput.mem (PreH1.mem_iff.mpr hx)
  intro k hk
  have hh:=Forall_Znth_elim__greedy_transitions sorted_2 1 (Zlength input) k hsorted (by omega)
  omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro n_pre input sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre input sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre input sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply prefix_greedy_step__greedy_transitions
  · omega
  · exact (PreH10 i (by omega)).1
  · exact PreH9
  · exact PreH17
  · rw [min_eq_right (by omega : Znth i sorted_2 0≤kept+1)]

theorem proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2 := by
  intro n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  nlinarith

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_1_split_goal_1 n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_solver_entail_wit_2_1_split_goal_2 n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply prefix_greedy_step__greedy_transitions
  · omega
  · exact (PreH10 i (by omega)).1
  · exact PreH9
  · exact PreH17
  · rw [min_eq_left (by omega : kept+1≤Znth i sorted_2 0)]

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hh:=PreH10 i (by omega)
  nlinarith

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_solver_entail_wit_2_2_split_goal_2 n_pre input spent kept i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n_pre input spent kept i sorted PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  obtain ⟨_,prepared,_,_,_,hs⟩:=PreH16
  exact hs (by omega)

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro n_pre input spent kept i sorted PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 n_pre input spent kept i sorted PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_proof_manual
