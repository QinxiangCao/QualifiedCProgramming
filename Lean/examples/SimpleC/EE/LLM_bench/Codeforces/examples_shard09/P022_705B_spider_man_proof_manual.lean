import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P022_705B_spider_man_goal P022_705B_spider_man_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array

theorem proof_of_next_parity_return_wit_1_split_goal_1 : next_parity_return_wit_1_split_goal_1 := by
  intro a par h1 h2 h3 h4
  exact ⟨⟨h1,h2⟩,h3,land_one_eq_rem_two_nonnegative__parity_foundation _ (by omega)⟩

theorem proof_of_next_parity_return_wit_1 : next_parity_return_wit_1 := by
  unfold next_parity_return_wit_1
  right
  intro a par h1 h2 h3 h4
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_next_parity_return_wit_1_split_goal_1 a par h1 h2 h3 h4

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro out n added h1 h2 h3 h4
  dump_pre_spatial
  rw [Zsublist_nil added 0 0 (by omega)]
  refine ⟨rfl,⟨by omega,by omega⟩,rfl,?_⟩
  intro i hi
  change 0≤i ∧ i<0 at hi
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro out n added h1 h2 h3 h4
  dump_pre_spatial
  exact h3

theorem proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial := by
  intro out n added h1 h2 h3 h4
  sep_apply (intArray.full_shape_to_seg_shape out n)
  exact intArray.seg_shape_to_undef_seg out 0 n

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro out n added h1 h2 h3 h4
  split_pure_spatial
  · exact proof_of_solver_entail_wit_1_split_goal_spatial out n added h1 h2 h3 h4
  · split_pures
    · exact proof_of_solver_entail_wit_1_split_goal_1 out n added h1 h2 h3 h4
    · exact proof_of_solver_entail_wit_1_split_goal_2 out n added h1 h2 h3 h4

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n added written par i retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  apply spider_prefix_state_extend__prefix_evolution added written par i retval 1
  · omega
  · intro j hj
    exact (h7 j (by omega)).1
  · exact h2
  · exact h10
  · have hb := rem_nonneg_bounds (par+(Znth i added 0-1)) 2 (by rcases h2 with ⟨hp,ha,hn⟩;omega) (by omega)
    exact Or.inl ⟨rfl,by rcases h2 with ⟨hp,ha,hn⟩;omega⟩

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro n added written par i retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_1_split_goal_1 n added written par i retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n added written par i retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst retval
  apply spider_prefix_state_extend__prefix_evolution added written par i 0 2
  · omega
  · intro j hj
    exact (h7 j (by omega)).1
  · exact h2
  · exact h10
  · exact Or.inr ⟨rfl,rfl⟩

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro n added written par i retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_2_split_goal_1 n added written par i retval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro out n added written par i h1 h2 h3 h4 h5 h6 h7 h8
  have hi : i=n := by omega
  subst i
  rw [sublist_self added n h4] at h8
  Exists written
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact spider_prefix_state_implies_spec__final_result added written par
      (fun j hj => (h5 j (by omega)).1) h8

theorem proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1 := by
  intro out n addedPtr added written par i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  dump_pre_spatial
  exact h14.2.1.1

theorem proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2 := by
  intro out n addedPtr added written par i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  dump_pre_spatial
  exact h14.2.1.2

theorem proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure := by
  unfold solver_partial_solve_wit_2_pure
  right
  intro out n addedPtr added written par i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  split_pures
  · exact proof_of_solver_partial_solve_wit_2_pure_split_goal_1 out n addedPtr added written par i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  · exact proof_of_solver_partial_solve_wit_2_pure_split_goal_2 out n addedPtr added written par i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_proof_manual
