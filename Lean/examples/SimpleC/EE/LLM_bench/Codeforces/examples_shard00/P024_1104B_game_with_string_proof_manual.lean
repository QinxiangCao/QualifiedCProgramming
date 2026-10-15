import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray
private theorem prefix_succ (xs : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength xs) :
    sublist 0 (i+1) xs=sublist 0 i xs++[Znth i xs 0] := by
  rw [sublist_split 0 (i+1) i xs (by omega) (by omega),sublist_single 0 i xs hi]

private theorem clear_stack (x top capacity : Int) (reduced : List Int) (hb : 0≤top ∧ top≤capacity) :
    (charArray.full x top reduced ** charArray.undef_seg x top capacity) |-- charArray.undef_full x capacity := by
  sep_apply (charArray.full_to_undef_full x top reduced)
  sep_apply (charArray.undef_full_to_undef_seg x top)
  sep_apply (charArray.undef_seg_merge_to_undef_seg x 0 top capacity (by omega))
  sep_apply (charArray.undef_seg_to_undef_full x 0 capacity)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro text PreH1 PreH2 PreH3
  change PrefixGameState [] [] 0
  apply prefix_game_state_of_normal_trace__stack_transitions
  · refine ⟨by omega,[[]],rfl,rfl,rfl,?_⟩
    intro k hk;omega
  · apply (pair_deletion_irreducible_adjacent__stack_transitions _).mpr
    intro k hk;change 0≤k ∧ k< -1 at hk;omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro text PreH1 PreH2 PreH3
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro text PreH1 PreH2 PreH3
  exact PreH3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro text PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 text PreH1 PreH2 PreH3
      | exact proof_of_solver_entail_wit_1_split_goal_2 text PreH1 PreH2 PreH3
      | exact proof_of_solver_entail_wit_1_split_goal_3 text PreH1 PreH2 PreH3

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hi:=sentinel_nonzero_index_bound__stack_transitions text i (by omega) PreH15
  rw [nth_append 0 text [0] i (by omega)] at PreH1
  have hstate : PrefixGameState (sublist 0 (i+1) text) (sublist 0 (top-1) reduced_2) (moves+1) := by
    rw [prefix_succ text i (by omega),PreH10]
    apply prefix_game_state_pop_pair__stack_transitions _ _ _ _ PreH14 (by omega)
    rwa [←PreH10]
  have hl:=len_prefix (top-1) reduced_2 (by omega)
  refine Automation.exp_right_rule (CRules:=naive_C_Rules) (sublist 0 (top-1) reduced_2) ?_
  split_pure_spatial
  · sep_apply (charArray.full_split_to_seg ( &("stack") ) (top-1) top reduced_2 (by omega))
    sep_apply (charArray.seg_to_full ( &("stack") ) 0 (top-1) (sublist 0 (top-1) reduced_2))
    simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
    sep_apply (charArray.seg_to_undef_seg ( &("stack") ) (top-1) top (sublist (top-1) top reduced_2))
    sep_apply (charArray.undef_seg_merge_to_undef_seg ( &("stack") ) (top-1) top 100005 (by omega))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals solve | exact hstate | exact PreH5 | omega

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hi:=sentinel_nonzero_index_bound__stack_transitions text i (by omega) PreH14
  rw [←PreH12,nth_append 0 text [0] i (by omega),prefix_succ text i (by omega)]
  apply prefix_game_state_push__stack_transitions _ _ _ _ PreH13
  left
  apply List.length_eq_zero_iff.mp
  simp only [Zlength,Int.ofNat_eq_coe] at PreH9
  omega

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3 := by
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hi:=sentinel_nonzero_index_bound__stack_transitions text i (by omega) PreH14
  omega

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_solver_entail_wit_2_2_split_goal_2 text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
      | exact proof_of_solver_entail_wit_2_2_split_goal_3 text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hi:=sentinel_nonzero_index_bound__stack_transitions text i (by omega) PreH15
  rw [←PreH13,nth_append 0 text [0] i (by omega),prefix_succ text i (by omega)]
  apply prefix_game_state_push__stack_transitions _ _ _ _ PreH14
  right
  refine ⟨by omega,?_⟩
  rw [←PreH10]
  rwa [nth_append 0 text [0] i (by omega)] at PreH1

theorem proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2 := by
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_2_3_split_goal_3 : solver_entail_wit_2_3_split_goal_3 := by
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hi:=sentinel_nonzero_index_bound__stack_transitions text i (by omega) PreH15
  omega

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  right
  intro text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_solver_entail_wit_2_3_split_goal_2 text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_solver_entail_wit_2_3_split_goal_3 text moves reduced_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro text moves reduced top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  dump_pre_spatial
  have hi:=terminator_zero_index_eq_length__final_result text i (by omega) PreH3 PreH13
  rw [sublist_self text i hi] at PreH12
  exact prefix_game_state_spec_parity__final_result text reduced moves PreH12

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  intro text moves reduced top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact clear_stack ( &("stack") ) top 100005 reduced (by omega)

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro text moves reduced top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  all_goals first
    | exact proof_of_solver_return_wit_1_split_goal_1 text moves reduced top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_return_wit_1_split_goal_spatial text moves reduced top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_proof_manual
