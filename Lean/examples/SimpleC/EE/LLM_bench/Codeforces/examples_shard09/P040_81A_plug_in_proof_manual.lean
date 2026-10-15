import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P040_81A_plug_in_goal P040_81A_plug_in_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray

private theorem prefix_succ (xs : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength xs) :
    sublist 0 (i + 1) xs = sublist 0 i xs ++ [Znth i xs 0] := by
  rw [sublist_split 0 (i + 1) i xs (by omega) (by omega), sublist_single 0 i xs hi]

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre text PreH1 PreH2 PreH3 PreH4
  refine ⟨[[]], ?_, rfl, rfl, ?_, ?_⟩
  · intro h; cases h
  · intro i hi
    change 0 ≤ i ∧ i < 0 at hi
    omega
  · rintro ⟨q, i, hi, _⟩
    change 0 ≤ i ∧ i < -1 at hi
    omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre text PreH1 PreH2 PreH3 PreH4
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro n_pre text PreH1 PreH2 PreH3 PreH4
  exact PreH3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre text PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre text PreH1 PreH2 PreH3 PreH4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre text PreH1 PreH2 PreH3 PreH4
      | exact proof_of_solver_entail_wit_1_split_goal_3 n_pre text PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro out_pre n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs : stack_2 ≠ [] := by intro h; subst stack_2; change top = 0 at PreH12; omega
  have hp : Spec (sublist 0 (i + 1) text) (sublist 0 (top - 1) stack_2) := by
    rw [PreH12, prefix_succ text i (by omega)]
    apply Spec_extend_drop_equal__stack_transitions _ stack_2 _ PreH13 hs
    rwa [← PreH12]
  have hl : Zlength (sublist 0 (top - 1) stack_2) = top - 1 :=
    ListLib.Zlength_sublist0 (top - 1) stack_2 (by change 0 ≤ top - 1 ∧ top - 1 ≤ Zlength stack_2; omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (sublist 0 (top - 1) stack_2) ?_
  split_pure_spatial
  · sep_apply (charArray.full_split_to_seg out_pre (top - 1) top stack_2 (by omega))
    sep_apply (charArray.seg_to_full out_pre 0 (top - 1) (sublist 0 (top - 1) stack_2))
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    sep_apply (charArray.seg_to_undef_seg out_pre (top - 1) top (sublist (top - 1) top stack_2))
    sep_apply (charArray.undef_seg_merge_to_undef_seg out_pre (top - 1) top (n_pre + 1) (by omega))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hp | exact PreH7 | omega

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hs : stack_2 = [] := by
    cases stack_2 with
    | nil => rfl
    | cons x xs => have := Zlength_nonneg xs; rw [Zlength_cons] at PreH11; omega
  rw [prefix_succ text i (by omega)]
  exact Spec_extend_keep_distinct__stack_transitions _ stack_2 _ PreH12 (Or.inl hs)

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.zero_add]
  omega

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_2_split_goal_2 n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [prefix_succ text i (by omega)]
  apply Spec_extend_keep_distinct__stack_transitions _ stack_2 _ PreH13
  right
  rwa [← PreH12]

theorem proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2 := by
  intro n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [Zlength_app, Zlength_cons, Zlength_nil, Int.zero_add]
  omega

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  unfold solver_entail_wit_2_3
  right
  intro n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_2_3_split_goal_2 n_pre text stack_2 top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro out_pre n_pre text stack top i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  rw [sublist_self text i (by omega)] at PreH11
  rw [PreH10]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) stack ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH11 | rfl

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_proof_manual
