import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P018_1382B_sequential_nim_goal P018_1382B_sequential_nim_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n piles h1 h2 h3 h4 i hi
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n piles h1 h2 h3 h4
  exact h3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n piles h1 h2 h3 h4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_solver_entail_wit_1_split_goal_1 n piles h1 h2 h3 h4
    · exact proof_of_solver_entail_wit_1_split_goal_2 n piles h1 h2 h3 h4

theorem proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1 := by
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨⟨h6, by omega⟩, h8, Or.inl (by omega)⟩

theorem proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1 := by
  unfold solver_entail_wit_3_1
  right
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_3_1_split_goal_1 n piles c h1 h2 h3 h4 h5 h6 h7 h8

theorem proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1 := by
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨⟨h7, by omega⟩, h9, Or.inr h1⟩

theorem proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2 := by
  unfold solver_entail_wit_3_2
  right
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8 h9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_3_2_split_goal_1 n piles c h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8
  have hn : ¬ FirstWins piles := by
    rintro ⟨k, hk, hw⟩
    have he := leading_ones_unique__return_semantics piles k c hk h8
    subst k
    rcases hw with ⟨hend, heven⟩ | ⟨hbefore, heven⟩
    · omega
    · have hodd := odd_of_nonnegative_rem_nonzero__return_semantics c h6 h1
      simp only [hodd, Bool.false_eq_true] at heven
  have hs : Spec piles 0 := Or.inr ⟨rfl, hn⟩
  have hb : SolverReturnBridge 0 0 := Or.inr ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (0 : Int) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8
  have he := even_of_nonnegative_rem_zero__return_semantics c h6 h1
  have hw : FirstWins piles := ⟨c, h8, Or.inr ⟨by omega, he⟩⟩
  have hs : Spec piles 1 := Or.inl ⟨rfl, hw⟩
  have hb : SolverReturnBridge 1 1 := Or.inl ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (1 : Int) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8
  have he := even_of_nonnegative_rem_not_one__return_semantics n (by omega) h1
  have hn : ¬ FirstWins piles := by
    rintro ⟨k, hk, hw⟩
    have heq := leading_ones_unique__return_semantics piles k c hk h8
    subst k
    rcases hw with ⟨hend, hodd⟩ | ⟨hbefore, hparity⟩
    · rw [h2, he] at hodd
      contradiction
    · omega
  have hs : Spec piles 0 := Or.inr ⟨rfl, hn⟩
  have hb : SolverReturnBridge 0 0 := Or.inr ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (0 : Int) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  unfold solver_return_wit_4
  right
  intro n piles c h1 h2 h3 h4 h5 h6 h7 h8
  have ho := odd_of_nonnegative_rem_nonzero__return_semantics n (by omega) (by omega)
  have hw : FirstWins piles := ⟨c, h8, Or.inl ⟨by omega, by rwa [h2]⟩⟩
  have hs : Spec piles 1 := Or.inl ⟨rfl, hw⟩
  have hb : SolverReturnBridge 1 1 := Or.inl ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (1 : Int) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_proof_manual
