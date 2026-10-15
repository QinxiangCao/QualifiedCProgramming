import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray

private theorem subsequence_member (x : Int) (xs l : List Int)
    (h : ListLib.is_subsequence (x :: xs) l) :
    ∃ k, (0 ≤ k ∧ k < Zlength l) ∧ Znth k l 0 = x := by
  induction l with
  | nil => exact False.elim h
  | cons a l ih =>
    rcases h with h | ⟨rfl, h⟩
    · obtain ⟨k, hk, hv⟩ := ih h
      refine ⟨k + 1, ?_, ?_⟩
      · simp only [Zlength_cons]; omega
      · rw [Znth_cons 0 (k + 1) a l (by omega)]
        simpa using hv
    · exact ⟨0, ⟨by omega, by simp only [Zlength_cons]; have := Zlength_nonneg l; omega⟩, rfl⟩

private theorem singleton_subsequence (x : Int) (l : List Int) (k : Int)
    (hk : 0 ≤ k ∧ k < Zlength l) (hv : Znth k l 0 = x) :
    ListLib.is_subsequence [x] l := by
  induction l generalizing k with
  | nil => simp only [Zlength_nil] at hk; omega
  | cons a l ih =>
    by_cases h0 : k = 0
    · subst k
      refine Or.inr ⟨?_, ?_⟩
      · simpa using hv.symm
      · cases l <;> trivial
    · apply Or.inl
      apply ih (k - 1)
      · simp only [Zlength_cons] at hk; omega
      · rw [Znth_cons 0 k a l (by omega)] at hv
        exact hv

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  unfold solver_entail_wit_1_split_goal_1
  intro m_pre n_pre right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dump_pre_spatial
  exact PreH6

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  unfold solver_entail_wit_1_split_goal_2
  intro m_pre n_pre right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  dump_pre_spatial
  exact PreH5

theorem proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial := by
  unfold solver_entail_wit_1_split_goal_spatial
  intro m_pre n_pre right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  simp only [SimpleC.SL.CommonAssertion.DerivedPredSig.sizeof_char, Int.zero_mul, Int.add_zero, Int.one_mul]
  cancel

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro m_pre n_pre right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  simp only [SimpleC.SL.CommonAssertion.DerivedPredSig.sizeof_char, Int.zero_mul, Int.add_zero, Int.one_mul]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro m_pre n_pre right left retval k_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simp only [SimpleC.SL.CommonAssertion.DerivedPredSig.sizeof_char, Int.zero_mul, Int.add_zero, Int.one_mul]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 1001 (0 : Int)) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | rfl
      | exact (fun v hv => Or.inl (Znth_repeat 0 1001 v))
      | exact (fun k hk => False.elim (by omega))
      | exact (fun v hv => False.elim (by
          have h := Znth_repeat (0 : Int) 1001 v
          have heq := hv.2
          change Znth v (List.replicate 1001 (0 : Int)) 0 = 1 at heq
          change Znth v (List.replicate 1001 (0 : Int)) 0 = 0 at h
          omega))

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  unfold solver_entail_wit_3_split_goal_1
  intro m_pre n_pre right left k_4 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simpa only [Zlength_replace_Znth] using PreH13

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro m_pre n_pre right left k_4 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    simpa only [Zlength_replace_Znth] using PreH13

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  unfold solver_entail_wit_4_split_goal_1
  intro m_pre n_pre right left k_9 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  intro k hk
  omega

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  unfold solver_entail_wit_4_split_goal_2
  intro m_pre n_pre right left k_9 seen_l_2 i k_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  intro v hv
  obtain ⟨k, hk, heq⟩ := PreH15 v hv
  exact ⟨k, ⟨hk.1, by omega⟩, heq⟩

theorem proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3 := by
  unfold solver_entail_wit_4_split_goal_3
  intro m_pre n_pre right left k_9 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  intro k hk
  exact PreH14 k ⟨hk.1, by omega⟩

theorem proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4 := by
  unfold solver_entail_wit_4_split_goal_4
  intro m_pre n_pre right left k_9 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH13

theorem proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5 := by
  unfold solver_entail_wit_4_split_goal_5
  intro m_pre n_pre right left k_9 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH9

theorem proof_of_solver_entail_wit_4_split_goal_6 : solver_entail_wit_4_split_goal_6 := by
  unfold solver_entail_wit_4_split_goal_6
  intro m_pre n_pre right left k_9 seen_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH8

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro m_pre n_pre right left k_9 seen_l_2 i k_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hi : i = n_pre := by omega
  subst i
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | exact (fun k hk => False.elim (by omega))

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  intro m_pre b_pre n_pre a_pre right left k_4 seen_l j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hspec : Spec left right none := by
    left
    refine ⟨rfl, ?_⟩
    rintro ⟨c, hn, hl, hr⟩
    cases c with
    | nil => exact hn rfl
    | cons x xs =>
      obtain ⟨kl, hkl, hlv⟩ := subsequence_member x xs left hl
      obtain ⟨kr, hkr, hrv⟩ := subsequence_member x xs right hr
      have h1 := PreH14 kl ⟨hkl.1, by omega⟩
      have h0 := PreH16 kr ⟨hkr.1, by omega⟩
      rw [hlv] at h1
      rw [hrv] at h0
      omega
  Left
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (none : Option (List Int)) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hspec | rfl

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  intro m_pre b_pre n_pre a_pre right left k_4 seen_l j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hx := PreH10 j ⟨PreH11, PreH2⟩
  have hxrange : 0 ≤ Znth j right 0 ∧ Znth j right 0 < 1001 := by omega
  have hseen : Znth (Znth j right 0) seen_l 0 = 1 := by
    rcases PreH14 _ hxrange with h | h
    · exact False.elim (PreH18 h)
    · exact h
  obtain ⟨kl, hkl, hklv⟩ := PreH16 _ ⟨hxrange, hseen⟩
  have hspec : Spec left right (some [Znth j right 0]) := by
    right
    refine ⟨[Znth j right 0], rfl, ?_⟩
    constructor
    · refine ⟨by simp, ?_, ?_⟩
      · exact singleton_subsequence _ left kl ⟨hkl.1, by omega⟩ hklv
      · exact singleton_subsequence _ right j ⟨PreH11, by omega⟩ rfl
    · intro c hc
      rcases hc with ⟨hn, _, _⟩
      cases c with
      | nil => exact False.elim (hn rfl)
      | cons y ys =>
        simp only [Zlength_cons, Zlength_nil]
        have := Zlength_nonneg ys
        omega
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (some [Znth j right 0]) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hspec | rfl

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_proof_manual
