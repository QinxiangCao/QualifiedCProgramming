import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_goal
import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open quicksort_goal quicksort_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem manual_read_swap (l : List Int) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l)
    (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 =
    if k = j then Znth i l 0 else if k = i then Znth j l 0 else Znth k l 0 := by
  by_cases he : k = j
  · subst k; rw [if_pos rfl]; exact Znth_replace_Znth_Same 0 _ j _ (by simpa only [Zlength_replace_Znth] using hj)
  · rw [if_neg he, Znth_replace_Znth_Diff 0 _ j k _ (by simpa only [Zlength_replace_Znth] using hj)
      (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm he)]
    by_cases he' : k = i
    · subst k; rw [if_pos rfl]; exact Znth_replace_Znth_Same 0 l i _ hi
    · rw [if_neg he']; exact Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm he')


private theorem manual_range_lower_succ_iff (a b k : Int) :
    (a+1 ≤ k ∧ k < b) ↔ (a < k ∧ k < b) := by omega

private theorem manual_range_upper_succ_iff (a b k : Int) :
    (a ≤ k ∧ k < b+1) ↔ (a ≤ k ∧ k ≤ b) := by omega

private theorem manual_range_succ_iff (a b k : Int) :
    (a+1 ≤ k ∧ k < b+1) ↔ (a < k ∧ k ≤ b) := by omega

private theorem manual_forall_sublist (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo) (hhi : hi ≤ Zlength l) :
    Forall P (sublist lo hi l) ↔ ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0) := by
  by_cases hord : lo ≤ hi
  · constructor
    · intro h k hk
      have hr : 0 ≤ k-lo ∧ k-lo < Zlength (sublist lo hi l) := by
        have hlen : Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l ⟨hlo,hord⟩ hhi
        rw [hlen]
        omega
      have hv := lomuto_Forall_Znth P (sublist lo hi l) (k-lo) 0 h hr
      rw [Znth_sublist 0 lo (k-lo) hi l hlo (by omega)] at hv
      simpa only [Int.sub_add_cancel] using hv
    · exact lomuto_Forall_sublist_by_Znth P l lo hi ⟨hlo,hord⟩ hhi
  · rw [Zsublist_nil l lo hi (by omega)]
    constructor
    · intro _ k hk; omega
    · intro _; exact Forall.nil

private theorem manual_forall_suffix (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo+1 ∧ lo ≤ hi) (hhi : hi+1 ≤ Zlength l) :
    Forall P (sublist (lo+1) (hi+1) l) ↔ ∀ k, (lo < k ∧ k ≤ hi) → P (Znth k l 0) := by
  rw [manual_forall_sublist P l (lo+1) (hi+1) (by omega) hhi]
  constructor <;> intro h k hk <;> exact h k (by omega)


-- Preserve the original residual VCs and execute the split/cancel SL strategy.
-- Goal_apply uses explicit arguments; pure predicate conclusions can require
-- direct application of the same split theorem after spatial preprocessing.

theorem proof_of_partition_entail_wit_1_split_goal_1 : partition_entail_wit_1_split_goal_1 := by
  unfold partition_entail_wit_1_split_goal_1
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  intro k hk
  omega

theorem proof_of_partition_entail_wit_1_split_goal_2 : partition_entail_wit_1_split_goal_2 := by
  unfold partition_entail_wit_1_split_goal_2
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  intro k hk
  omega

theorem proof_of_partition_entail_wit_1_split_goal_3 : partition_entail_wit_1_split_goal_3 := by
  unfold partition_entail_wit_1_split_goal_3
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact same_outside_range_refl l low_pre high_pre

theorem proof_of_partition_entail_wit_1_split_goal_4 : partition_entail_wit_1_split_goal_4 := by
  unfold partition_entail_wit_1_split_goal_4
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact List.Perm.refl l

theorem proof_of_partition_entail_wit_1 : partition_entail_wit_1 := by
  unfold partition_entail_wit_1
  right
  intro high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_1 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_1 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_2 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_2 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_3 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_3 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | (solve | Goal_apply (proof_of_partition_entail_wit_1_split_goal_4 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4))
      | exact (proof_of_partition_entail_wit_1_split_goal_4 high_pre low_pre n_pre l PreH1 PreH2 PreH3 PreH4)
      | trivial

theorem proof_of_partition_entail_wit_2_1_split_goal_3 : partition_entail_wit_2_1_split_goal_3 := by
  unfold partition_entail_wit_2_1_split_goal_3
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  simp only [Zlength_replace_Znth] at PreH1
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  rw [lomuto_Znth_replace_neq (replace_Znth (i_2+1) (Znth j_2 l1_2 0) l1_2) high_pre j_2 (Znth (i_2+1) l1_2 0) 0 (by simp only [Zlength_replace_Znth]; omega) (by omega) (by omega),
    lomuto_Znth_replace_neq l1_2 high_pre (i_2+1) (Znth j_2 l1_2 0) 0 (by omega) (by omega) (by omega)]
  exact PreH13

theorem proof_of_partition_entail_wit_2_1_split_goal_4 : partition_entail_wit_2_1_split_goal_4 := by
  unfold partition_entail_wit_2_1_split_goal_4
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  simp only [Zlength_replace_Znth] at PreH1
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact same_outside_range_trans l l1_2 _ low_pre high_pre PreH12
    (same_outside_range_swap_inside l1_2 low_pre high_pre (i_2+1) j_2 PreH5 (by omega) (by omega) (by omega))

theorem proof_of_partition_entail_wit_2_1_split_goal_1 : partition_entail_wit_2_1_split_goal_1 := by
  unfold partition_entail_wit_2_1_split_goal_1
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_replace_Znth] at PreH1
  apply lomuto_Forall_sublist_by_Znth _ _ _ _ (by omega) (by simpa only [Zlength_replace_Znth] using (show j_2+1 ≤ Zlength l1_2 by omega))
  intro k hk
  rw [manual_read_swap l1_2 (i_2+1) j_2 k (by omega) (by omega) (by omega)]
  by_cases hj : k = j_2
  · rw [if_pos hj]
    exact (manual_forall_sublist _ l1_2 (i_2+1) j_2 (by omega) (by omega)).mp PreH15 (i_2+1) (by omega)
  · rw [if_neg hj, if_neg (by omega)]
    exact (manual_forall_sublist _ l1_2 (i_2+1) j_2 (by omega) (by omega)).mp PreH15 k (by omega)

theorem proof_of_partition_entail_wit_2_1_split_goal_2 : partition_entail_wit_2_1_split_goal_2 := by
  unfold partition_entail_wit_2_1_split_goal_2
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  simp only [Zlength_replace_Znth] at PreH1
  apply lomuto_Forall_sublist_by_Znth _ _ _ _ (by omega) (by simpa only [Zlength_replace_Znth] using (show (i_2+1)+1 ≤ Zlength l1_2 by omega))
  intro k hk
  rw [manual_read_swap l1_2 (i_2+1) j_2 k (by omega) (by omega) (by omega)]
  by_cases hj : k = j_2
  · rw [if_pos hj]
    have he : j_2 = i_2+1 := by omega
    simpa only [he] using PreH2
  · rw [if_neg hj]
    by_cases hi : k = i_2+1
    · rw [if_pos hi]; exact PreH2
    · rw [if_neg hi]
      exact (manual_forall_sublist _ l1_2 low_pre (i_2+1) (by omega) (by omega)).mp PreH14 k (by omega)

theorem proof_of_partition_entail_wit_2_1_split_goal_5 : partition_entail_wit_2_1_split_goal_5 := by
  unfold partition_entail_wit_2_1_split_goal_5
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  simp only [Zlength_replace_Znth] at PreH1
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact PreH11.trans (lomuto_permutation_swap_Znth l1_2 (i_2+1) j_2 0 (by omega) (by omega))

theorem proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1 := by
  unfold partition_entail_wit_2_1
  right
  intro high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_partition_entail_wit_2_1_split_goal_1 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_partition_entail_wit_2_1_split_goal_2 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_partition_entail_wit_2_1_split_goal_3 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_partition_entail_wit_2_1_split_goal_4 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      | exact proof_of_partition_entail_wit_2_1_split_goal_5 high_pre low_pre n_pre l l1_2 j_2 i_2 pivot_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_partition_return_wit_1_split_goal_1 : partition_return_wit_1_split_goal_1 := by
  unfold partition_return_wit_1_split_goal_1
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  simp only [Zlength_replace_Znth] at PreH1
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  have hj : j = high_pre := by omega
  rw [hj] at PreH14
  rw [← PreH12]
  exact partitioned_at_after_lomuto_final_swap l1_2 low_pre high_pre pivot i PreH4 (by omega) PreH7 (by omega) PreH12 PreH13 PreH14

theorem proof_of_partition_return_wit_1_split_goal_2 : partition_return_wit_1_split_goal_2 := by
  unfold partition_return_wit_1_split_goal_2
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  simp only [Zlength_replace_Znth] at PreH1
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  rw [← PreH12]
  exact same_outside_range_trans l l1_2 _ low_pre high_pre PreH11
    (same_outside_range_swap_inside l1_2 low_pre high_pre (i+1) high_pre PreH4 (by omega) (by omega) (by omega))

theorem proof_of_partition_return_wit_1_split_goal_3 : partition_return_wit_1_split_goal_3 := by
  unfold partition_return_wit_1_split_goal_3
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  simp only [Zlength_replace_Znth] at PreH1
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  rw [← PreH12]
  exact PreH10.trans (lomuto_permutation_swap_Znth l1_2 (i+1) high_pre 0 (by omega) (by omega))

theorem proof_of_partition_return_wit_1 : partition_return_wit_1 := by
  unfold partition_return_wit_1
  right
  intro high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_1 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
      | exact (proof_of_partition_return_wit_1_split_goal_1 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_2 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
      | exact (proof_of_partition_return_wit_1_split_goal_2 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | (solve | Goal_apply (proof_of_partition_return_wit_1_split_goal_3 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14))
      | exact (proof_of_partition_return_wit_1_split_goal_3 high_pre low_pre n_pre l l1_2 j i pivot PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14)
      | trivial

theorem proof_of_quicksort_range_return_wit_1_split_goal_1 : quicksort_range_return_wit_1_split_goal_1 := by
  unfold quicksort_range_return_wit_1_split_goal_1
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  have hl3 := PreH3.1
  have hl2 := PreH7.1
  have hp3 := partitioned_at_preserved_by_left_local l1_2 l1_3 left_pre right_pre retval PreH6 PreH17 PreH7 (by omega) PreH14
  have hp4 := partitioned_at_preserved_by_right_local l1_3 l1_4 left_pre right_pre retval PreH2 PreH17 PreH3 (by omega) hp3
  have hsl : range_nondecreasing l1_4 left_pre (retval - 1) := by
    apply range_nondecreasing_ext_local l1_3 l1_4 left_pre (retval - 1) hl3 _ PreH8
    intro k hk
    exact PreH3.2 k (by omega) (Or.inl (by omega))
  exact quicksort_partition_combine_both_sides_local l1_4 left_pre right_pre retval PreH17 (by omega) ⟨PreH10, PreH11⟩ hp4 hsl PreH4

theorem proof_of_quicksort_range_return_wit_1_split_goal_2 : quicksort_range_return_wit_1_split_goal_2 := by
  unfold quicksort_range_return_wit_1_split_goal_2
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  have h1 := same_outside_range_weaken_local l1_2 l1_3 left_pre (retval - 1) left_pre right_pre (by omega) (by omega) PreH7
  have h2 := same_outside_range_weaken_local l1_3 l1_4 (retval + 1) right_pre left_pre right_pre (by omega) (by omega) PreH3
  exact same_outside_range_trans_local l l1_3 l1_4 left_pre right_pre
    (same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH13 h1) h2

theorem proof_of_quicksort_range_return_wit_1_split_goal_3 : quicksort_range_return_wit_1_split_goal_3 := by
  unfold quicksort_range_return_wit_1_split_goal_3
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact PreH12.trans (PreH6.trans PreH2)

theorem proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1 := by
  unfold quicksort_range_return_wit_1
  right
  intro right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact (proof_of_quicksort_range_return_wit_1_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact (proof_of_quicksort_range_return_wit_1_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_1_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
      | exact (proof_of_quicksort_range_return_wit_1_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 l1_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | trivial

theorem proof_of_quicksort_range_return_wit_2_split_goal_1 : quicksort_range_return_wit_2_split_goal_1 := by
  unfold quicksort_range_return_wit_2_split_goal_1
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  have hlen := PreH3.1
  have hp := partitioned_at_preserved_by_right_local l1_2 l1_3 left_pre right_pre retval PreH2 PreH14 PreH3 (by omega) PreH11
  exact quicksort_partition_combine_right_only_local l1_3 left_pre right_pre retval PreH14 (by omega) (by omega) hp PreH4

theorem proof_of_quicksort_range_return_wit_2_split_goal_2 : quicksort_range_return_wit_2_split_goal_2 := by
  unfold quicksort_range_return_wit_2_split_goal_2
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH10
    (same_outside_range_weaken_local l1_2 l1_3 (retval + 1) right_pre left_pre right_pre (by omega) (by omega) PreH3)

theorem proof_of_quicksort_range_return_wit_2_split_goal_3 : quicksort_range_return_wit_2_split_goal_3 := by
  unfold quicksort_range_return_wit_2_split_goal_3
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact PreH9.trans PreH2

theorem proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2 := by
  unfold quicksort_range_return_wit_2
  right
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_2_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_2_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_2_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_2_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | trivial

theorem proof_of_quicksort_range_return_wit_3_split_goal_1 : quicksort_range_return_wit_3_split_goal_1 := by
  unfold quicksort_range_return_wit_3_split_goal_1
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  have hlen := PreH4.1
  have hp := partitioned_at_preserved_by_left_local l1_2 l1_3 left_pre right_pre retval PreH3 PreH14 PreH4 (by omega) PreH11
  exact quicksort_partition_combine_left_only_local l1_3 left_pre right_pre retval PreH14 (by omega) (by omega) hp PreH5

theorem proof_of_quicksort_range_return_wit_3_split_goal_2 : quicksort_range_return_wit_3_split_goal_2 := by
  unfold quicksort_range_return_wit_3_split_goal_2
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact same_outside_range_trans_local l l1_2 l1_3 left_pre right_pre PreH10
    (same_outside_range_weaken_local l1_2 l1_3 left_pre (retval - 1) left_pre right_pre (by omega) (by omega) PreH4)

theorem proof_of_quicksort_range_return_wit_3_split_goal_3 : quicksort_range_return_wit_3_split_goal_3 := by
  unfold quicksort_range_return_wit_3_split_goal_3
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact PreH9.trans PreH3

theorem proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3 := by
  unfold quicksort_range_return_wit_3
  right
  intro right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_3_split_goal_1 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_3_split_goal_2 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_3_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_quicksort_range_return_wit_3_split_goal_3 right_pre left_pre n_pre l l1_2 retval l1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | trivial

theorem proof_of_quicksort_range_return_wit_4_split_goal_1 : quicksort_range_return_wit_4_split_goal_1 := by
  unfold quicksort_range_return_wit_4_split_goal_1
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  intro i j hi hij hj
  have he : i = j := by omega
  rw [he] <;> omega

theorem proof_of_quicksort_range_return_wit_4_split_goal_2 : quicksort_range_return_wit_4_split_goal_2 := by
  unfold quicksort_range_return_wit_4_split_goal_2
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact same_outside_range_refl l left_pre right_pre

theorem proof_of_quicksort_range_return_wit_4_split_goal_3 : quicksort_range_return_wit_4_split_goal_3 := by
  unfold quicksort_range_return_wit_4_split_goal_3
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  exact List.Perm.refl l

theorem proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4 := by
  unfold quicksort_range_return_wit_4
  right
  intro right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_1 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_range_return_wit_4_split_goal_1 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_2 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_range_return_wit_4_split_goal_2 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | (solve | Goal_apply (proof_of_quicksort_range_return_wit_4_split_goal_3 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_range_return_wit_4_split_goal_3 right_pre left_pre n_pre l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | trivial

theorem proof_of_quicksort_return_wit_1_split_goal_1 : quicksort_return_wit_1_split_goal_1 := by
  unfold quicksort_return_wit_1_split_goal_1
  intro n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  try simp (disch := omega) only [manual_forall_sublist, manual_forall_suffix, manual_range_succ_iff, manual_range_lower_succ_iff, manual_range_upper_succ_iff] at *
  apply range_nondecreasing_full_to_increasing
  simpa only [PreH1] using PreH4

theorem proof_of_quicksort_return_wit_1 : quicksort_return_wit_1 := by
  unfold quicksort_return_wit_1
  right
  intro n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | (solve | Goal_apply (proof_of_quicksort_return_wit_1_split_goal_1 n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6))
      | exact (proof_of_quicksort_return_wit_1_split_goal_1 n_pre l l1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)
      | trivial

theorem proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2 := by
  unfold partition_entail_wit_2_2
  right
  intro high low n l current j i pivot hlen hread hjh hpivot hlo hlh hhigh hli hij hjh' hperm hout hreadpivot hleft hmiddle
  have hnew : Forall (fun x : Int => pivot < x) (sublist (i+1) (j+1) current) := by
    apply lomuto_Forall_sublist_by_Znth _ current _ _ (by omega) (by omega)
    intro k hk
    by_cases he : k = j
    · subst k; exact hread
    · exact (manual_forall_sublist _ current (i+1) j (by omega) (by omega)).mp hmiddle k (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact hnew


end SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_proof_manual
