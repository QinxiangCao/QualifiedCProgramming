import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_goal
import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open split_array_largest_sum_goal split_array_largest_sum_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem quot_half_lt (a : Int) (ha : 0 < a) : Z.quot a 2 < a := by
  by_cases he : a = 1
  · subst a; decide
  · have h := Z.quot_le_upper_bound a 2 (a-1) (by omega) (by omega)
    omega

private theorem forall_nonnegative_index (l : List Int) (hv : Forall (fun x => 0 ≤ x) l)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : 0 ≤ Znth i l 0 := by
  have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
  have hm := hv.mem (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm

private theorem prefix_nonnegative (l : List Int) (i : Int)
    (hv : Forall (fun x => 0 ≤ x) l) (_ : 0 ≤ i ∧ i ≤ Zlength l) :
    Forall (fun x => 0 ≤ x) (sublist 0 i l) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  exact hv.mem (List.mem_of_mem_take (by simpa [sublist] using hx))

theorem proof_of_check_entail_wit_1 : check_entail_wit_1 := by
  unfold check_entail_wit_1
  right
  intro l n_pre m_pre cap_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    simpa [sublist] using split_progress_empty cap_pre

theorem proof_of_check_entail_wit_2_1 : check_entail_wit_2_1 := by
  unfold check_entail_wit_2_1
  right
  intro l n_pre m_pre cap_pre cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hn : 0 ≤ Znth i l 0 := forall_nonnegative_index l PreH11 i ⟨PreH13, by omega⟩
  have hv : Forall (fun x => 0 ≤ x) (sublist 0 i l) := prefix_nonnegative l i PreH11 ⟨PreH13, by omega⟩
  have hs : sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l 0] := sublist_snoc_Znth 0 l i ⟨PreH13, by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [hs]
    exact split_progress_new_segment _ _ _ _ _ hv ⟨hn, PreH2⟩ PreH19 PreH1

theorem proof_of_check_entail_wit_2_2 : check_entail_wit_2_2 := by
  unfold check_entail_wit_2_2
  right
  intro l n_pre m_pre cap_pre cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hn : 0 ≤ Znth i l 0 := forall_nonnegative_index l PreH11 i ⟨PreH13, by omega⟩
  have hv : Forall (fun x => 0 ≤ x) (sublist 0 i l) := prefix_nonnegative l i PreH11 ⟨PreH13, by omega⟩
  have hs : sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l 0] := sublist_snoc_Znth 0 l i ⟨PreH13, by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · rw [hs]; exact split_progress_extend _ _ _ _ _ hv ⟨hn, PreH2⟩ PreH19 PreH1
    · omega

theorem proof_of_check_return_wit_1 : check_return_wit_1 := by
  unfold check_return_wit_1
  right
  intro l n_pre m_pre cap_pre cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hp : SplitProgress l cap_pre cnt cur := by
    have hi : i = Zlength l := by omega
    rw [hi, sublist_self l _ rfl] at PreH18
    exact PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _
    exact split_progress_infeasible l cap_pre cnt cur m_pre PreH5 PreH10 hp PreH1

theorem proof_of_check_return_wit_2 : check_return_wit_2 := by
  unfold check_return_wit_2
  right
  intro l n_pre m_pre cap_pre cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hp : SplitProgress l cap_pre cnt cur := by
    have hi : i = Zlength l := by omega
    rw [hi, sublist_self l _ rfl] at PreH18
    exact PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _
    exact split_progress_feasible l cap_pre cnt cur m_pre ⟨PreH5, by omega⟩ PreH7 PreH10 hp PreH1

theorem proof_of_check_return_wit_3 : check_return_wit_3 := by
  unfold check_return_wit_3
  right
  intro l n_pre m_pre cap_pre cur cnt i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro _
    apply (split_infeasible_legacy l m_pre cap_pre ⟨PreH5, by omega⟩ PreH7 PreH10).mpr
    intro c v hs
    have hh := PrefixSplitState_items_bound _ _ _ _ _ hs i ⟨PreH12, by omega⟩
    omega

theorem proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3 := by
  unfold splitArrayLargestSum_safety_wit_3
  right
  intro l arr_pre n_pre m_pre res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hm := mid_quot_bounds left right PreH9 PreH1 PreH10
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7 := by
  unfold splitArrayLargestSum_safety_wit_7
  right
  intro l arr_pre n_pre m_pre res right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hm := mid_quot_bounds left right PreH13 PreH5 PreH14
  have hq := quot_half_lt (right-left) (by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1 := by
  unfold splitArrayLargestSum_entail_wit_1
  right
  intro l ans n_pre m_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH9 | omega

theorem proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1 := by
  unfold splitArrayLargestSum_entail_wit_2_1
  right
  intro l n_pre m_pre res_2 right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hm := mid_quot_bounds left right PreH13 PreH5 PreH14
  rcases PreH3 (by omega) with ⟨v, hp, hv⟩
  have hb := minimized_lower_bound l m_pre res_2 v PreH18 hp
  refine Automation.exp_right_rule (CRules := naive_C_Rules) res_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH18 | omega

theorem proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2 := by
  unfold splitArrayLargestSum_entail_wit_2_2
  right
  intro l n_pre m_pre res_2 right left retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hm := mid_quot_bounds left right PreH13 PreH5 PreH14
  have hq := quot_half_lt (right-left) (by omega)
  have hb : left+Z.quot (right-left) 2 < res_2 := by
    by_contra hh
    exact PreH4 PreH19 ⟨res_2, minimized_partition_witness _ _ _ PreH18, by omega⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) res_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH18 | omega

theorem proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure := by
  unfold splitArrayLargestSum_partial_solve_wit_1_pure
  right
  intro l arr_pre n_pre m_pre res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hm := mid_quot_bounds left right PreH19 PreH11 PreH20
  split_pures <;> dump_pre_spatial <;> omega

theorem proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1 := by
  unfold splitArrayLargestSum_return_wit_1
  right
  intro l n_pre m_pre res right left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rw [show left = res by omega]; exact PreH14

end SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_proof_manual
