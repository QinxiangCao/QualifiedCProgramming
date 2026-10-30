import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_proof_auto
import AUXLib.Arithmetic
import ListLib.General.Length
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open selection_sort_lib

private theorem minimum_append_smaller (xs : List Int) (a b : Int)
    (hm : selection_minimum xs b) (ha : a ≤ b) : selection_minimum (xs ++ [a]) a := by
  rcases hm with ⟨x, ⟨hx, hb⟩, he⟩
  change x = b at he
  refine ⟨a, ⟨by simp, ?_⟩, rfl⟩
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · have hxy := hb y hy
    change x ≤ y at hxy
    rw [he] at hxy
    exact ha.trans hxy
  · have heq := List.mem_singleton.mp hy
    exact heq.symm.le

private theorem minimum_append_larger (xs : List Int) (a b : Int)
    (hm : selection_minimum xs b) (ha : b ≤ a) : selection_minimum (xs ++ [a]) b := by
  rcases hm with ⟨x, ⟨hx, hb⟩, he⟩
  change x = b at he
  refine ⟨x, ⟨List.mem_append_left _ hx, ?_⟩, he⟩
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hb y hy
  · have heq := List.mem_singleton.mp hy
    change x ≤ y
    rw [he, heq]
    exact ha

private theorem selection_minimum_sublist_bound (l : List Int) (lo hi v k : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (hm : selection_minimum (sublist lo hi l) v) (hk : lo ≤ k ∧ k < hi) :
    v ≤ Znth k l 0 := by
  rcases hm with ⟨x, ⟨hx, hb⟩, he⟩
  have hlen : Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l hlo hhi
  have hr : 0 ≤ k-lo ∧ k-lo < Zlength (sublist lo hi l) := by rw [hlen]; omega
  have hin : (k-lo).toNat < (sublist lo hi l).length := by
    change 0 ≤ k-lo ∧ k-lo < Int.ofNat ((sublist lo hi l).length) at hr
    exact (Int.toNat_lt hr.1).mpr hr.2
  have hmem := List.getElem_mem (l := sublist lo hi l) hin
  have hval := hb _ hmem
  have hv : v ≤ Znth (k-lo) (sublist lo hi l) 0 := by
    simpa only [he, Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using hval
  rw [Znth_sublist 0 lo (k-lo) hi l hlo.1 (by omega)] at hv
  simpa only [Int.sub_add_cancel] using hv

private theorem swapped_lookup (l : List Int) (i m k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hm : 0 ≤ m ∧ m < Zlength l)
    (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth m (Znth i l 0) (replace_Znth i (Znth m l 0) l)) 0 =
      if k = m then Znth i l 0 else if k = i then Znth m l 0 else Znth k l 0 := by
  by_cases hkm : k = m
  · subst k
    rw [if_pos rfl]
    apply Znth_replace_Znth_Same
    simpa only [Zlength_replace_Znth] using hm
  · rw [if_neg hkm, Znth_replace_Znth_Diff 0 _ m k _
      (by simpa only [Zlength_replace_Znth] using hm)
      (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm hkm)]
    by_cases hki : k = i
    · subst k
      rw [if_pos rfl]
      exact Znth_replace_Znth_Same 0 l i _ hi
    · rw [if_neg hki]
      exact Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm hki)


private theorem selection_minimum_sublist_intro (l : List Int) (lo hi index : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (hiindex : lo ≤ index ∧ index < hi)
    (hbound : ∀ k, (lo ≤ k ∧ k < hi) → Znth index l 0 ≤ Znth k l 0) :
    selection_minimum (sublist lo hi l) (Znth index l 0) := by
  have hlen : Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l hlo hhi
  have hr : 0 ≤ index-lo ∧ index-lo < Zlength (sublist lo hi l) := by rw [hlen]; omega
  have hin : (index-lo).toNat < (sublist lo hi l).length := by
    change 0 ≤ index-lo ∧ index-lo < Int.ofNat ((sublist lo hi l).length) at hr
    exact (Int.toNat_lt hr.1).mpr hr.2
  have hmem : Znth (index-lo) (sublist lo hi l) 0 ∈ sublist lo hi l := by
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using (List.getElem_mem (l := sublist lo hi l) hin)
  rw [Znth_sublist 0 lo (index-lo) hi l hlo.1 (by omega)] at hmem
  simp only [Int.sub_add_cancel] at hmem
  refine ⟨Znth index l 0, ⟨hmem, ?_⟩, rfl⟩
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨idx,hidx,he⟩
  have hr : 0 ≤ (idx : Int) ∧ (idx : Int) < hi-lo := by
    have hc : (idx : Int) < Zlength (sublist lo hi l) := by
      change (idx : Int) < Int.ofNat ((sublist lo hi l).length)
      exact Int.ofNat_lt.mpr hidx
    rw [hlen] at hc
    omega
  have hv := hbound ((idx : Int)+lo) (by omega)
  have heq : Znth ((idx : Int)+lo) l 0 = x := by
    rw [← Znth_sublist 0 lo (idx : Int) hi l hlo.1 hr]
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some] using he
  simpa only [heq] using hv

theorem proof_of_sortArray_entail_wit_1_split_goal_1 : sortArray_entail_wit_1_split_goal_1 := by
  unfold sortArray_entail_wit_1_split_goal_1
  intro l numsSize_pre PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1_split_goal_2 : sortArray_entail_wit_1_split_goal_2 := by
  unfold sortArray_entail_wit_1_split_goal_2
  intro l numsSize_pre PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1_split_goal_3 : sortArray_entail_wit_1_split_goal_3 := by
  unfold sortArray_entail_wit_1_split_goal_3
  intro l numsSize_pre PreH1 PreH2 PreH3
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1 := by
  unfold sortArray_entail_wit_1
  right
  intro l numsSize_pre PreH1 PreH2 PreH3
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_1_split_goal_1 l numsSize_pre) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_1_split_goal_3 l numsSize_pre) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_2_split_goal_1 : sortArray_entail_wit_2_split_goal_1 := by
  unfold sortArray_entail_wit_2_split_goal_1
  intro l numsSize_pre a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [sublist_single 0 i_2 a_2 (by omega)]
  refine ⟨Znth i_2 a_2 0, ⟨by simp, ?_⟩, rfl⟩
  intro x hx
  exact (List.mem_singleton.mp hx).symm.le

theorem proof_of_sortArray_entail_wit_2_split_goal_2 : sortArray_entail_wit_2_split_goal_2 := by
  unfold sortArray_entail_wit_2_split_goal_2
  intro l numsSize_pre a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    first | omega | (solve | simp [Sorting.increasing, sublist]) | grind

theorem proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2 := by
  unfold sortArray_entail_wit_2
  right
  intro l numsSize_pre a_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_2_split_goal_1 l numsSize_pre a_2 i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_2_split_goal_2 l numsSize_pre a_2 i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_3_1_split_goal_1 : sortArray_entail_wit_3_1_split_goal_1 := by
  unfold sortArray_entail_wit_3_1_split_goal_1
  intro l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  simp only [Zlength_replace_Znth] at PreH1
  apply selection_minimum_sublist_intro _ i_2 (j_2+1) i_2 (by omega) (by simpa only [Zlength_replace_Znth] using (show j_2+1 ≤ Zlength a_2 by omega)) (by omega)
  intro k hk
  rw [swapped_lookup a_2 i_2 j_2 i_2 (by omega) (by omega) (by omega), if_neg (by omega), if_pos rfl,
    swapped_lookup a_2 i_2 j_2 k (by omega) (by omega) (by omega)]
  split_ifs with hkj hki
  · omega
  · exact Int.le_refl _
  · have hb := selection_minimum_sublist_bound a_2 i_2 j_2 (Znth i_2 a_2 0) k (by omega) (by omega) PreH13 (by omega)
    omega

theorem proof_of_sortArray_entail_wit_3_1_split_goal_2 : sortArray_entail_wit_3_1_split_goal_2 := by
  unfold sortArray_entail_wit_3_1_split_goal_2
  intro l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    have hlen : Zlength a_2 = numsSize_pre := by simpa only [Zlength_replace_Znth] using PreH1
    apply increasing_sublist_intro <;> try omega
    intro p q hr
    rw [Znth_replace_Znth_Diff, Znth_replace_Znth_Diff, Znth_replace_Znth_Diff, Znth_replace_Znth_Diff]
    · exact increasing_sublist_elim a_2 0 i_2 p q (by omega) (by omega) PreH11 (by omega)
    all_goals try simp only [Zlength_replace_Znth]
    all_goals omega

theorem proof_of_sortArray_entail_wit_3_1_split_goal_3 : sortArray_entail_wit_3_1_split_goal_3 := by
  unfold sortArray_entail_wit_3_1_split_goal_3
  intro l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    have hlen : Zlength a_2 = numsSize_pre := by simpa only [Zlength_replace_Znth] using PreH1
    exact PreH10.trans (permutation_swap_Znth_lt a_2 i_2 j_2 0 (by omega))

theorem proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1 := by
  unfold sortArray_entail_wit_3_1
  right
  intro l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | exact proof_of_sortArray_entail_wit_3_1_split_goal_1 l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sortArray_entail_wit_3_1_split_goal_2 l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_sortArray_entail_wit_3_1_split_goal_3 l numsSize_pre a_2 j_2 i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_sortArray_entail_wit_4_split_goal_1 : sortArray_entail_wit_4_split_goal_1 := by
  unfold sortArray_entail_wit_4_split_goal_1
  intro l numsSize_pre a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have PreH12 := selection_minimum_sublist_bound a_2 i_2 j (Znth i_2 a_2 0) (hlo := by omega) (hhi := by omega) (hm := PreH12)
  all_goals
    intro p q h
    by_cases hp : p < i_2
    · exact PreH11 p q (by omega)
    · have heq : p = i_2 := by omega
      subst p
      exact PreH12 q (by omega)

theorem proof_of_sortArray_entail_wit_4_split_goal_2 : sortArray_entail_wit_4_split_goal_2 := by
  unfold sortArray_entail_wit_4_split_goal_2
  intro l numsSize_pre a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    apply increasing_sublist_intro <;> try omega
    intro p q hr
    by_cases hq : q = i_2
    · subst q
      by_cases hp : p = i_2
      · subst p; omega
      · exact PreH11 p i_2 (by omega)
    · exact increasing_sublist_elim a_2 0 i_2 p q (by omega) (by omega) PreH10 (by omega)

theorem proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4 := by
  unfold sortArray_entail_wit_4
  right
  intro l numsSize_pre a_2 j i_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_entail_wit_4_split_goal_1 l numsSize_pre a_2 j i_2) <;> assumption)
      | (apply (proof_of_sortArray_entail_wit_4_split_goal_2 l numsSize_pre a_2 j i_2) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_return_wit_1_split_goal_1 : sortArray_return_wit_1_split_goal_1 := by
  unfold sortArray_return_wit_1_split_goal_1
  intro l numsSize_pre a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    have hi : i = numsSize_pre := by omega
    subst i
    rw [← PreH1] at PreH8
    simpa [sublist, Zlength] using PreH8

theorem proof_of_sortArray_return_wit_1 : sortArray_return_wit_1 := by
  unfold sortArray_return_wit_1
  right
  intro l numsSize_pre a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  all_goals
    aggressive_pre_process
    all_goals try (apply dump_spatial_left)
    all_goals first
      | (apply (proof_of_sortArray_return_wit_1_split_goal_1 l numsSize_pre a i) <;> assumption)
      | omega
      | int_auto

theorem proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2 := by
  unfold sortArray_entail_wit_3_2
  right
  intro l n current j i hlen hread hj hn hnmax hi hin hij hjn hperm hsorted hcross hmin
  have hnew : selection_minimum (sublist i (j+1) current) (Znth i current 0) := by
    rw [sublist_split i (j+1) j current (by omega) (by omega), sublist_single 0 j current (by omega)]
    exact minimum_append_larger _ _ _ hmin hread
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact hnew


end SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_proof_manual
