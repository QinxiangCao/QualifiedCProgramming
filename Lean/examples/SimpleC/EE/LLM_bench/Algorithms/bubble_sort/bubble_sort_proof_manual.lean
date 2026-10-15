import SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open bubble_sort_lib

theorem proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1 := by
  unfold sortArray_entail_wit_1
  right
  intro numsSize_pre l PreH1 PreH2 PreH3 PreH4
  Exists l ([] : List Int)
  have hn : prefix_suffix_sorted l [] := by intro x hx; trivial
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | exact List.Perm.refl _
      | omega
      | (simp only [List.append_nil]; exact List.Perm.refl _)
      | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
      | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

theorem proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2 := by
  unfold sortArray_entail_wit_2
  right
  intro numsSize_pre l i l1_2 l2_2 l3_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hlen : Zlength l = Zlength l3_2 := congrArg (fun n : Nat => (n : Int)) PreH10.length_eq
  cases l1_2 with
  | nil => simp [Zlength] at PreH9
  | cons z tail =>
    Exists ([] : List Int) z tail l2_2
    have hn : prefix_suffix_sorted [] [z] := by intro x hx; contradiction
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
        | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

theorem proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1 := by
  unfold sortArray_entail_wit_3_1
  right
  intro numsSize_pre l j i l1_2 key_2 l2_2 l4_2 l3_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  cases l2_2 with
  | nil => simp [Zlength, Int.ofNat_eq_coe] at PreH14 PreH11; omega
  | cons z tail =>
    have hj : Znth j l3_2 0 = key_2 := by
      rw [PreH5, PreH11]
      simpa only [List.append_assoc, List.cons_append] using Sorting.Znth_boundary l1_2 (z::(tail++l4_2)) key_2
    have hj1 : Znth (j+1) l3_2 0 = z := by
      rw [PreH5, PreH11]
      simpa only [List.append_assoc, List.cons_append] using Sorting.Znth_boundary_next l1_2 (tail++l4_2) key_2 z
    have hz : z < key_2 := by rw [hj, hj1] at PreH1; exact PreH1
    have hsorted := prefix_suffix_sorted_prefix_perm_local _ _ _
      (perm_swap_with_prefix l1_2 [] tail key_2 z) PreH17
    have hsingle := prefix_suffix_sorted_snoc_singleton_local l1_2 z key_2 PreH18 (by omega)
    have hperm : Permutation l ((l1_2 ++ [z]) ++ key_2 :: tail ++ l4_2) := by
      rw [PreH5] at PreH15
      exact PreH15.trans (by simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using
        perm_swap_with_prefix l1_2 [] (tail++l4_2) key_2 z)
    have hswap := Sorting.swap_boundary l1_2 (tail++l4_2) key_2 z
    Exists (l1_2 ++ [z]) key_2 tail l4_2
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp only [List.append_assoc, List.cons_append, List.singleton_append, Sorting.Znth_boundary, Sorting.Znth_boundary_next, hswap])
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
        | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

theorem proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2 := by
  unfold sortArray_entail_wit_3_2
  right
  intro numsSize_pre l j i l1_2 key_2 l2_2 l4_2 l3_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  cases l2_2 with
  | nil => simp [Zlength, Int.ofNat_eq_coe] at PreH14 PreH11; omega
  | cons z tail =>
    have hj : Znth j l3_2 0 = key_2 := by
      rw [PreH5, PreH11]
      simpa only [List.append_assoc, List.cons_append] using Sorting.Znth_boundary l1_2 (z::(tail++l4_2)) key_2
    have hj1 : Znth (j+1) l3_2 0 = z := by
      rw [PreH5, PreH11]
      simpa only [List.append_assoc, List.cons_append] using Sorting.Znth_boundary_next l1_2 (tail++l4_2) key_2 z
    have hz : key_2 ≤ z := by rw [hj, hj1] at PreH1; exact PreH1
    have hsingle := prefix_suffix_sorted_snoc_singleton_local l1_2 key_2 z
      (prefix_suffix_sorted_singleton_le_local l1_2 key_2 z PreH18 hz) hz
    Exists (l1_2 ++ [key_2]) z tail l4_2
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
        | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

theorem proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4 := by
  unfold sortArray_entail_wit_4
  right
  intro numsSize_pre l j i l1_2 key l2_2 l4 l3_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hnil : l2_2 = [] := by
    have := Zlength_nonneg l2_2
    have hn : Zlength l2_2 = 0 := by
      simp only [Zlength_app, Zlength_cons] at PreH13
      omega
    simpa [Zlength] using hn
  subst l2_2
  have hbound : lowerbound key l4 := PreH16 key (by simp)
  have hinc := increasing_cons_local key l4 hbound PreH15
  have hps := prefix_suffix_sorted_extend_suffix_local l1_2 key l4 PreH17
    (fun x hx => PreH16 x (List.mem_append_left _ hx))
  Exists l1_2 (key::l4)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | exact List.Perm.refl _
      | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
      | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

theorem proof_of_sortArray_return_wit_1 : sortArray_return_wit_1 := by
  unfold sortArray_return_wit_1
  right
  intro numsSize_pre l i l1_2 l2 l3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hlen := congrArg (fun n : Nat => (n : Int)) PreH10.length_eq
  have hlen1 : Zlength l1_2 = 1 := by
    rw [PreH4] at hlen
    simp only [List.length_append, Int.natCast_add] at hlen
    change Zlength l = Zlength l1_2 + Zlength l2 at hlen
    omega
  cases l1_2 with
  | nil => simp [Zlength] at hlen1
  | cons z tail =>
    have hn : tail = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [Zlength, List.length_cons, Int.ofNat_eq_coe] at hlen1
      omega
    subst tail
    have hinc := increasing_cons_local z l2 (PreH12 z (by simp)) PreH11
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
        | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

theorem proof_of_sortArray_return_wit_2 : sortArray_return_wit_2 := by
  unfold sortArray_return_wit_2
  right
  intro numsSize_pre l PreH1 PreH2 PreH3 PreH4
  have hn : Zlength l = 1 := by omega
  cases l with
  | nil => simp [Zlength] at hn
  | cons z tail =>
    have ht : tail = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [Zlength, List.length_cons, Int.ofNat_eq_coe] at hn
      omega
    subst tail
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Int.add_zero, Int.zero_add])
        | (simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]; omega)

end SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_proof_manual
