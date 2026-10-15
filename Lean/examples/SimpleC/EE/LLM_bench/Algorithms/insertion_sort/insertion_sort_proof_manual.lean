import SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_proof_auto
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_goal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
open insertion_sort_lib

theorem proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1 := by
  unfold sortArray_entail_wit_1
  right
  intro numsSize_pre l PreH1 PreH2 PreH3
  cases l with
  | nil => simp [Zlength] at PreH1; omega
  | cons z tail =>
    Exists ([z] : List Int) ([z] : List Int) tail
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Sorting.strict_lowerbound, Int.add_zero, Int.zero_add, Int.sub_add_cancel, Sorting.Znth_boundary, Sorting.Znth_end, replace_Znth_boundary_app_local])
        | (try simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, Int.add_zero, Int.zero_add]; omega)

theorem proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2 := by
  unfold sortArray_entail_wit_2
  right
  intro numsSize_pre l i l0_2 l3 l1_2 l2_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hlen : Zlength l1_2 = Zlength l0_2 := congrArg (fun n : Nat => (n : Int)) PreH10.length_eq
  cases l2_2 with
  | nil => simp only [List.append_nil] at PreH4; have := PreH6; rw [PreH4] at this; omega
  | cons z tail =>
    have hz : Znth (Zlength l1_2) (l0_2 ++ z :: tail) 0 = z := by rw [hlen, Sorting.Znth_boundary]
    Exists l0_2 ([] : List Int) l1_2 tail
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first
        | assumption
        | exact List.Perm.refl _
        | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Sorting.strict_lowerbound, Int.add_zero, Int.zero_add, Int.sub_add_cancel, Sorting.Znth_boundary, Sorting.Znth_end, replace_Znth_boundary_app_local])
        | (try simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, Int.add_zero, Int.zero_add]; omega)

theorem proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3 := by
  unfold sortArray_entail_wit_3
  right
  intro numsSize_pre l j l5_2 l2_2 l3_2 l0_2 i l1_2 key l4_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  obtain ⟨pfx, z, heq⟩ := Sorting.exists_snoc_of_pos l2_2 (by omega)
  subst l2_2
  have hj : j = Zlength pfx := by simp only [Zlength_app, Zlength_cons, Zlength_nil] at PreH15; omega
  have hznth : Znth j l5_2 0 = z := by
    rw [PreH13, hj]
    simpa only [hj, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append] using
      Sorting.Znth_boundary pfx (Znth (j+1) l0_2 key :: (l3_2 ++ l4_2)) z
  have hgt : key < z := by rw [hznth] at PreH1; exact PreH1
  have hbound : strict_lowerbound key (z::l3_2) := ⟨hgt, PreH18⟩
  have harray : replace_Znth (j+1) z (((pfx ++ [z]) ++ Znth (j+1) l0_2 key :: l3_2) ++ l4_2) =
      ((pfx ++ [z]) ++ z :: l3_2) ++ l4_2 := by
    rw [PreH15, replace_Znth_boundary_app_local]
  Exists pfx (z::l3_2) l1_2 l4_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [hj, Int.sub_add_cancel, List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, Sorting.Znth_boundary_d]
    all_goals first
      | assumption
      | (solve | simpa only [hj, Int.sub_add_cancel, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, Sorting.Znth_boundary_d] using harray)
      | exact List.Perm.refl _
      | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Sorting.strict_lowerbound, Int.add_zero, Int.zero_add, Int.sub_add_cancel, Sorting.Znth_boundary, Sorting.Znth_end, replace_Znth_boundary_app_local])
      | (try simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, Int.add_zero, Int.zero_add]; omega)

theorem proof_of_sortArray_entail_wit_4_2 : sortArray_entail_wit_4_2 := by
  unfold sortArray_entail_wit_4_2
  right
  intro numsSize_pre l j l5 l2_2 l3_2 l0_2 i l1_2 key l4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  obtain ⟨pfx, z, heq⟩ := Sorting.exists_snoc_of_pos l2_2 (by omega)
  subst l2_2
  have hj : j = Zlength pfx := by simp only [Zlength_app, Zlength_cons, Zlength_nil] at PreH15; omega
  have hznth : Znth j l5 0 = z := by
    rw [PreH13, hj]
    simpa only [hj, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append] using
      Sorting.Znth_boundary pfx (Znth (j+1) l0_2 key :: (l3_2 ++ l4)) z
  have hz : z ≤ key := by rw [hznth] at PreH1; exact PreH1
  have hinc : increasing (pfx ++ z :: key :: l3_2) :=
    increasing_middle pfx z key l3_2 (by simpa only [PreH12, List.append_assoc, List.singleton_append] using PreH11) hz PreH18
  have hp : Permutation (l1_2 ++ [key]) (((pfx ++ [z]) ++ key :: l3_2)) := by
    apply (PreH10.append_right [key]).trans
    rw [PreH12]
    simpa only [List.append_assoc, List.singleton_append] using
      (List.perm_append_comm (l₁ := l3_2) (l₂ := [key])).append_left (pfx ++ [z])
  have harray : replace_Znth (j+1) key (((pfx ++ [z]) ++ Znth (j+1) l0_2 key :: l3_2) ++ l4) =
      (((pfx ++ [z]) ++ key :: l3_2) ++ l4) := by
    rw [PreH15, replace_Znth_boundary_app_local]
  Exists ((pfx ++ [z]) ++ key :: l3_2) (l1_2 ++ [key]) l4
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | exact List.Perm.refl _
      | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Sorting.strict_lowerbound, Int.add_zero, Int.zero_add, Int.sub_add_cancel, Sorting.Znth_boundary, Sorting.Znth_end, replace_Znth_boundary_app_local])
      | (try simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, Int.add_zero, Int.zero_add]; omega)

theorem proof_of_sortArray_entail_wit_4_1 : sortArray_entail_wit_4_1 := by
  unfold sortArray_entail_wit_4_1
  right
  intro numsSize_pre l j l5 l2_2 l3_2 l0_2 i l1_2 key l4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hj : j+1 = 0 := by omega
  have hn : l2_2 = [] := by
    have : Zlength l2_2 = 0 := by omega
    simpa [Zlength] using this
  subst l2_2
  simp only [List.nil_append] at PreH11
  subst l0_2
  have hinc := increasing_insert key l3_2 PreH10
  rw [upperbound_insert_nil key l3_2 PreH17] at hinc
  have hp : Permutation (l1_2 ++ [key]) (key::l3_2) :=
    (PreH9.append_right [key]).trans (List.perm_append_comm (l₁ := l3_2) (l₂ := [key]))
  Exists (key::l3_2) (l1_2 ++ [key]) l4
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals try simp only [hj, List.nil_append, List.cons_append, replace_Znth, Int.toNat_zero, replace_nth]
    all_goals first
      | assumption
      | exact List.Perm.refl _
      | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Sorting.strict_lowerbound, Int.add_zero, Int.zero_add, Int.sub_add_cancel, Sorting.Znth_boundary, Sorting.Znth_end, replace_Znth_boundary_app_local])
      | (try simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, Int.add_zero, Int.zero_add]; omega)

theorem proof_of_sortArray_return_wit_1 : sortArray_return_wit_1 := by
  unfold sortArray_return_wit_1
  right
  intro numsSize_pre l i l0 l3 l1_2 l2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hn : l2 = [] := by
    have heq : Zlength l2 = 0 := by
      rw [PreH4, Zlength_app] at PreH6
      omega
    simpa [Zlength] using heq
  subst l2
  have hlen : Zlength l1_2 = Zlength l0 := congrArg (fun n : Nat => (n : Int)) PreH10.length_eq
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | exact List.Perm.refl _
      | (solve | simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, Sorting.increasing, Sorting.increasing_aux, Sorting.strict_lowerbound, Int.add_zero, Int.zero_add, Int.sub_add_cancel, Sorting.Znth_boundary, Sorting.Znth_end, replace_Znth_boundary_app_local])
      | (try simp_all only [Zlength_app, Zlength_cons, Zlength_nil, List.nil_append, List.append_nil, List.append_assoc, List.cons_append, Int.add_zero, Int.zero_add]; omega)

end SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_proof_manual
