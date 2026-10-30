import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_goal
import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open discretize_goal discretize_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Previously proved auxiliary statements retained for proof audits.
private noncomputable abbrev intArray := naive_C_Rules.IntArray
theorem proof_of_partition_entail_wit_1 : partition_entail_wit_1 := by
  unfold partition_entail_wit_1
  left
  intro l arr_pre n_pre low_pre high_pre NewPreH1 NewPreH2 NewPreH3
  have PreH1 : ((0 : Int) <= low_pre) := NewPreH1
  have PreH2 : (low_pre <= high_pre) := NewPreH2
  Exists l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact partition_scan_inv_init__partition_scan l low_pre high_pre PreH1 PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1 := by
  unfold partition_entail_wit_2_1
  left
  intro l arr_pre n_pre low_pre high_pre l1_2 j i pivot NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : ((Znth j l1_2 (0 : Int)) <= pivot) := NewPreH1
  have PreH2 : (j < high_pre) := NewPreH2
  have PreH4 : ((0 : Int) <= low_pre) := NewPreH4
  have PreH5 : (low_pre <= high_pre) := NewPreH5
  have PreH7 : ((low_pre - 1) <= i) := NewPreH7
  have PreH8 : (i < j) := NewPreH8
  have PreH9 : (j <= high_pre) := NewPreH9
  have PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j) := NewPreH10
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  Exists (replace_Znth j (Znth (i+1) l1_2 0) (replace_Znth (i+1) (Znth j l1_2 0) l1_2))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact partition_scan_inv_step_le__partition_scan l l1_2 low_pre high_pre pivot i j PreH4 PreH5 (by omega) PreH1 PreH2 PreH7 PreH8 PreH9 PreH10
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2 := by
  unfold partition_entail_wit_2_2
  left
  intro l arr_pre n_pre low_pre high_pre l1_2 j i pivot NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : ((Znth j l1_2 (0 : Int)) > pivot) := NewPreH1
  have PreH2 : (j < high_pre) := NewPreH2
  have PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j) := NewPreH10
  Exists l1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact partition_scan_inv_step_gt__partition_scan l l1_2 low_pre high_pre pivot i j PreH1 PreH2 PreH10
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_partition_return_wit_1 : partition_return_wit_1 := by
  unfold partition_return_wit_1
  left
  intro l arr_pre n_pre low_pre high_pre l1_2 j i pivot NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  have PreH1 : (j >= high_pre) := NewPreH1
  have PreH3 : ((0 : Int) <= low_pre) := NewPreH3
  have PreH4 : (low_pre <= high_pre) := NewPreH4
  have PreH6 : ((low_pre - 1) <= i) := NewPreH6
  have PreH7 : (i < j) := NewPreH7
  have PreH8 : (j <= high_pre) := NewPreH8
  have PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j) := NewPreH9
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  Exists (replace_Znth high_pre (Znth (i+1) l1_2 0) (replace_Znth (i+1) (Znth high_pre l1_2 0) l1_2))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact partition_scan_inv_final_permutation__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | exact partition_scan_inv_final_same_outside__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | exact partition_scan_inv_final_swap_partitioned_at__partition_scan l l1_2 low_pre high_pre pivot i j PreH3 PreH4 PreH6 (by omega) PreH1 PreH7 PreH8 PreH9
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1 := by
  unfold quicksort_range_return_wit_1
  left
  intro l arr_pre n_pre left_pre right_pre l1_2 retval l1_3 l1_4 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18
  have PreH1 : (permutation l1_3 l1_4) := NewPreH1
  have PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre) := NewPreH2
  have PreH3 : (sorted_range l1_4 (retval + 1) right_pre) := NewPreH3
  have PreH5 : (permutation l1_2 l1_3) := NewPreH5
  have PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1)) := NewPreH6
  have PreH7 : (sorted_range l1_3 left_pre (retval - 1)) := NewPreH7
  have PreH9 : (left_pre <= retval) := NewPreH9
  have PreH10 : (retval <= right_pre) := NewPreH10
  have PreH11 : (permutation l l1_2) := NewPreH11
  have PreH12 : (same_outside_range l l1_2 left_pre right_pre) := NewPreH12
  have PreH13 : (partitioned_at l1_2 left_pre right_pre retval) := NewPreH13
  have PreH16 : ((0 : Int) <= left_pre) := NewPreH16
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_4)
  Intros_p hlen
  have hlen34 := PreH2.1
  have hlen23 := PreH6.1
  have hp3 := partitioned_at_preserved_by_left__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH5 PreH16 PreH6 (by omega) PreH13
  have hp4 := partitioned_at_preserved_by_right__quicksort_range l1_3 l1_4 left_pre right_pre retval PreH1 PreH16 PreH2 (by omega) hp3
  have hleft : sorted_range l1_4 left_pre (retval-1) := by
    apply sorted_range_ext__quicksort_range l1_3 l1_4 left_pre (retval-1) PreH16 (by omega) hlen34 _ PreH7
    intro k hk
    exact PreH2.2 k (by omega) (Or.inl (by omega))
  have hs := sorted_range_from_both l1_4 left_pre right_pre retval ⟨PreH9,PreH10⟩ hp4 hleft PreH3
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 left_pre (retval-1) left_pre right_pre (by omega) (by omega) PreH6
  have hsame34 := same_outside_range_weaken__quicksort_range l1_3 l1_4 (retval+1) right_pre left_pre right_pre (by omega) (by omega) PreH2
  have hsame := same_outside_range_trans__quicksort_range l l1_3 l1_4 left_pre right_pre
    (same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH12 hsame23) hsame34
  Exists l1_4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact PreH11.trans (PreH5.trans PreH1)
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2 := by
  unfold quicksort_range_return_wit_2
  left
  intro l arr_pre n_pre left_pre right_pre l1_2 retval l1_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (permutation l1_2 l1_3) := NewPreH1
  have PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre) := NewPreH2
  have PreH3 : (sorted_range l1_3 (retval + 1) right_pre) := NewPreH3
  have PreH5 : (retval <= left_pre) := NewPreH5
  have PreH8 : (permutation l l1_2) := NewPreH8
  have PreH9 : (same_outside_range l l1_2 left_pre right_pre) := NewPreH9
  have PreH10 : (partitioned_at l1_2 left_pre right_pre retval) := NewPreH10
  have PreH13 : ((0 : Int) <= left_pre) := NewPreH13
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_3)
  Intros_p hlen
  have hlen23 := PreH2.1
  have hp := partitioned_at_preserved_by_right__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH1 PreH13 PreH2 (by omega) PreH10
  have hs := sorted_range_from_right l1_3 left_pre right_pre retval PreH5 hp PreH3
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 (retval+1) right_pre left_pre right_pre (by omega) (by omega) PreH2
  have hsame := same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH9 hsame23
  Exists l1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact PreH8.trans PreH1
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3 := by
  unfold quicksort_range_return_wit_3
  left
  intro l arr_pre n_pre left_pre right_pre l1_2 retval l1_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (retval >= right_pre) := NewPreH1
  have PreH2 : (permutation l1_2 l1_3) := NewPreH2
  have PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1)) := NewPreH3
  have PreH4 : (sorted_range l1_3 left_pre (retval - 1)) := NewPreH4
  have PreH8 : (permutation l l1_2) := NewPreH8
  have PreH9 : (same_outside_range l l1_2 left_pre right_pre) := NewPreH9
  have PreH10 : (partitioned_at l1_2 left_pre right_pre retval) := NewPreH10
  have PreH13 : ((0 : Int) <= left_pre) := NewPreH13
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_3)
  Intros_p hlen
  have hlen23 := PreH3.1
  have hp := partitioned_at_preserved_by_left__quicksort_range l1_2 l1_3 left_pre right_pre retval PreH2 PreH13 PreH3 (by omega) PreH10
  have hs := sorted_range_from_left l1_3 left_pre right_pre retval PreH1 hp PreH4
  have hsame23 := same_outside_range_weaken__quicksort_range l1_2 l1_3 left_pre (retval-1) left_pre right_pre (by omega) (by omega) PreH3
  have hsame := same_outside_range_trans__quicksort_range l l1_2 l1_3 left_pre right_pre PreH9 hsame23
  Exists l1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact PreH8.trans PreH2
    | exact hsame
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4 := by
  unfold quicksort_range_return_wit_4
  left
  intro l arr_pre n_pre left_pre right_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH1 : (left_pre >= right_pre) := NewPreH1
  Exists l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact List.Perm.refl l
    | exact same_outside_range_refl__quicksort_range l left_pre right_pre
    | exact sorted_range_base l left_pre right_pre PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1 := by
  unfold int_array_quicksort_return_wit_1
  left
  intro l arr_pre n_pre l1_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH3 : (sorted_range l1_2 (0 : Int) (n_pre - 1)) := NewPreH3
  prop_apply (naive_C_Rules.IntArray.full_Zlength arr_pre n_pre l1_2)
  Intros_p hlen
  have hs := sorted_range_implies_increasing__quicksort_range l1_2 (by rw [hlen]; exact PreH3)
  Exists l1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_1 : discretize_entail_wit_1 := by
  unfold discretize_entail_wit_1
  left
  intro src_l src_pre n_pre dest_map_pre NewPreH1 NewPreH2
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg dest_map_pre n_pre)
  have he : sublist 0 0 src_l=[] := by simp [sublist]
  rw [he]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.full_empty dest_map_pre 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_2 : discretize_entail_wit_2 := by
  unfold discretize_entail_wit_2
  left
  intro src_l src_pre n_pre dest_map_pre i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  prop_apply (intArray.full_Zlength src_pre n_pre src_l)
  Intros_p source_length
  rw [sublist_split 0 (i+1) i src_l (by omega) (by omega),sublist_single 0 i src_l (by omega)]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_3 : discretize_entail_wit_3 := by
  unfold discretize_entail_wit_3
  left
  intro src_l src_pre n_pre dest_map_pre i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  prop_apply (intArray.full_Zlength src_pre n_pre src_l)
  Intros_p PreH2
  have hi : i=n_pre := by omega
  subst i
  rw [sublist_self src_l n_pre PreH2.symm]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (naive_C_Rules.IntArray.undef_seg_empty dest_map_pre n_pre)).1)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_4 : discretize_entail_wit_4 := by
  unfold discretize_entail_wit_4
  left
  intro src_l src_pre n_pre dest_map_pre l1 NewPreH1 NewPreH2 NewPreH3 NewPreH4
  have PreH1 : (permutation src_l l1) := NewPreH1
  have PreH2 : (increasing l1) := NewPreH2
  prop_apply (intArray.full_Zlength src_pre n_pre src_l)
  Intros_p PreH3
  have PreH4 : (1 <= n_pre) := NewPreH3
  Exists l1
  Exists l1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact dedup_scan_inv_init__discretize_dedup src_l l1 n_pre PreH1 PreH2 PreH3 PreH4
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_5_1 : discretize_entail_wit_5_1 := by
  unfold discretize_entail_wit_5_1
  left
  intro src_l src_pre n_pre dest_map_pre sorted_l_2 cur_l_2 fast slow NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : ((Znth fast cur_l_2 (0 : Int)) ≠ (Znth slow cur_l_2 (0 : Int))) := NewPreH1
  have PreH10 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast) := NewPreH8
  prop_apply (intArray.full_Zlength src_pre n_pre src_l)
  Intros_p source_length
  have hlen := PreH10.1
  Exists sorted_l_2
  Exists (replace_Znth (slow+1) (Znth fast cur_l_2 0) cur_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact dedup_scan_inv_step_new__discretize_dedup src_l sorted_l_2 cur_l_2 slow fast PreH10 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_entail_wit_5_2 : discretize_entail_wit_5_2 := by
  unfold discretize_entail_wit_5_2
  left
  intro src_l src_pre n_pre dest_map_pre sorted_l_2 cur_l_2 fast slow NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : ((Znth fast cur_l_2 (0 : Int)) = (Znth slow cur_l_2 (0 : Int))) := NewPreH1
  have PreH10 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast) := NewPreH8
  prop_apply (intArray.full_Zlength src_pre n_pre src_l)
  Intros_p source_length
  have hlen := PreH10.1
  Exists sorted_l_2
  Exists cur_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact dedup_scan_inv_step_duplicate__discretize_dedup src_l sorted_l_2 cur_l_2 slow fast PreH10 (by omega) PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_safety_wit_4 : query_forward_safety_wit_4 := by
  unfold query_forward_safety_wit_4
  left
  intro map_l map_pre map_size_pre target_pre high low NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7
  have PreH1 : (low <= high) := NewPreH1
  have hm := midpoint_between_bounds__query_forward_search low high PreH1
  split_pures <;> dump_pre_spatial
  · change _≤2147483647
    omega
  · change (-2147483648:Int)≤_
    omega

theorem proof_of_query_forward_entail_wit_1 : query_forward_entail_wit_1 := by
  unfold query_forward_entail_wit_1
  left
  intro map_l map_pre map_size_pre target_pre NewPreH1 NewPreH2
  prop_apply (intArray.full_Zlength map_pre map_size_pre map_l)
  Intros_p map_length
  have hn := Zlength_nonneg map_l
  have PreH2 : 0 ≤ map_size_pre := by omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact query_forward_search_inv_init__query_forward_search map_l map_size_pre target_pre PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_2 : query_forward_entail_wit_2 := by
  unfold query_forward_entail_wit_2
  left
  intro map_l map_pre map_size_pre target_pre high low NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7
  have PreH1 : (low <= high) := NewPreH1
  have hm := midpoint_between_bounds__query_forward_search low high PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_3_1 : query_forward_entail_wit_3_1 := by
  unfold query_forward_entail_wit_3_1
  left
  intro map_l map_pre map_size_pre target_pre low mid high NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  have PreH1 : ((Znth mid map_l (0 : Int)) < target_pre) := NewPreH1
  prop_apply (intArray.full_Zlength map_pre map_size_pre map_l)
  Intros_p PreH3
  have PreH6 : (strict_increasing map_l) := NewPreH4
  have PreH8 : (low <= mid) := NewPreH6
  have PreH9 : (mid <= high) := NewPreH7
  have PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high) := NewPreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact query_forward_search_inv_step_right__query_forward_search map_l map_size_pre target_pre low mid high PreH3 PreH6 PreH11 PreH8 PreH9 PreH1
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_entail_wit_3_2 : query_forward_entail_wit_3_2 := by
  unfold query_forward_entail_wit_3_2
  left
  intro map_l map_pre map_size_pre target_pre low mid high NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  have PreH1 : ((Znth mid map_l (0 : Int)) >= target_pre) := NewPreH1
  have PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre) := NewPreH2
  prop_apply (intArray.full_Zlength map_pre map_size_pre map_l)
  Intros_p PreH3
  have PreH6 : (strict_increasing map_l) := NewPreH4
  have PreH8 : (low <= mid) := NewPreH6
  have PreH9 : (mid <= high) := NewPreH7
  have PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high) := NewPreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact query_forward_search_inv_step_left__query_forward_search map_l map_size_pre target_pre low mid high PreH3 PreH6 PreH11 PreH8 PreH9 PreH1 PreH2
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_query_forward_return_wit_2 : query_forward_return_wit_2 := by
  unfold query_forward_return_wit_2
  left
  intro map_l map_pre map_size_pre target_pre low mid high NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : ((Znth mid map_l (0 : Int)) = target_pre) := NewPreH1
  prop_apply (intArray.full_Zlength map_pre map_size_pre map_l)
  Intros_p PreH2
  have PreH5 : (strict_increasing map_l) := NewPreH3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact Or.inl ⟨⟨by omega, by omega⟩, PreH1⟩
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_discretize_return_wit_1 : discretize_return_wit_1 := by
  unfold discretize_return_wit_1
  left
  intro src_l src_pre n_pre dest_map_pre sorted_l cur_l fast slow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  prop_apply (intArray.full_Zlength src_pre n_pre src_l)
  Intros_p source_length
  have hf : fast = n_pre := by omega
  rw [hf] at PreH7
  have hlegacy := dedup_scan_inv_to_discretize_result__discretize_dedup src_l sorted_l cur_l slow n_pre PreH7 source_length (by omega)
  rcases hlegacy with ⟨hs, hc, hn, hr, hstrict, hvalues, _⟩
  have hresult : discretize_result src_l cur_l (slow+1) := by
    refine ⟨⟨by omega, by omega⟩, hstrict, ?_⟩
    intro x
    have hh := hvalues x
    rw [sublist_self src_l n_pre hs.symm] at hh
    exact hh
  Exists cur_l
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hresult

theorem proof_of_query_forward_safety_wit_2 : query_forward_safety_wit_2 := by
  unfold query_forward_safety_wit_2
  left
  intro map_l map_pre map_size_pre target_pre PreH1 PreH2
  prop_apply (intArray.full_Zlength map_pre map_size_pre map_l)
  Intros_p map_length
  have hn := Zlength_nonneg map_l
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega

theorem proof_of_query_forward_return_wit_1 : query_forward_return_wit_1 := by
  unfold query_forward_return_wit_1
  left
  intro map_l map_pre map_size_pre target_pre high low PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  prop_apply (intArray.full_Zlength map_pre map_size_pre map_l)
  Intros_p map_length
  have hlegacy := query_forward_result_not_found__query_forward_search map_l map_size_pre target_pre low high PreH7 PreH1 PreH5
  have hnone : ∀ j, 0 ≤ j ∧ j < map_size_pre → Znth j map_l 0 ≠ target_pre := by
    rcases hlegacy with ⟨⟨j, hj, _, he⟩, _⟩ | ⟨hn, _⟩
    · omega
    · exact hn
  have hresult : query_forward_result map_l target_pre (-1) := by
    right
    refine ⟨rfl, ?_⟩
    intro hin
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hin
    have hr : 0 ≤ (k : Int) ∧ (k : Int) < map_size_pre := by
      change k < map_l.length at hk
      change (map_l.length : Int) = map_size_pre at map_length
      omega
    apply hnone k hr
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, Option.getD_some] using he
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hresult

end SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_proof_manual
