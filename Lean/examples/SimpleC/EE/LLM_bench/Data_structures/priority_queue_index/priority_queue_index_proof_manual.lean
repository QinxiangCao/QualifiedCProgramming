import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_goal
import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_proof_auto
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open priority_queue_index_goal priority_queue_index_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_push_entail_wit_1 : push_entail_wit_1 := by
  unfold push_entail_wit_1
  left
  intro n_pre data_pre key_pre S_before PreH1 PreH2
  unfold store_heap
  Intros key_base data_base
  have hr : heap_representation S_before key_base data_base n_pre := by assumption
  simp only [heap_tail,if_pos PreH2,heap_spare]
  Exists key_base data_base
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_push_entail_wit_2 : push_entail_wit_2 := by
  unfold push_entail_wit_2
  left
  intro key_x_pre data_x_pre n_pre data_pre key_pre S_before key_base data_base PreH1 PreH2 PreH3
  have hl := push_appended_loop_state__push_initialization S_before key_base data_base n_pre data_x_pre key_x_pre PreH3
  have hs := push_appended_source__push_initialization S_before key_base data_base n_pre data_x_pre key_x_pre PreH3
  Exists (key_base ++ [key_x_pre]) (data_base ++ [data_x_pre]) (key_base ++ [key_x_pre]) (data_base ++ [data_x_pre])
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_push_entail_wit_3 : push_entail_wit_3 := by
  unfold push_entail_wit_3
  left
  intro key_x_pre data_x_pre n_pre data_pre key_pre S_before key_current_2 data_current_2 key_written_2 data_written_2 child PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  obtain ⟨h0,h1,h2⟩ := heap_parent_positive_bounds__push_sift_up child n_pre PreH1 PreH5
  unfold heap_parent at h0 h1 h2
  Exists key_current_2 data_current_2 key_written_2 data_written_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_push_entail_wit_4_split_goal_1 : push_entail_wit_4_split_goal_1 := by
  unfold push_entail_wit_4_split_goal_1
  intro key_x_pre data_x_pre n_pre S_before key_written_2 data_written_2 key_current_2 data_current_2 child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact push_break_establishes_result__push_sift_up S_before key_written_2 data_written_2 key_current_2 data_current_2 n_pre child parent data_x_pre key_x_pre PreH10 PreH11 PreH9 PreH1

theorem proof_of_push_entail_wit_4 : push_entail_wit_4 := by
  unfold push_entail_wit_4
  right
  intro key_x_pre data_x_pre n_pre S_before key_written_2 data_written_2 key_current_2 data_current_2 child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have h := push_break_establishes_result__push_sift_up S_before key_written_2 data_written_2 key_current_2 data_current_2 n_pre child parent data_x_pre key_x_pre PreH10 PreH11 PreH9 PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_push_entail_wit_5 : push_entail_wit_5 := by
  unfold push_entail_wit_5
  left
  intro key_x_pre data_x_pre n_pre data_pre key_pre S_before key_written_2 data_written_2 key_current_2 data_current_2 child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  obtain ⟨hk,hd,hl⟩ := push_swap_advances_loop__push_sift_up key_written_2 data_written_2 key_current_2 data_current_2 n_pre child parent data_x_pre key_x_pre PreH11 PreH4 PreH9 PreH1
  Exists (replace_Znth child (Znth parent key_current_2 0)       (replace_Znth parent (Znth child key_current_2 0) key_current_2)) (replace_Znth child (Znth parent data_current_2 0)       (replace_Znth parent (Znth child data_current_2 0) data_current_2)) key_written_2 data_written_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_push_return_wit_1_split_goal_spatial : push_return_wit_1_split_goal_spatial := by
  unfold push_return_wit_1_split_goal_spatial
  intro key_x_pre data_x_pre n_pre data_pre key_pre S_before key_current data_current key_written data_written child PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hz : child = 0 := by omega
  have hresult := push_zero_exit_result__push_finalization S_before key_written data_written key_current data_current n_pre data_x_pre key_x_pre PreH6 (by simpa only [hz] using PreH7)
  have hr := push_result_representation__push_finalization S_before key_current data_current n_pre data_x_pre key_x_pre (by assumption) hresult
  sep_apply (concrete_arrays_to_store_heap__build_finalization key_pre data_pre _ _ _ (n_pre+1) (by omega) hr)
  cancel

theorem proof_of_push_return_wit_1 : push_return_wit_1 := by
  unfold push_return_wit_1
  right
  exact proof_of_push_return_wit_1_split_goal_spatial

theorem proof_of_push_return_wit_2_split_goal_spatial : push_return_wit_2_split_goal_spatial := by
  unfold push_return_wit_2_split_goal_spatial
  intro key_x_pre data_x_pre n_pre data_pre key_pre S_before key_written data_written key_current data_current child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hr := push_result_representation__push_finalization S_before key_current data_current n_pre data_x_pre key_x_pre (by assumption) (by assumption)
  sep_apply (concrete_arrays_to_store_heap__build_finalization key_pre data_pre _ _ _ (n_pre+1) (by omega) hr)
  cancel

theorem proof_of_push_return_wit_2 : push_return_wit_2 := by
  unfold push_return_wit_2
  right
  exact proof_of_push_return_wit_2_split_goal_spatial

theorem proof_of_build_entail_wit_1 : build_entail_wit_1 := by
  unfold build_entail_wit_1
  intro n_pre data_pre key_pre data_input key_input PreH1 PreH2 PreH3 PreH4
  by_cases hz : n_pre = 0
  · Left
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first | assumption | trivial | omega | int_auto
  · Right
    have hn : 1 ≤ n_pre := by omega
    obtain ⟨hp,hr⟩ := build_initial_prefix__build_progress key_input data_input n_pre PreH3 PreH4 hn
    sep_apply (intArray.full_split_to_seg key_pre 1 n_pre key_input (by omega))
    sep_apply (intArray.full_split_to_seg data_pre 1 n_pre data_input (by omega))
    sep_apply (intArray.seg_to_full key_pre 0 1 (sublist 0 1 key_input))
    sep_apply (intArray.seg_to_full data_pre 0 1 (sublist 0 1 data_input))
    simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
    Exists (sublist 0 1 key_input) (sublist 0 1 data_input) (list_to_multiset [heap_item (Znth 0 key_input 0) (Znth 0 data_input 0)])
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_entail_wit_2 : build_entail_wit_2 := by
  unfold build_entail_wit_2
  left
  intro n_pre data_pre key_pre data_input key_input key_prefix data_prefix S_prefix_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hdk : Znth (i-i) (sublist i n_pre data_input) 0 = Znth i data_input 0 := by
    rw [Znth_sublist 0 i (i-i) n_pre data_input (by omega) (by omega)]
    congr 1 <;> omega
  have hkk : Znth (i-i) (sublist i n_pre key_input) 0 = Znth i key_input 0 := by
    rw [Znth_sublist 0 i (i-i) n_pre key_input (by omega) (by omega)]
    congr 1 <;> omega
  rw [hdk,hkk]
  have hklen := PreH9.2.2.2.1
  have hdlen := PreH9.2.2.2.2.1
  have hs := push_appended_source__push_initialization S_prefix_2 key_prefix data_prefix i (Znth i data_input 0) (Znth i key_input 0) PreH9
  have hl := push_appended_loop_state__push_initialization S_prefix_2 key_prefix data_prefix i (Znth i data_input 0) (Znth i key_input 0) PreH9
  sep_apply (build_append_next_cell__build_progress key_pre i n_pre key_prefix key_input (by omega) hklen (by omega))
  sep_apply (build_append_next_cell__build_progress data_pre i n_pre data_prefix data_input (by omega) hdlen (by omega))
  Exists (key_prefix ++ [Znth i key_input 0]) (data_prefix ++ [Znth i data_input 0]) (key_prefix ++ [Znth i key_input 0]) (data_prefix ++ [Znth i data_input 0]) S_prefix_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_entail_wit_3 : build_entail_wit_3 := by
  unfold build_entail_wit_3
  left
  intro n_pre data_pre key_pre data_input key_input key_current_2 data_current_2 key_written_2 data_written_2 S_prefix_2 child key_x i data_x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  obtain ⟨h0,h1,h2⟩ := heap_parent_positive_bounds__push_sift_up child i PreH1 (by omega)
  unfold heap_parent at h0 h1 h2
  Exists key_current_2 data_current_2     key_written_2 data_written_2 S_prefix_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_entail_wit_4 : build_entail_wit_4 := by
  unfold build_entail_wit_4
  left
  intro n_pre data_pre key_pre data_input key_input S_prefix_2 key_written_2 data_written_2 key_current_2 data_current_2 data_x i key_x child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have h := push_break_establishes_result__push_sift_up S_prefix_2 key_written_2 data_written_2 key_current_2 data_current_2 i child parent data_x key_x (by assumption) (by assumption) (by assumption) PreH1
  Exists data_current_2 key_written_2     data_written_2 S_prefix_2 key_current_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_entail_wit_5 : build_entail_wit_5 := by
  unfold build_entail_wit_5
  left
  intro n_pre data_pre key_pre data_input key_input S_prefix_2 key_written_2 data_written_2 key_current_2 data_current_2 data_x i key_x child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  obtain ⟨hk,hd,hl⟩ := push_swap_advances_loop__push_sift_up key_written_2 data_written_2 key_current_2 data_current_2 i child parent data_x key_x PreH18 PreH8 PreH13 PreH1
  Exists (replace_Znth child (Znth parent key_current_2 0)       (replace_Znth parent (Znth child key_current_2 0) key_current_2)) (replace_Znth child (Znth parent data_current_2 0)       (replace_Znth parent (Znth child data_current_2 0) data_current_2)) key_written_2 data_written_2 S_prefix_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_entail_wit_6_1 : build_entail_wit_6_1 := by
  unfold build_entail_wit_6_1
  left
  intro n_pre data_pre key_pre data_input key_input key_current data_current key_written data_written S_prefix_2 child key_x i data_x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hz : child = 0 := by omega
  have hresult := push_zero_exit_result__push_finalization S_prefix_2 key_written data_written key_current data_current i data_x key_x PreH13 (by simpa only [hz] using PreH14)
  have hr := push_result_representation__push_finalization S_prefix_2 key_current data_current i data_x key_x (by omega) hresult
  have hp := build_prefix_extend__build_progress S_prefix_2 key_input data_input i data_x key_x (by omega) (by omega) (by omega) (by assumption) (by assumption) (by assumption)
  Exists key_current data_current (multiset_insert S_prefix_2 (heap_item key_x data_x))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_build_entail_wit_6_2 : build_entail_wit_6_2 := by
  unfold build_entail_wit_6_2
  left
  intro n_pre data_pre key_pre data_input key_input S_prefix_2 key_written data_written key_current data_current data_x i key_x child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hresult := PreH18
  have hr := push_result_representation__push_finalization S_prefix_2 key_current data_current i data_x key_x (by omega) hresult
  have hp := build_prefix_extend__build_progress S_prefix_2 key_input data_input i data_x key_x (by omega) (by omega) (by omega) (by assumption) (by assumption) (by assumption)
  Exists key_current data_current (multiset_insert S_prefix_2 (heap_item key_x data_x))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_build_return_wit_1_split_goal_spatial : build_return_wit_1_split_goal_spatial := by
  unfold build_return_wit_1_split_goal_spatial
  intro n_pre data_pre key_pre data_input key_input i PreH1 PreH2 PreH3 PreH4 PreH5
  subst n_pre
  have hk : key_input = [] := by
    apply List.eq_nil_of_length_eq_zero
    change (key_input.length : Int) = 0 at PreH4
    omega
  have hd : data_input = [] := by
    apply List.eq_nil_of_length_eq_zero
    change (data_input.length : Int) = 0 at PreH5
    omega
  subst key_input data_input
  have hr : heap_representation (list_to_multiset (pair_list [] [])) [] [] 0 := by
    refine ⟨by omega, by decide, rfl, rfl, rfl, List.Perm.refl _, ?_⟩
    intro child hc; omega
  sep_apply (concrete_arrays_to_store_heap__build_finalization key_pre data_pre _ [] [] 0 (by decide) hr)
  cancel

theorem proof_of_build_return_wit_1 : build_return_wit_1 := by
  unfold build_return_wit_1
  right
  exact proof_of_build_return_wit_1_split_goal_spatial

theorem proof_of_build_return_wit_2_split_goal_spatial : build_return_wit_2_split_goal_spatial := by
  unfold build_return_wit_2_split_goal_spatial
  intro n_pre data_pre key_pre data_input key_input key_prefix data_prefix S_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hi : i = n_pre := by omega
  subst i
  have he := build_prefix_complete__build_finalization S_prefix key_input data_input n_pre PreH8 (by omega) (by omega)
  have hr := store_heap_equiv_transport__build_finalization S_prefix (list_to_multiset (pair_list key_input data_input)) key_prefix data_prefix n_pre he PreH9
  sep_apply (concrete_arrays_to_store_heap__build_finalization key_pre data_pre _ _ _ n_pre (by omega) hr)
  cancel

theorem proof_of_build_return_wit_2 : build_return_wit_2 := by
  unfold build_return_wit_2
  right
  exact proof_of_build_return_wit_2_split_goal_spatial

theorem proof_of_pop_entail_wit_1 : pop_entail_wit_1 := by
  unfold pop_entail_wit_1
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before PreH1
  unfold store_heap
  Intros before_key before_data
  have hr : heap_representation S_before before_key before_data n_pre := by assumption
  have hn := hr.1
  have hc := hr.2.1
  sep_apply (heap_tail_to_undef_seg key_pre n_pre ⟨hn,hc⟩)
  sep_apply (heap_tail_to_undef_seg data_pre n_pre ⟨hn,hc⟩)
  obtain ⟨hp,hm⟩ := heap_root_is_multiset_minimum__pop_initialization S_before before_key before_data n_pre PreH1 hr
  Exists (heap_item (Znth 0 before_key 0) (Znth 0 before_data 0)) before_key before_data
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_2 : pop_entail_wit_2 := by
  unfold pop_entail_wit_2
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key before_data popped_2 PreH1 PreH2 PreH3 PreH4 PreH5
  have hh := PreH4.2.2.2.1
  have hk : item_key popped_2 = Znth 0 before_key 0 := by rw [hh]; rfl
  have hd : item_data popped_2 = Znth 0 before_data 0 := by rw [hh]; rfl
  Exists before_key before_data popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_3 : pop_entail_wit_3 := by
  unfold pop_entail_wit_3
  right
  intro n_pre data_pre key_pre S_before before_key before_data popped_2 result_key result_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  subst n_pre
  Exists popped_2
  sep_apply (singleton_store_heap_after_remove__pop_singleton key_pre data_pre S_before before_key before_data popped_2 (by assumption) (by assumption))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_entail_wit_4 : pop_entail_wit_4 := by
  unfold pop_entail_wit_4
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 popped_2 result_key result_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hc : heap_capacity = 100000 := rfl
  have hmax : INT_MAX = 2147483647 := rfl
  Exists before_key_2 before_data_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_5 : pop_entail_wit_5 := by
  unfold pop_entail_wit_5
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 popped_2 result_key result_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hk := PreH8.2.2.2.1
  have hd := PreH8.2.2.2.2.1
  have ho := PreH8.2.2.2.2.2.2
  have hl := pop_root_replacement_loop_state__pop_initialization before_key_2 before_data_2 n_pre PreH3 hk hd ho
  Exists (replace_Znth 0 (Znth (n_pre-1) before_key_2 0) before_key_2) (replace_Znth 0 (Znth (n_pre-1) before_data_2 0) before_data_2) before_key_2 before_data_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_6 : pop_entail_wit_6 := by
  unfold pop_entail_wit_6
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before current_key_2 current_data_2 before_key_2 before_data_2 idx result_data popped_2 result_key PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  Exists current_key_2 current_data_2     before_key_2 before_data_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_7_1 : pop_entail_wit_7_1 := by
  unfold pop_entail_wit_7_1
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 current_key_2 current_data_2 popped_2 result_key result_data idx left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst smallest left right
  have hsel := pop_select_right__pop_child_selection current_key_2 (n_pre-1) idx PreH7
    (by unfold heap_right_child; omega)
    (by simpa only [heap_left_child,heap_right_child,show idx*2+2=idx*2+1+1 by omega] using PreH1)
  simp only [heap_right_child,show idx*2+2=idx*2+1+1 by omega] at hsel
  Exists current_data_2 before_key_2 before_data_2 current_key_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_7_2 : pop_entail_wit_7_2 := by
  unfold pop_entail_wit_7_2
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 current_key_2 current_data_2 popped_2 result_key result_data idx left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  subst smallest left right
  have hsel := pop_select_left__pop_child_selection current_key_2 (n_pre-1) idx PreH6 (by unfold heap_left_child; omega)
    (Or.inl (by unfold heap_right_child; omega))
  simp only [heap_left_child] at hsel
  Exists current_data_2 before_key_2 before_data_2 current_key_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_7_3 : pop_entail_wit_7_3 := by
  unfold pop_entail_wit_7_3
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 current_key_2 current_data_2 popped_2 result_key result_data idx left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  subst smallest left right
  have hsel := pop_select_left__pop_child_selection current_key_2 (n_pre-1) idx PreH7 (by unfold heap_left_child; omega)
    (Or.inr (by simpa only [heap_left_child,heap_right_child,show idx*2+2=idx*2+1+1 by omega] using PreH1))
  simp only [heap_left_child] at hsel
  Exists current_data_2 before_key_2 before_data_2 current_key_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_8 : pop_entail_wit_8 := by
  unfold pop_entail_wit_8
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 current_key_2 current_data_2 popped_2 result_key result_data idx left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hr := pop_comparison_ready__pop_ready_exit before_key_2 before_data_2 current_key_2 current_data_2 n_pre popped_2 idx smallest (by assumption) (by assumption) (by assumption) PreH1
  have hc := PreH12.2.2.2.2.2.2.1
  obtain ⟨hln,hll,hrn,hrb⟩ := pop_next_index_arithmetic__pop_swap_transition current_key_2 (n_pre-1) idx smallest (by omega) (by omega) hc
  simp only [heap_left_child,heap_right_child] at hln hll hrn hrb
  Exists current_data_2 before_key_2 before_data_2     current_key_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_9 : pop_entail_wit_9 := by
  unfold pop_entail_wit_9
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key_2 before_data_2 current_key_2 current_data_2 popped_2 result_key result_data idx left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have his := PreH12.2.2.1
  have hc := PreH12.2.2.2.2.2.2.1
  obtain ⟨hln,hll,hrn,hrb⟩ := pop_next_index_arithmetic__pop_swap_transition current_key_2 (n_pre-1) idx smallest PreH6 PreH11 hc
  simp only [heap_left_child,heap_right_child] at hln hll hrn hrb
  obtain ⟨hk,hd,hl⟩ := pop_swap_advances_loop__pop_swap_transition before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx smallest PreH16 PreH12 PreH1
  have hcap : n_pre ≤ 100000 := PreH5
  have hmax : INT_MAX = 2147483647 := rfl
  Exists (replace_Znth smallest (Znth idx current_key_2 0) (replace_Znth idx (Znth smallest current_key_2 0) current_key_2)) (replace_Znth smallest (Znth idx current_data_2 0) (replace_Znth idx (Znth smallest current_data_2 0) current_data_2)) before_key_2 before_data_2 popped_2
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_return_wit_1 : pop_return_wit_1 := by
  unfold pop_return_wit_1
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before current_key current_data before_key before_data idx result_data popped_2 result_key PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hready := pop_leaf_ready__pop_ready_exit before_key before_data current_key current_data n_pre popped_2 idx PreH11 PreH13 (by unfold heap_left_child; omega)
  have hr := pop_ready_write_result__pop_finalization S_before before_key before_data current_key current_data n_pre popped_2 (by assumption) (by assumption) hready
  sep_apply (pop_result_store_retired_pair__pop_finalization key_pre data_pre S_before before_key before_data current_key current_data n_pre popped_2 (by omega) hr)
  Exists result_data popped_2 result_key
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_return_wit_2 : pop_return_wit_2 := by
  unfold pop_return_wit_2
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before before_key before_data current_key current_data popped_2 result_key result_data idx left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hready := PreH20
  have hr := pop_ready_write_result__pop_finalization S_before before_key before_data current_key current_data n_pre popped_2 (by assumption) (by assumption) hready
  sep_apply (pop_result_store_retired_pair__pop_finalization key_pre data_pre S_before before_key before_data current_key current_data n_pre popped_2 (by omega) hr)
  Exists result_data popped_2 result_key
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_return_wit_3 : pop_return_wit_3 := by
  unfold pop_return_wit_3
  left
  intro key_out_pre data_out_pre n_pre data_pre key_pre S_before popped_2 result_key result_data PreH1 PreH2 PreH3 PreH4
  subst n_pre
  Exists result_data popped_2 result_key
  simp only [show (1 : Int)-1=0 from rfl]
  pureIntros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto


end SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_proof_manual
