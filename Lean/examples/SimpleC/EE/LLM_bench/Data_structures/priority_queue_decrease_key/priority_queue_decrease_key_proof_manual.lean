import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal
import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_proof_auto
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open priority_queue_decrease_key_goal priority_queue_decrease_key_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

local macro "finish_entail" : tactic => `(tactic| (
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto))

theorem proof_of_pqdk_sift_up_entail_wit_1 : pqdk_sift_up_entail_wit_1 := by
  unfold pqdk_sift_up_entail_wit_1
  left
  intro idx_pre n_pre data_bound_pre pos_pre data_pre key_pre capacity M PreH1 PreH2 PreH3 PreH4
  unfold store_sift_up
  Intros key_values data_values pos_values
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_sift_up_entail_wit_2 : pqdk_sift_up_entail_wit_2 := by
  unfold pqdk_sift_up_entail_wit_2
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values_2 data_values_2 pos_values_2 child PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  obtain ⟨hp0,hpc,hpn⟩ := heap_parent_positive_bounds child n_pre PreH1 PreH5
  unfold heap_parent at hp0 hpc hpn
  have he : Z.quot (child - 1) 2 = heap_parent child := rfl
  Exists key_values_2 data_values_2 pos_values_2
  finish_entail

theorem proof_of_pqdk_sift_up_entail_wit_3 : pqdk_sift_up_entail_wit_3 := by
  unfold pqdk_sift_up_entail_wit_3
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values_2 child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hv := PreH10.1.2.2.2.2.2.1
  have hc := hv child (by omega)
  have hp := hv parent (by omega)
  Exists pos_values_2 data_values key_values
  finish_entail

theorem proof_of_pqdk_sift_up_entail_wit_4 : pqdk_sift_up_entail_wit_4 := by
  unfold pqdk_sift_up_entail_wit_4
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values_2 data_values_2 pos_values_2 child parent tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst tmp_key tmp_data
  have hswap := sift_up_swap_state M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child parent PreH16 PreH3 PreH8 PreH9
  have hklen := PreH16.1.2.2.1.1
  have hdlen := PreH16.1.2.2.1.2.1
  have hkey := Znth_swap_Znth key_values_2 parent child 0 (by omega) (by omega) (by omega)
  have hdata := Znth_swap_Znth data_values_2 parent child 0 (by omega) (by omega) (by omega)
  dsimp only at hkey hdata
  obtain ⟨hki,hkj,_⟩ := hkey
  obtain ⟨hdi,hdj,_⟩ := hdata
  unfold heap_swap_values heap_swap_pos at hswap
  Exists (replace_Znth child (Znth parent key_values_2 0) (replace_Znth parent (Znth child key_values_2 0) key_values_2)) (replace_Znth child (Znth parent data_values_2 0) (replace_Znth parent (Znth child data_values_2 0) data_values_2)) (replace_Znth (Znth child data_values_2 0) parent (replace_Znth (Znth parent data_values_2 0) child pos_values_2))
  finish_entail

theorem proof_of_pqdk_sift_up_return_wit_1 : pqdk_sift_up_return_wit_1 := by
  unfold pqdk_sift_up_return_wit_1
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values child PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hr := sift_up_state_heap_representation_at_root M key_values data_values pos_values data_bound_pre n_pre child PreH1 PreH6
  unfold store_heap
  Exists key_values data_values pos_values
  finish_entail

theorem proof_of_pqdk_sift_up_return_wit_2 : pqdk_sift_up_return_wit_2 := by
  unfold pqdk_sift_up_return_wit_2
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hr := sift_up_state_heap_representation_at_break M key_values data_values pos_values data_bound_pre n_pre child parent PreH4 PreH9 PreH1 PreH10
  unfold store_heap
  Exists key_values data_values pos_values
  finish_entail

theorem proof_of_pqdk_sift_down_safety_wit_1 : pqdk_sift_down_safety_wit_1 := by
  unfold pqdk_sift_down_safety_wit_1
  left
  intro idx_pre n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values current PreH1 PreH2 PreH3 PreH4 PreH5
  have hcap : heap_capacity = 100000 := rfl
  have hmax : INT_MAX = 2147483647 := rfl
  have hmin : INT_MIN = -2147483648 := rfl
  split_pures
  all_goals dump_pre_spatial
  all_goals omega

theorem proof_of_pqdk_sift_down_safety_wit_2 : pqdk_sift_down_safety_wit_2 := by
  unfold pqdk_sift_down_safety_wit_2
  left
  intro idx_pre n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values current PreH1 PreH2 PreH3 PreH4 PreH5
  have hcap : heap_capacity = 100000 := rfl
  have hmax : INT_MAX = 2147483647 := rfl
  have hmin : INT_MIN = -2147483648 := rfl
  split_pures
  all_goals dump_pre_spatial
  all_goals omega

theorem proof_of_pqdk_sift_down_entail_wit_1 : pqdk_sift_down_entail_wit_1 := by
  unfold pqdk_sift_down_entail_wit_1
  left
  intro idx_pre n_pre data_bound_pre pos_pre data_pre key_pre capacity M PreH1 PreH2 PreH3 PreH4
  unfold store_sift_down
  Intros key_values data_values pos_values
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_sift_down_entail_wit_3_1 : pqdk_sift_down_entail_wit_3_1 := by
  unfold pqdk_sift_down_entail_wit_3_1
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hl : left = heap_left_child current := by unfold heap_left_child; omega
  have hr : right = heap_right_child current := by unfold heap_right_child; omega
  have hs : SelectedChild key_values_2 n_pre current right := by
    rw [hr]
    apply selected_child_right key_values_2 n_pre current PreH5 PreH6
    · omega
    · simpa only [← hl,← hr] using PreH1
  Exists data_values_2 pos_values_2 key_values_2
  finish_entail

theorem proof_of_pqdk_sift_down_entail_wit_3_2 : pqdk_sift_down_entail_wit_3_2 := by
  unfold pqdk_sift_down_entail_wit_3_2
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hl : left = heap_left_child current := by unfold heap_left_child; omega
  have hr : right = heap_right_child current := by unfold heap_right_child; omega
  have hs : SelectedChild key_values_2 n_pre current smallest := by
    rw [PreH8,hl]
    apply selected_child_left key_values_2 n_pre current PreH4 PreH5
    · omega
    · left; omega
  Exists data_values_2 pos_values_2 key_values_2
  finish_entail

theorem proof_of_pqdk_sift_down_entail_wit_3_3 : pqdk_sift_down_entail_wit_3_3 := by
  unfold pqdk_sift_down_entail_wit_3_3
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hl : left = heap_left_child current := by unfold heap_left_child; omega
  have hr : right = heap_right_child current := by unfold heap_right_child; omega
  have hs : SelectedChild key_values_2 n_pre current smallest := by
    rw [PreH9,hl]
    apply selected_child_left key_values_2 n_pre current PreH5 PreH6
    · omega
    · right; simpa only [← hl,← hr] using PreH1
  Exists data_values_2 pos_values_2 key_values_2
  finish_entail

theorem proof_of_pqdk_sift_down_entail_wit_4 : pqdk_sift_down_entail_wit_4 := by
  unfold pqdk_sift_down_entail_wit_4
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values_2 current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hv := PreH11.1.2.2.2.2.2.1
  have hc := hv current (by omega)
  have hs := hv smallest (by omega)
  have hp := PreH10.2.2.2.2.2.1
  have hcs := PreH10.2.2.1
  have hbranches := heap_children_characterization current smallest PreH4 (by omega) hp
  have hl : left < n_pre := by
    simp only [heap_left_child,heap_right_child] at hbranches
    omega
  Exists pos_values_2 data_values key_values
  finish_entail

theorem proof_of_pqdk_sift_down_entail_wit_5 : pqdk_sift_down_entail_wit_5 := by
  unfold pqdk_sift_down_entail_wit_5
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values_2 data_values_2 pos_values_2 current left right smallest tmp_key tmp_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  subst tmp_key tmp_data
  have hswap := sift_down_swap_state M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current smallest PreH21 PreH20 PreH13
  have hklen := PreH21.1.2.2.1.1
  have hdlen := PreH21.1.2.2.1.2.1
  have hkey := Znth_swap_Znth key_values_2 current smallest 0 (by omega) (by omega) (by omega)
  have hdata := Znth_swap_Znth data_values_2 current smallest 0 (by omega) (by omega) (by omega)
  dsimp only at hkey hdata
  obtain ⟨hki,hkj,_⟩ := hkey
  obtain ⟨hdi,hdj,_⟩ := hdata
  unfold heap_swap_values heap_swap_pos at hswap
  Exists (replace_Znth smallest (Znth current key_values_2 0) (replace_Znth current (Znth smallest key_values_2 0) key_values_2)) (replace_Znth smallest (Znth current data_values_2 0) (replace_Znth current (Znth smallest data_values_2 0) data_values_2)) (replace_Znth (Znth smallest data_values_2 0) current (replace_Znth (Znth current data_values_2 0) smallest pos_values_2))
  finish_entail

theorem proof_of_pqdk_sift_down_return_wit_1 : pqdk_sift_down_return_wit_1 := by
  unfold pqdk_sift_down_return_wit_1
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hl : heap_left_child current ≥ n_pre := by unfold heap_left_child; omega
  have hr := sift_down_state_heap_representation_at_leaf M key_values data_values pos_values data_bound_pre n_pre current hl PreH6
  unfold store_heap
  Exists key_values data_values pos_values
  finish_entail

theorem proof_of_pqdk_sift_down_return_wit_2 : pqdk_sift_down_return_wit_2 := by
  unfold pqdk_sift_down_return_wit_2
  left
  intro n_pre data_bound_pre pos_pre data_pre key_pre capacity M key_values data_values pos_values current left right smallest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hr := sift_down_state_heap_representation_at_break M key_values data_values pos_values data_bound_pre n_pre current smallest PreH1 PreH10 PreH11
  unfold store_heap
  Exists key_values data_values pos_values
  finish_entail

theorem proof_of_pqdk_push_safety_wit_1 : pqdk_push_safety_wit_1 := by
  unfold pqdk_push_safety_wit_1
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hcap : heap_capacity = 100000 := rfl
  have hmax : INT_MAX = 2147483647 := rfl
  have hmin : INT_MIN = -2147483648 := rfl
  split_pures
  all_goals dump_pre_spatial
  all_goals omega

theorem proof_of_pqdk_push_entail_wit_1 : pqdk_push_entail_wit_1 := by
  unfold pqdk_push_entail_wit_1
  left
  intro data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  unfold store_heap
  Intros key_values data_values pos_values
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_push_entail_wit_2 : pqdk_push_entail_wit_2 := by
  unfold pqdk_push_entail_wit_2
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hp := push_write_state_from_heap_representation M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre PreH7 PreH6 (by omega) (by omega)
  have hs := hp.2.1
  unfold store_sift_up
  Exists (key_values ++ [key_x_pre]) (data_values ++ [data_x_pre]) (replace_Znth data_x_pre n pos_values)
  pureIntros
  finish_entail

theorem proof_of_pqdk_decrease_key_entail_wit_1 : pqdk_decrease_key_entail_wit_1 := by
  unfold pqdk_decrease_key_entail_wit_1
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  unfold store_heap
  Intros key_values data_values pos_values
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_decrease_key_entail_wit_2 : pqdk_decrease_key_entail_wit_2 := by
  unfold pqdk_decrease_key_entail_wit_2
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values_2 data_values_2 pos_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  obtain ⟨hi,hr⟩ := heap_index_of_from_heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n data_x_pre key_x_pre PreH7 (by omega) PreH6
  Exists key_values_2 data_values_2 pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_decrease_key_entail_wit_3 : pqdk_decrease_key_entail_wit_3 := by
  unfold pqdk_decrease_key_entail_wit_3
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hw := decrease_key_write_state_from_heap_representation M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre idx PreH8 PreH6 PreH7 (by omega)
  have hs := hw.2.2.2.1
  unfold store_sift_up
  Exists (replace_Znth idx key_x_pre key_values) data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_update_or_push_entail_wit_1 : pqdk_update_or_push_entail_wit_1 := by
  unfold pqdk_update_or_push_entail_wit_1
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  unfold store_heap
  Intros key_values data_values pos_values
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_update_or_push_entail_wit_2 : pqdk_update_or_push_entail_wit_2 := by
  unfold pqdk_update_or_push_entail_wit_2
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have ha := partial_map_absent_from_negative_pos M_before key_values data_values pos_values data_bound_pre n data_x_pre PreH8 (by omega) PreH1
  unfold store_heap
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_update_or_push_entail_wit_3 : pqdk_update_or_push_entail_wit_3 := by
  unfold pqdk_update_or_push_entail_wit_3
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hd := partial_map_decrease_key_pre_from_nonnegative_pos M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre PreH8 (by omega) (by omega) PreH7
  unfold store_heap
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_update_or_push_entail_wit_4_1 : pqdk_update_or_push_entail_wit_4_1 := by
  unfold pqdk_update_or_push_entail_wit_4_1
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hs : partial_map_update_or_add_size M_before n (n + 1) data_x_pre key_x_pre := Or.inl ⟨PreH6,rfl⟩
  Exists (n + 1)
  pureIntros
  simp only [partial_map_update_or_add,partial_map_update]
  finish_entail

theorem proof_of_pqdk_update_or_push_entail_wit_4_2 : pqdk_update_or_push_entail_wit_4_2 := by
  unfold pqdk_update_or_push_entail_wit_4_2
  left
  intro key_x_pre data_x_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hs : partial_map_update_or_add_size M_before n n data_x_pre key_x_pre := Or.inr ⟨PreH6,rfl⟩
  Exists n
  pureIntros
  simp only [partial_map_update_or_add,partial_map_update]
  finish_entail

theorem proof_of_pqdk_pop_entail_wit_1 : pqdk_pop_entail_wit_1 := by
  unfold pqdk_pop_entail_wit_1
  left
  intro key_out_pre data_out_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before PreH1 PreH2 PreH3
  unfold store_heap
  Intros key_values data_values pos_values
  Exists key_values data_values pos_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_pop_entail_wit_2 : pqdk_pop_entail_wit_2 := by
  unfold pqdk_pop_entail_wit_2
  left
  intro key_out_pre data_out_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values_2 PreH1 PreH2 PreH3 PreH4
  have hv := PreH4.2.2.2.2.2.2.1
  have hroot := hv 0 (by omega)
  Exists pos_values_2 data_values key_values
  pureIntros
  finish_entail

theorem proof_of_pqdk_pop_entail_wit_3 : pqdk_pop_entail_wit_3 := by
  unfold pqdk_pop_entail_wit_3
  left
  intro key_out_pre data_out_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values_2 data_values_2 pos_values_2 result_key result_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  subst result_key result_data
  have hm := pop_marked_state_from_heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n (by omega) PreH9
  have hv := PreH9.2.2.2.2.2.2.1
  have hlast := hv (n-1) (by omega)
  unfold absent at hm
  Exists key_values_2 (replace_Znth (Znth 0 data_values_2 0) (-1 : Int) pos_values_2) data_values_2 (heap_item (Znth 0 key_values_2 0) (Znth 0 data_values_2 0))
  pureIntros
  finish_entail

theorem proof_of_pqdk_pop_entail_wit_4 : pqdk_pop_entail_wit_4 := by
  unfold pqdk_pop_entail_wit_4
  left
  intro key_out_pre data_out_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before popped_2 key_values data_values pos_values result_key result_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hm := PreH11.2.1
  have hklen := PreH11.2.2.2.2.1.1
  have hdlen := PreH11.2.2.2.2.1.2.1
  have hs := pop_root_replacement_sift_down_state M_before key_values data_values pos_values data_bound_pre n popped_2 PreH1 PreH11
  have hv := hs.1.2.2.2.2.2.1
  have hr := hv 0 (by omega)
  sep_apply (full_retire_last_to_undef key_pre n capacity (replace_Znth 0 (Znth (n-1) key_values 0) key_values) (by omega) (by omega) (by rw [Zlength_replace_Znth]; exact hklen))
  sep_apply (full_retire_last_to_undef data_pre n capacity (replace_Znth 0 (Znth (n-1) data_values 0) data_values) (by omega) (by omega) (by rw [Zlength_replace_Znth]; exact hdlen))
  unfold pop_replaced_values at hs hr
  unfold store_sift_down
  Exists popped_2 (sublist 0 (n-1) (replace_Znth 0 (Znth (n-1) key_values 0) key_values)) (sublist 0 (n-1) (replace_Znth 0 (Znth (n-1) data_values 0) data_values)) (replace_Znth (Znth (n-1) data_values 0) (0 : Int) pos_values)
  pureIntros
  finish_entail

theorem proof_of_pqdk_pop_return_wit_1 : pqdk_pop_return_wit_1 := by
  unfold pqdk_pop_return_wit_1
  left
  intro key_out_pre data_out_pre data_bound_pre size_pre pos_pre data_pre key_pre capacity n M_before key_values data_values pos_values result_key result_data PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  subst n result_key result_data
  have hm := heap_root_is_partial_map_minimum M_before key_values data_values pos_values data_bound_pre 1 (by omega) PreH9
  have hr := heap_representation_remove_singleton M_before key_values data_values pos_values data_bound_pre PreH9
  have hklen := PreH9.2.2.1.1
  have hdlen := PreH9.2.2.1.2.1
  sep_apply (singleton_full_to_empty_undef key_pre capacity key_values (by omega) hklen)
  sep_apply (singleton_full_to_empty_undef data_pre capacity data_values (by omega) hdlen)
  unfold store_heap
  unfold absent at hr
  Exists (Znth 0 data_values 0) (heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)) (Znth 0 key_values 0) ([] : List Int) ([] : List Int) (replace_Znth (Znth 0 data_values 0) (-1 : Int) pos_values)
  pureIntros
  simp only [Int.sub_self]
  finish_entail


end SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_proof_manual
