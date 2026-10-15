import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_goal
import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_auto
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open priority_queue_goal priority_queue_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem cell_to_seg (p i value : Int) :
    ((p+i*sizeof(INT)) # Int |-> value) |-- intArray.seg p i (i+1) [value] := by
  exact intArray.seg_single p i value

theorem proof_of_push_entail_wit_1 : push_entail_wit_1 := by
  unfold push_entail_wit_1
  left
  intro x_pre n_pre heap_pre S_before PreH1 PreH2
  unfold store_heap
  Intros base
  have hr : heap_representation S_before base n_pre := by assumption
  have hl := push_appended_loop_state__push_initialization S_before base n_pre x_pre hr
  have hs := push_appended_source__push_initialization S_before base n_pre x_pre hr
  Exists (base ++ [x_pre]) (base ++ [x_pre])
  sep_apply (intArray.seg_single heap_pre n_pre x_pre)
  sep_apply (intArray.full_to_seg heap_pre n_pre base)
  sep_apply (intArray.seg_merge_to_full heap_pre 0 n_pre (n_pre+1) base [x_pre] (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_push_entail_wit_2 : push_entail_wit_2 := by
  unfold push_entail_wit_2
  left
  intro x_pre n_pre heap_pre S_before current_2 written_2 child PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  obtain ⟨h0,h1,h2⟩ := heap_parent_positive_bounds__push_sift_up child n_pre PreH1 PreH5
  unfold heap_parent at h0 h1 h2
  Exists current_2 written_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_push_entail_wit_3 : push_entail_wit_3 := by
  unfold push_entail_wit_3
  left
  intro x_pre n_pre heap_pre S_before written_2 current_2 child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  obtain ⟨hv,hl⟩ := push_swap_advances_loop__push_sift_up written_2 current_2 n_pre child parent x_pre PreH11 PreH4 PreH9 PreH1
  Exists (replace_Znth child (Znth parent current_2 0) (replace_Znth parent (Znth child current_2 0) current_2)) written_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_push_return_wit_1_split_goal_spatial : push_return_wit_1_split_goal_spatial := by
  unfold push_return_wit_1_split_goal_spatial
  intro x_pre n_pre heap_pre S_before current written child PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hz : child = 0 := by omega
  have hresult := push_zero_exit_result__push_finalization S_before written current n_pre x_pre PreH6 (by simpa only [hz] using PreH7)
  have hr := push_result_representation__push_finalization S_before current n_pre x_pre PreH3 hresult
  unfold store_heap
  Exists current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_push_return_wit_1 : push_return_wit_1 := by
  unfold push_return_wit_1
  right
  exact proof_of_push_return_wit_1_split_goal_spatial

theorem proof_of_push_return_wit_2_split_goal_spatial : push_return_wit_2_split_goal_spatial := by
  unfold push_return_wit_2_split_goal_spatial
  intro x_pre n_pre heap_pre S_before written current child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hresult := push_break_establishes_result__push_sift_up S_before written current n_pre child parent x_pre PreH10 PreH11 PreH9 PreH1
  have hr := push_result_representation__push_finalization S_before current n_pre x_pre PreH3 hresult
  unfold store_heap
  Exists current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_push_return_wit_2 : push_return_wit_2 := by
  unfold push_return_wit_2
  right
  exact proof_of_push_return_wit_2_split_goal_spatial

theorem proof_of_build_entail_wit_1 : build_entail_wit_1 := by
  unfold build_entail_wit_1
  intro n_pre heap_pre input PreH1 PreH2 PreH3
  by_cases hz : n_pre = 0
  · Left
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first | assumption | trivial | omega
  · Right
    obtain ⟨hp,hr⟩ := build_initial_prefix__build_progress input n_pre PreH3 (by omega)
    sep_apply (intArray.full_split_to_seg heap_pre 1 n_pre input (by omega))
    unfold store_heap
    Exists (list_to_multiset [Znth 0 input 0]) (sublist 0 1 input)
    sep_apply (intArray.seg_to_full heap_pre 0 1 (sublist 0 1 input))
    simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
    split_pure_spatial
    · cancel
    · split_pures
      all_goals dump_pre_spatial
      all_goals first | assumption | trivial | omega

theorem proof_of_build_entail_wit_2 : build_entail_wit_2 := by
  unfold build_entail_wit_2
  left
  intro n_pre heap_pre input S_prefix_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hread : Znth (i-i) (sublist i n_pre input) 0 = Znth i input 0 := by
    rw [Znth_sublist 0 i (i-i) n_pre input (by omega) (by omega)]
    simp
  Exists S_prefix_2
  sep_apply (build_split_next_cell__build_progress heap_pre i n_pre input (by omega) (by omega))
  unfold heap_spare
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1 := by
  unfold build_entail_wit_3_split_goal_1
  intro n_pre input S_prefix_2 i x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact build_prefix_extend__build_progress S_prefix_2 input i x PreH3 (by omega) PreH5 PreH7

theorem proof_of_build_entail_wit_3 : build_entail_wit_3 := by
  unfold build_entail_wit_3
  right
  intro n_pre input S_prefix_2 i x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have h := build_prefix_extend__build_progress S_prefix_2 input i x PreH3 (by omega) PreH5 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_build_return_wit_1_split_goal_spatial : build_return_wit_1_split_goal_spatial := by
  unfold build_return_wit_1_split_goal_spatial
  intro n_pre heap_pre input i PreH1 PreH2 PreH3 PreH4
  subst n_pre
  have hi : input = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [Zlength,Int.ofNat_eq_coe] at PreH4
    omega
  subst input
  have hr : heap_representation (list_to_multiset []) [] 0 := by
    refine ⟨by omega,by decide,rfl,rfl,List.Perm.refl _,?_⟩
    intro child hc; omega
  unfold store_heap
  Exists ([] : List Int)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_return_wit_1 : build_return_wit_1 := by
  unfold build_return_wit_1
  right
  exact proof_of_build_return_wit_1_split_goal_spatial

theorem proof_of_build_return_wit_2_split_goal_spatial : build_return_wit_2_split_goal_spatial := by
  unfold build_return_wit_2_split_goal_spatial
  intro n_pre heap_pre input S_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hi : i = n_pre := by omega
  subst i
  unfold store_heap
  Intros concrete
  have hr : heap_representation S_prefix concrete n_pre := by assumption
  have he := build_prefix_complete__build_finalization S_prefix input n_pre PreH7 PreH6.symm
  have ht := store_heap_equiv_transport__build_finalization S_prefix (list_to_multiset input) concrete n_pre he hr
  Exists concrete
  rw [Zsublist_nil input n_pre n_pre (by omega)]
  sep_apply ((intArray.seg_empty heap_pre n_pre n_pre).1)
  Intros
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_build_return_wit_2 : build_return_wit_2 := by
  unfold build_return_wit_2
  right
  exact proof_of_build_return_wit_2_split_goal_spatial

theorem proof_of_pop_entail_wit_1 : pop_entail_wit_1 := by
  unfold pop_entail_wit_1
  left
  intro n_pre heap_pre S_before PreH1 PreH2
  unfold store_heap
  Intros before
  have hr : heap_representation S_before before n_pre := by assumption
  have hcap := hr.2.1
  obtain ⟨hp,hroot,hm⟩ := heap_root_is_multiset_max__pop_initialization S_before before n_pre PreH1 hr
  Exists before
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_entail_wit_2 : pop_entail_wit_2 := by
  unfold pop_entail_wit_2
  left
  intro n_pre heap_pre S_before before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hloop := pop_root_replacement_loop_state__pop_initialization before n_pre (by omega) PreH4.2.2.2.1 PreH4.2.2.2.2.2
  Exists (replace_Znth 0 (Znth (n_pre-1) before 0) before) before
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_entail_wit_3_1 : pop_entail_wit_3_1 := by
  unfold pop_entail_wit_3_1
  left
  intro n_pre heap_pre S_before current_2 idx before_2 ret PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hsel := pop_select_right__pop_child_selection current_2 (n_pre-1) idx PreH11 (by unfold heap_right_child; omega)
    (by simpa only [heap_left_child, heap_right_child, show idx*2+2=idx*2+1+1 by omega] using PreH1)
  simp only [heap_left_child, heap_right_child, show idx*2+2=idx*2+1+1 by omega] at hsel
  Exists current_2 before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_entail_wit_3_2 : pop_entail_wit_3_2 := by
  unfold pop_entail_wit_3_2
  left
  intro n_pre heap_pre S_before current_2 idx before_2 ret PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hsel := pop_select_left__pop_child_selection current_2 (n_pre-1) idx PreH10 (by unfold heap_left_child; omega) (Or.inl (by unfold heap_right_child; omega))
  simp only [heap_left_child, heap_right_child, show idx*2+2=idx*2+1+1 by omega] at hsel
  Exists current_2 before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_entail_wit_3_3 : pop_entail_wit_3_3 := by
  unfold pop_entail_wit_3_3
  left
  intro n_pre heap_pre S_before current_2 idx before_2 ret PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hsel := pop_select_left__pop_child_selection current_2 (n_pre-1) idx PreH11 (by unfold heap_left_child; omega) (Or.inr (by simpa only [heap_left_child, heap_right_child, show idx*2+2=idx*2+1+1 by omega] using PreH1))
  simp only [heap_left_child, heap_right_child, show idx*2+2=idx*2+1+1 by omega] at hsel
  Exists current_2 before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_pop_entail_wit_4 : pop_entail_wit_4 := by
  unfold pop_entail_wit_4
  left
  intro n_pre heap_pre S_before before_2 current_2 ret idx left right largest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hloop := pop_swap_advances_loop__pop_swap_transition before_2 current_2 n_pre idx largest PreH16 PreH15 PreH1
  have hchoice := PreH15.2.2.2.2.2.2.1
  have harith := pop_next_index_arithmetic__pop_swap_transition current_2 (n_pre-1) idx largest PreH9 PreH14 hchoice
  dsimp only [heap_left_child,heap_right_child] at harith
  have hlen := PreH16.2.2.1
  have hread := Znth_replace_Znth_Same 0 (replace_Znth idx (Znth largest current_2 0) current_2) largest (Znth idx current_2 0) (by rw [Zlength_replace_Znth]; omega)
  have hidx := PreH15.2.2.1
  have hcap : n_pre ≤ 100000 := PreH3
  have hmax : INT_MAX = 2147483647 := rfl
  Exists (replace_Znth largest (Znth idx current_2 0) (replace_Znth idx (Znth largest current_2 0) current_2)) before_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto

theorem proof_of_pop_return_wit_1_split_goal_spatial : pop_return_wit_1_split_goal_spatial := by
  unfold pop_return_wit_1_split_goal_spatial
  intro n_pre heap_pre S_before current idx before ret PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hready := pop_leaf_ready__pop_ready_exit before current n_pre ret idx PreH7 PreH13 PreH1
  have hresult := pop_ready_write_result__pop_finalization S_before before current n_pre ret PreH5 PreH6 hready
  sep_apply (pop_result_store_retired__pop_finalization heap_pre S_before before current n_pre ret PreH3 hresult)
  cancel

theorem proof_of_pop_return_wit_1 : pop_return_wit_1 := by
  unfold pop_return_wit_1
  right
  exact proof_of_pop_return_wit_1_split_goal_spatial

theorem proof_of_pop_return_wit_2_split_goal_spatial : pop_return_wit_2_split_goal_spatial := by
  unfold pop_return_wit_2_split_goal_spatial
  intro n_pre heap_pre S_before before current ret idx left right largest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hready := pop_comparison_ready__pop_ready_exit before current n_pre ret idx largest PreH7 PreH16 PreH15 PreH1
  have hresult := pop_ready_write_result__pop_finalization S_before before current n_pre ret PreH5 PreH6 hready
  sep_apply (pop_result_store_retired__pop_finalization heap_pre S_before before current n_pre ret PreH3 hresult)
  cancel

theorem proof_of_pop_return_wit_2 : pop_return_wit_2 := by
  unfold pop_return_wit_2
  right
  exact proof_of_pop_return_wit_2_split_goal_spatial

theorem proof_of_pop_return_wit_3_split_goal_spatial : pop_return_wit_3_split_goal_spatial := by
  unfold pop_return_wit_3_split_goal_spatial
  intro n_pre heap_pre S_before before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  subst n_pre
  have hlen := PreH4.2.2.2.1
  have hms := PreH4.2.2.1
  have hr := remove_max_singleton_empty__pop_singleton S_before hms
  have hrep : heap_representation (multiset_remove S_before (multiset_max S_before)) [] 0 := by
    refine ⟨by omega,by decide,?_,rfl,?_,?_⟩
    · unfold multiset_size; rw [hr]; rfl
    · unfold heap_relation; rw [hr]
    · intro child hc; omega
  sep_apply (singleton_full_split_retired__pop_singleton heap_pre before (Znth 0 before 0) hlen rfl)
  unfold store_heap heap_spare
  Exists ([] : List Int)
  simp only [Int.zero_add,Int.sub_self]
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    simpa only [PreH6] using hrep

theorem proof_of_pop_return_wit_3 : pop_return_wit_3 := by
  unfold pop_return_wit_3
  right
  exact proof_of_pop_return_wit_3_split_goal_spatial

theorem proof_of_heap_sort_entail_wit_1 : heap_sort_entail_wit_1 := by
  unfold heap_sort_entail_wit_1
  left
  intro n_pre heap_pre input PreH1 PreH2 PreH3
  have h := heap_sort_initial_state__heap_sort_setup input
  Exists ([] : List Int) (list_to_multiset input)
  simp only [Zlength_nil, Int.sub_self]
  split_pure_spatial
  · cancel
    refine naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ ((intArray.seg_empty heap_pre n_pre n_pre).2)
    split_pure_spatial
    · cancel
    · dump_pre_spatial; rfl
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_heap_sort_entail_wit_2 : heap_sort_entail_wit_2 := by
  unfold heap_sort_entail_wit_2
  left
  intro n_pre heap_pre input suffix_2 active_2 i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hne : mlist active_2 ≠ [] := by
    intro he
    have hm := PreH1.1
    rw [he] at hm
    exact List.not_mem_nil hm
  have hmax := multiset_max_is_maximum active_2 hne
  have he : retval = multiset_max active_2 :=
    Int.le_antisymm (hmax.2 retval PreH1.1) (PreH1.2 _ hmax.1)
  obtain ⟨hsize,hstate⟩ := heap_sort_extract_step__heap_sort_transition input active_2 suffix_2 retval he PreH1 PreH10
  rw [← he] at hsize hstate
  have hlen : Zlength (retval::suffix_2) = n_pre-(i-1) := by rw [Zlength_cons,PreH9]; omega
  Exists (retval::suffix_2) (multiset_remove active_2 retval)
  sep_apply (intArray.seg_single heap_pre (i-1) retval)
  rw [show i-1+1=i by omega]
  sep_apply (intArray.seg_merge_to_seg heap_pre (i-1) i n_pre [retval] suffix_2 (by omega))
  simp only [List.singleton_append]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | int_auto

theorem proof_of_heap_sort_return_wit_1 : heap_sort_return_wit_1 := by
  unfold heap_sort_return_wit_1
  left
  intro n_pre heap_pre input suffix active i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hi : i = 0 := by omega
  have hsize : multiset_size active = 0 := by omega
  obtain ⟨hnil,hperm,hincr⟩ := heap_sort_empty_state_output__heap_sort_finalization input active suffix hsize PreH9
  rw [hi]
  Exists suffix
  sep_apply (heap_sort_zero_store_join__heap_sort_finalization heap_pre n_pre active suffix PreH2)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto


end SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_manual
