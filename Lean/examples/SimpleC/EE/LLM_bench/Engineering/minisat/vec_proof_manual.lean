import SimpleC.EE.LLM_bench.Engineering.minisat.vec_goal
import SimpleC.EE.LLM_bench.Engineering.minisat.vec_proof_auto
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Engineering.minisat.vec_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open vec_goal vec_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

private theorem ptr_size_Z_eq_sizeof : ptr_size_Z = sizeof(PTR) := by
  rfl

theorem proof_of_veci_new_return_wit_1 : veci_new_return_wit_1 := by
  unfold veci_new_return_wit_1
  left
  intro v_pre retval PreH1 PreH2 PreH3
  refine Automation.exp_right_rule (CRules := naive_C_Rules) retval ?_
  unfold veci_raw veci_header veci_buffer
  simp only [show Zlength ([] : List Int) = 0 from rfl]
  have he : intArray.undef_full retval 4 = intArray.undef_seg retval 0 4 := rfl
  rw [he]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.full_empty retval 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact ⟨PreH3, PreH1, by omega, by omega, by omega, by decide, PreH2⟩
      | rfl


theorem proof_of_veci_new_which_implies_wit_1 : veci_new_which_implies_wit_1 := by
  unfold veci_new_which_implies_wit_1
  left
  intro v
  unfold veci_shell
  Intros_p hneq
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hneq


theorem proof_of_veci_delete_return_wit_1_split_goal_spatial : veci_delete_return_wit_1_split_goal_spatial := by
  unfold veci_delete_return_wit_1_split_goal_spatial
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  unfold veci_shell
  split_pure_spatial
  · sep_apply (store_int_undef_store_int naive_C_Rules (&((v_pre # "veci_t") ->ₛ "size")) (Zlength xs))
    sep_apply (store_int_undef_store_int naive_C_Rules (&((v_pre # "veci_t") ->ₛ "cap")) cap)
    sep_apply (store_ptr_undef_store_ptr naive_C_Rules (&((v_pre # "veci_t") ->ₛ "ptr")) buf)
    cancel
  · dump_pre_spatial
    exact PreH5


theorem proof_of_veci_delete_return_wit_1 : veci_delete_return_wit_1 := by
  unfold veci_delete_return_wit_1
  right
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact proof_of_veci_delete_return_wit_1_split_goal_spatial v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_veci_delete_which_implies_wit_1 : veci_delete_which_implies_wit_1 := by
  unfold veci_delete_which_implies_wit_1
  left
  intro xs v
  unfold store_veci veci_raw veci_header veci_buffer
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro buf
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro cap
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption


theorem proof_of_veci_begin_return_wit_1 : veci_begin_return_wit_1 := by
  unfold veci_begin_return_wit_1
  left
  intro v_pre xs cap_2 buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap_2 ?_
  unfold veci_raw veci_header veci_buffer
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨PreH1, PreH2, PreH3, PreH4, PreH5, PreH6, PreH7⟩


theorem proof_of_veci_begin_which_implies_wit_1 : veci_begin_which_implies_wit_1 := by
  unfold veci_begin_which_implies_wit_1
  left
  intro xs v
  unfold store_veci veci_raw veci_header veci_buffer
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro buf
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro cap
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption


theorem proof_of_veci_size_return_wit_1_split_goal_spatial : veci_size_return_wit_1_split_goal_spatial := by
  unfold veci_size_return_wit_1_split_goal_spatial
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  unfold store_veci
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  unfold veci_raw veci_header veci_buffer
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨PreH5, PreH6, PreH7, PreH8, PreH9, PreH10, PreH11⟩


theorem proof_of_veci_size_return_wit_1 : veci_size_return_wit_1 := by
  unfold veci_size_return_wit_1
  right
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact proof_of_veci_size_return_wit_1_split_goal_spatial v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_veci_size_which_implies_wit_1 : veci_size_which_implies_wit_1 := by
  unfold veci_size_which_implies_wit_1
  left
  intro xs v
  unfold store_veci veci_raw veci_header veci_buffer
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro buf
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro cap
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption


theorem proof_of_veci_resize_return_wit_1_split_goal_spatial : veci_resize_return_wit_1_split_goal_spatial := by
  unfold veci_resize_return_wit_1_split_goal_spatial
  intro k_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  unfold veci_raw veci_header veci_buffer
  have hlen : Zlength (sublist 0 k_pre xs) = k_pre := by
    simpa only [Int.sub_zero] using ListLib.Zlength_sublist 0 k_pre xs (by omega) PreH13
  rw [hlen]
  sep_apply (veci_buffer_truncate__resize_prefix buf xs cap k_pre ⟨PreH12, PreH13⟩ PreH8)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨PreH5, PreH6, PreH12, by omega, PreH9, PreH10, PreH11⟩


theorem proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1 := by
  unfold veci_resize_return_wit_1
  right
  intro k_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact proof_of_veci_resize_return_wit_1_split_goal_spatial k_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_1 : veci_resize_which_implies_wit_1_split_goal_1 := by
  unfold veci_resize_which_implies_wit_1_split_goal_1
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact halloc


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_2 : veci_resize_which_implies_wit_1_split_goal_2 := by
  unfold veci_resize_which_implies_wit_1_split_goal_2
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hmax


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_3 : veci_resize_which_implies_wit_1_split_goal_3 := by
  unfold veci_resize_which_implies_wit_1_split_goal_3
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact h4


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_4 : veci_resize_which_implies_wit_1_split_goal_4 := by
  unfold veci_resize_which_implies_wit_1_split_goal_4
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hcap


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_5 : veci_resize_which_implies_wit_1_split_goal_5 := by
  unfold veci_resize_which_implies_wit_1_split_goal_5
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact h0


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_6 : veci_resize_which_implies_wit_1_split_goal_6 := by
  unfold veci_resize_which_implies_wit_1_split_goal_6
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hbuf


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_7 : veci_resize_which_implies_wit_1_split_goal_7 := by
  unfold veci_resize_which_implies_wit_1_split_goal_7
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hv


theorem proof_of_veci_resize_which_implies_wit_1_split_goal_spatial : veci_resize_which_implies_wit_1_split_goal_spatial := by
  unfold veci_resize_which_implies_wit_1_split_goal_spatial
  intro cap buf xs v
  unfold veci_raw
  Intros_p hraw
  unfold veci_header veci_buffer
  cancel


theorem proof_of_veci_resize_which_implies_wit_1 : veci_resize_which_implies_wit_1 := by
  unfold veci_resize_which_implies_wit_1
  right
  intro cap buf xs v
  split_pure_spatial
  · exact proof_of_veci_resize_which_implies_wit_1_split_goal_spatial cap buf xs v
  · split_pures
    all_goals first
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_1 cap buf xs v
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_2 cap buf xs v
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_3 cap buf xs v
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_4 cap buf xs v
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_5 cap buf xs v
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_6 cap buf xs v
      | exact proof_of_veci_resize_which_implies_wit_1_split_goal_7 cap buf xs v


theorem proof_of_veci_push_entail_wit_1_2_split_goal_1 : veci_push_entail_wit_1_2_split_goal_1 := by
  unfold veci_push_entail_wit_1_2_split_goal_1
  intro v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro h
  exact ⟨rfl, rfl⟩


theorem proof_of_veci_push_entail_wit_1_2_split_goal_2 : veci_push_entail_wit_1_2_split_goal_2 := by
  unfold veci_push_entail_wit_1_2_split_goal_2
  intro v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  omega


theorem proof_of_veci_push_entail_wit_1_2 : veci_push_entail_wit_1_2 := by
  unfold veci_push_entail_wit_1_2
  right
  intro v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_veci_push_entail_wit_1_2_split_goal_1 v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_veci_push_entail_wit_1_2_split_goal_2 v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10


theorem proof_of_veci_push_partial_solve_wit_2_pure_split_goal_1 : veci_push_partial_solve_wit_2_pure_split_goal_1 := by
  unfold veci_push_partial_solve_wit_2_pure_split_goal_1
  intro e_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hg := (PreH18 PreH9).1.1
  obtain ⟨hstride, hcap, htwice, hnew, halloc, haddr⟩ := hg
  have he : cap * 2 + 1 = 2 * cap + 1 := by omega
  dump_pre_spatial
  unfold vec_alloc_ok
  rw [he]
  exact ⟨hstride, by omega, halloc⟩


theorem proof_of_veci_push_partial_solve_wit_2_pure : veci_push_partial_solve_wit_2_pure := by
  unfold veci_push_partial_solve_wit_2_pure
  right
  intro e_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact proof_of_veci_push_partial_solve_wit_2_pure_split_goal_1 e_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18


theorem proof_of_veci_push_which_implies_wit_1_split_goal_1 : veci_push_which_implies_wit_1_split_goal_1 := by
  unfold veci_push_which_implies_wit_1_split_goal_1
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_1 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_2 : veci_push_which_implies_wit_1_split_goal_2 := by
  unfold veci_push_which_implies_wit_1_split_goal_2
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_2 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_3 : veci_push_which_implies_wit_1_split_goal_3 := by
  unfold veci_push_which_implies_wit_1_split_goal_3
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_3 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_4 : veci_push_which_implies_wit_1_split_goal_4 := by
  unfold veci_push_which_implies_wit_1_split_goal_4
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_4 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_5 : veci_push_which_implies_wit_1_split_goal_5 := by
  unfold veci_push_which_implies_wit_1_split_goal_5
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_5 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_6 : veci_push_which_implies_wit_1_split_goal_6 := by
  unfold veci_push_which_implies_wit_1_split_goal_6
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_6 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_7 : veci_push_which_implies_wit_1_split_goal_7 := by
  unfold veci_push_which_implies_wit_1_split_goal_7
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_7 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1_split_goal_spatial : veci_push_which_implies_wit_1_split_goal_spatial := by
  unfold veci_push_which_implies_wit_1_split_goal_spatial
  intro cap buf xs v
  exact proof_of_veci_resize_which_implies_wit_1_split_goal_spatial cap buf xs v


theorem proof_of_veci_push_which_implies_wit_1 : veci_push_which_implies_wit_1 := by
  unfold veci_push_which_implies_wit_1
  right
  intro cap buf xs v
  split_pure_spatial
  · exact proof_of_veci_push_which_implies_wit_1_split_goal_spatial cap buf xs v
  · split_pures
    all_goals first
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_1 cap buf xs v
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_2 cap buf xs v
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_3 cap buf xs v
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_4 cap buf xs v
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_5 cap buf xs v
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_6 cap buf xs v
      | exact proof_of_veci_push_which_implies_wit_1_split_goal_7 cap buf xs v


theorem proof_of_veci_push_which_implies_wit_2 : veci_push_which_implies_wit_2 := by
  unfold veci_push_which_implies_wit_2
  left
  intro v_pre cap buf xs curcap_2 curbuf_2 e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine Automation.exp_right_rule (CRules := naive_C_Rules) curbuf_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) curcap_2 ?_
  unfold veci_raw veci_header veci_buffer
  have hlen : Zlength (xs ++ [e]) = Zlength xs + 1 := by simp [Zlength]
  have hnonneg : 0 ≤ Zlength xs := by simp [Zlength]
  rw [hlen]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact ⟨PreH1, PreH2, by omega, by omega, PreH3, PreH4, PreH5⟩
      | exact vec_push_result_from_branches__push_final (Zlength xs) buf cap curbuf_2 curcap_2 PreH6 PreH7 PreH8 PreH9


theorem proof_of_vecp_new_return_wit_1 : vecp_new_return_wit_1 := by
  unfold vecp_new_return_wit_1
  left
  intro v_pre retval PreH1 PreH2 PreH3
  refine Automation.exp_right_rule (CRules := naive_C_Rules) retval ?_
  unfold vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  simp only [show Zlength ([] : List Int) = 0 from rfl]
  have he : ptrArray.undef_full retval 4 = ptrArray.undef_seg retval 0 4 := rfl
  rw [he]
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (ptrArray.full_empty retval 0)).2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact ⟨PreH3, PreH1, by omega, by omega, by omega, by decide, PreH2⟩
      | rfl


theorem proof_of_vecp_new_which_implies_wit_1 : vecp_new_which_implies_wit_1 := by
  unfold vecp_new_which_implies_wit_1
  left
  intro v
  unfold vecp_shell
  Intros_p hneq
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hneq


theorem proof_of_vecp_delete_return_wit_1_split_goal_spatial : vecp_delete_return_wit_1_split_goal_spatial := by
  unfold vecp_delete_return_wit_1_split_goal_spatial
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  unfold vecp_shell
  split_pure_spatial
  · sep_apply (store_int_undef_store_int naive_C_Rules (&((v_pre # "vecp_t") ->ₛ "size")) (Zlength xs))
    sep_apply (store_int_undef_store_int naive_C_Rules (&((v_pre # "vecp_t") ->ₛ "cap")) cap)
    sep_apply (store_ptr_undef_store_ptr naive_C_Rules (&((v_pre # "vecp_t") ->ₛ "ptr")) buf)
    cancel
  · dump_pre_spatial
    exact PreH5


theorem proof_of_vecp_delete_return_wit_1 : vecp_delete_return_wit_1 := by
  unfold vecp_delete_return_wit_1
  right
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact proof_of_vecp_delete_return_wit_1_split_goal_spatial v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_vecp_delete_which_implies_wit_1 : vecp_delete_which_implies_wit_1 := by
  unfold vecp_delete_which_implies_wit_1
  left
  intro xs v
  unfold store_vecp vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro buf
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro cap
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption


theorem proof_of_vecp_begin_return_wit_1 : vecp_begin_return_wit_1 := by
  unfold vecp_begin_return_wit_1
  left
  intro v_pre xs cap_2 buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap_2 ?_
  unfold vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨PreH1, PreH2, PreH3, PreH4, PreH5, PreH6, PreH7⟩


theorem proof_of_vecp_begin_which_implies_wit_1 : vecp_begin_which_implies_wit_1 := by
  unfold vecp_begin_which_implies_wit_1
  left
  intro xs v
  unfold store_vecp vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro buf
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro cap
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption


theorem proof_of_vecp_size_return_wit_1_split_goal_spatial : vecp_size_return_wit_1_split_goal_spatial := by
  unfold vecp_size_return_wit_1_split_goal_spatial
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  unfold store_vecp
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  unfold vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨PreH5, PreH6, PreH7, PreH8, PreH9, PreH10, PreH11⟩


theorem proof_of_vecp_size_return_wit_1 : vecp_size_return_wit_1 := by
  unfold vecp_size_return_wit_1
  right
  intro v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact proof_of_vecp_size_return_wit_1_split_goal_spatial v_pre xs cap buf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_vecp_size_which_implies_wit_1 : vecp_size_which_implies_wit_1 := by
  unfold vecp_size_which_implies_wit_1
  left
  intro xs v
  unfold store_vecp vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro buf
  refine Automation.exp_left_rule (CRules := naive_C_Rules) ?_
  intro cap
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cap ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buf ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption


theorem proof_of_vecp_resize_return_wit_1_split_goal_spatial : vecp_resize_return_wit_1_split_goal_spatial := by
  unfold vecp_resize_return_wit_1_split_goal_spatial
  intro k_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  unfold vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  have hlen : Zlength (sublist 0 k_pre xs) = k_pre := by
    simpa only [Int.sub_zero] using ListLib.Zlength_sublist 0 k_pre xs (by omega) PreH13
  rw [hlen]
  sep_apply (vecp_buffer_truncate__resize_prefix buf xs cap k_pre ⟨PreH12, PreH13⟩ PreH8)
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨PreH5, PreH6, PreH12, by omega, PreH9, PreH10, PreH11⟩


theorem proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1 := by
  unfold vecp_resize_return_wit_1
  right
  intro k_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact proof_of_vecp_resize_return_wit_1_split_goal_spatial k_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_1 : vecp_resize_which_implies_wit_1_split_goal_1 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_1
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact halloc


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_2 : vecp_resize_which_implies_wit_1_split_goal_2 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_2
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hmax


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_3 : vecp_resize_which_implies_wit_1_split_goal_3 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_3
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact h4


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_4 : vecp_resize_which_implies_wit_1_split_goal_4 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_4
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hcap


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_5 : vecp_resize_which_implies_wit_1_split_goal_5 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_5
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact h0


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_6 : vecp_resize_which_implies_wit_1_split_goal_6 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_6
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hbuf


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_7 : vecp_resize_which_implies_wit_1_split_goal_7 := by
  unfold vecp_resize_which_implies_wit_1_split_goal_7
  intro cap buf xs v
  unfold vecp_raw
  simp only [ptr_size_Z_eq_sizeof]
  Intros_p hraw
  obtain ⟨hv, hbuf, h0, hcap, h4, hmax, halloc⟩ := hraw
  dump_pre_spatial
  exact hv


theorem proof_of_vecp_resize_which_implies_wit_1_split_goal_spatial : vecp_resize_which_implies_wit_1_split_goal_spatial := by
  unfold vecp_resize_which_implies_wit_1_split_goal_spatial
  intro cap buf xs v
  unfold vecp_raw
  Intros_p hraw
  unfold vecp_header vecp_buffer
  cancel


theorem proof_of_vecp_resize_which_implies_wit_1 : vecp_resize_which_implies_wit_1 := by
  unfold vecp_resize_which_implies_wit_1
  right
  intro cap buf xs v
  split_pure_spatial
  · exact proof_of_vecp_resize_which_implies_wit_1_split_goal_spatial cap buf xs v
  · split_pures
    all_goals first
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_1 cap buf xs v
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_2 cap buf xs v
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_3 cap buf xs v
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_4 cap buf xs v
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_5 cap buf xs v
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_6 cap buf xs v
      | exact proof_of_vecp_resize_which_implies_wit_1_split_goal_7 cap buf xs v


theorem proof_of_vecp_push_entail_wit_1_2_split_goal_1 : vecp_push_entail_wit_1_2_split_goal_1 := by
  unfold vecp_push_entail_wit_1_2_split_goal_1
  intro v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro h
  exact ⟨rfl, rfl⟩


theorem proof_of_vecp_push_entail_wit_1_2_split_goal_2 : vecp_push_entail_wit_1_2_split_goal_2 := by
  unfold vecp_push_entail_wit_1_2_split_goal_2
  intro v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  omega


theorem proof_of_vecp_push_entail_wit_1_2 : vecp_push_entail_wit_1_2 := by
  unfold vecp_push_entail_wit_1_2
  right
  intro v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_vecp_push_entail_wit_1_2_split_goal_1 v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_vecp_push_entail_wit_1_2_split_goal_2 v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10


theorem proof_of_vecp_push_partial_solve_wit_2_pure_split_goal_1 : vecp_push_partial_solve_wit_2_pure_split_goal_1 := by
  unfold vecp_push_partial_solve_wit_2_pure_split_goal_1
  intro e_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hg := (PreH16 PreH7).1.1
  obtain ⟨hstride, hcap, htwice, hnew, halloc, haddr⟩ := hg
  have he : cap * 2 + 1 = 2 * cap + 1 := by omega
  dump_pre_spatial
  unfold vec_alloc_ok
  rw [he]
  exact ⟨hstride, by omega, halloc⟩


theorem proof_of_vecp_push_partial_solve_wit_2_pure : vecp_push_partial_solve_wit_2_pure := by
  unfold vecp_push_partial_solve_wit_2_pure
  right
  intro e_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact proof_of_vecp_push_partial_solve_wit_2_pure_split_goal_1 e_pre v_pre cap buf xs PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_1 : vecp_push_which_implies_wit_1_split_goal_1 := by
  unfold vecp_push_which_implies_wit_1_split_goal_1
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_1 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_2 : vecp_push_which_implies_wit_1_split_goal_2 := by
  unfold vecp_push_which_implies_wit_1_split_goal_2
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_2 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_3 : vecp_push_which_implies_wit_1_split_goal_3 := by
  unfold vecp_push_which_implies_wit_1_split_goal_3
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_3 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_4 : vecp_push_which_implies_wit_1_split_goal_4 := by
  unfold vecp_push_which_implies_wit_1_split_goal_4
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_4 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_5 : vecp_push_which_implies_wit_1_split_goal_5 := by
  unfold vecp_push_which_implies_wit_1_split_goal_5
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_5 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_6 : vecp_push_which_implies_wit_1_split_goal_6 := by
  unfold vecp_push_which_implies_wit_1_split_goal_6
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_6 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_7 : vecp_push_which_implies_wit_1_split_goal_7 := by
  unfold vecp_push_which_implies_wit_1_split_goal_7
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_7 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1_split_goal_spatial : vecp_push_which_implies_wit_1_split_goal_spatial := by
  unfold vecp_push_which_implies_wit_1_split_goal_spatial
  intro cap buf xs v
  exact proof_of_vecp_resize_which_implies_wit_1_split_goal_spatial cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_1 : vecp_push_which_implies_wit_1 := by
  unfold vecp_push_which_implies_wit_1
  right
  intro cap buf xs v
  split_pure_spatial
  · exact proof_of_vecp_push_which_implies_wit_1_split_goal_spatial cap buf xs v
  · split_pures
    all_goals first
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_1 cap buf xs v
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_2 cap buf xs v
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_3 cap buf xs v
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_4 cap buf xs v
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_5 cap buf xs v
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_6 cap buf xs v
      | exact proof_of_vecp_push_which_implies_wit_1_split_goal_7 cap buf xs v


theorem proof_of_vecp_push_which_implies_wit_2 : vecp_push_which_implies_wit_2 := by
  unfold vecp_push_which_implies_wit_2
  left
  intro v_pre cap buf xs curcap_2 curbuf_2 e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine Automation.exp_right_rule (CRules := naive_C_Rules) curbuf_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) curcap_2 ?_
  unfold vecp_raw vecp_header vecp_buffer
  simp only [ptr_size_Z_eq_sizeof]
  have hlen : Zlength (xs ++ [e]) = Zlength xs + 1 := by simp [Zlength]
  have hnonneg : 0 ≤ Zlength xs := by simp [Zlength]
  rw [hlen]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact ⟨PreH1, PreH2, by omega, by omega, PreH3, PreH4, PreH5⟩
      | exact vec_push_result_from_branches__push_final (Zlength xs) buf cap curbuf_2 curcap_2 PreH6 PreH7 PreH8 PreH9

end SimpleC.EE.LLM_bench.Engineering.minisat.vec_proof_manual
