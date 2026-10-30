From SimpleC.Verification Require Import VCPrelude.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.


Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.

Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part7.

Lemma proof_of_assume_entail_wit_1 : assume_entail_wit_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst. match goal with H : enqueue_input _ _ _ _ _ _ _ |- _ => pose proof H as Hin; unfold enqueue_input in Hin end. msat_manual_entailer_with ltac:(intuition lia).
Qed.


Lemma proof_of_enqueue_partial_solve_wit_2_pure : enqueue_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold enqueue_input, lit_wf_c in PreH11.
  subst l_pre; entailer!; lia.
Qed.


Lemma proof_of_solver_addclause_entail_wit_7_4 : solver_addclause_entail_wit_7_4.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.


Lemma proof_of_solver_addclause_entail_wit_7_5 : solver_addclause_entail_wit_7_5.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_50_pure : solver_addclause_partial_solve_wit_50_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_addclause_sort_cursor_close.
Qed.


Lemma proof_of_solver_addclause_return_wit_4_split_goal_spatial : solver_addclause_return_wit_4_split_goal_spatial.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { intros rho HF.
    eapply addclause_dedup_complement;
      [eassumption | exact Hin | ac_arith | rewrite ?Z.sub_0_r in *; congruence]. }
  msat_addclause_entailed_return Mnew kept tail Hent.

all: try solve [msat_manual_entailer_with ltac:(reflexivity || lia)].
Qed.


Lemma proof_of_solver_addclause_return_wit_4 : solver_addclause_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_addclause_return_wit_4_split_goal_spatial.
Qed.


Lemma proof_of_solver_addclause_return_wit_5_split_goal_spatial : solver_addclause_return_wit_5_split_goal_spatial.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { intros rho HF.
    eapply addclause_dedup_complement;
      [eassumption | exact Hin | ac_arith | rewrite ?Z.sub_0_r in *; congruence]. }
  msat_addclause_entailed_return Mnew kept tail Hent.

all: try solve [msat_manual_entailer_with ltac:(reflexivity || lia)].
Qed.


Lemma proof_of_solver_addclause_return_wit_5 : solver_addclause_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_addclause_return_wit_5_split_goal_spatial.
Qed.


Lemma proof_of_solver_canceluntil_safety_wit_5 : solver_canceluntil_safety_wit_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_canceluntil_which_implies_wit_5 : solver_canceluntil_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( cancel_reinsert_loop_inv M0 level c assigns_now reasons_now order_now orderpos_now ) as
      H_cancel_reinsert_loop_inv.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  assert (Hlev : 0 <= level < Zlength (mt_lim (ms_core M0))) by tauto.
  pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level H_mtrail_wf Hlev)
    as Hbound.
  pose proof (mtw_qhead_range H_mtrail_wf) as Hqhead.
  assert (Hcrange : 0 <= c < Zlength (mt_trail (ms_core M0))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 c (mtw_trail_lits H_mtrail_wf) Hcrange)
    as Hlit.
  pose proof (lit_var_c_in_range (ms_size M0)
    (Znth c (mt_trail (ms_core M0)) 0) Hlit) as Hvar.
  unfold lit_wf_c in Hlit.
  unfold solver_shape in H_solver_shape.
  unfold order_unassigned_pre, order_heap_wf, heap_of_lists.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_record_which_implies_wit_5 : solver_record_which_implies_wit_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
pose proof PreH2 as Halloc. pose proof PreH3 as Hsuccess.
 destruct Hsuccess as [Henq Hrest].
 destruct Halloc as [[[Hlen [Hzero Heq]]|[Hlen [Hne [Hfresh [Hinstall Htail]]]]] _]; [congruence|].
 assert (Hdb : db_words (ms_learnt Menq) = db_words (ms_learnt M0) ++ (c :: nil)).
 { rewrite Henq. change (db_words (ms_learnt Mstage) = db_words (ms_learnt M0) ++ (c :: nil)).
   rewrite Hinstall.
   unfold msolver_install_learnt_clause, db_words;
   cbn [msolver_install_clause msolver_propagation_overlay msolver_propagation_update ms_learnt];
   rewrite map_app; reflexivity. }
 unfold solver_record_rep_at, clause_new_frame_at.
 Intros act asg opos rsn trl tgs.
 unfold solver_record_finish_frame_at. Exists act asg opos rsn trl tgs.
 unfold clause_new_scalars_frame, solver_vecs_without_learnts_rep, clause_new_ptrs_frame, solver_scalars_rep,
 solver_fp_rep, solver_ptrs_rep, solver_wlists_handle, stats_rep, stats_record_frame, db_words.
 split_pure_spatial.
 - Intros. msat_cancel_sound. csimpl. msat_manual_entailer_with ltac:(lia || tauto).
 - split_pures; dump_pre_spatial.
   + exact PreH1.
   + exact PreH2.
   + exact PreH3.
   + exact PreH4.
   + exact Hdb.
   + exact H.
Qed.


Lemma proof_of_solver_search_entail_wit_4_1 : solver_search_entail_wit_4_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). unfold solver_simplify_post_at, solver_simplify_post_sat_at, solver_simplify_post_unsat_at in *.
    Split.
- Intros Mclean. (repeat split; solve [auto | (lia)]).
- Intros Mclean. (repeat split; solve [auto | (lia)]).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_50_pure : solver_search_partial_solve_wit_50_pure.
Proof.
  msat_search_cla_inc_nonneg H_msolver_inv n F A_arr A_inst Mrecord.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_103_pure : solver_search_partial_solve_wit_103_pure.
Proof.
msat_search_decision_lit_var_entail.
Qed.


Lemma proof_of_solver_search_safety_wit_19 : solver_search_safety_wit_19.
Proof.
msat_search_safety_qtail_gap.
Qed.



Lemma proof_of_solver_search_which_implies_wit_19 : solver_search_which_implies_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_rep_levels_wl_at, solver_cancel_owned,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_search_decay_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_fp_rep,
    solver_fp_without_decay_incs_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(assumption).
Qed.


Lemma proof_of_solver_search_which_implies_wit_43 : solver_search_which_implies_wit_43.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_selection_state n F A_arr A_inst next Mselected ) as H_solver_search_selection_state.
  bind_fact ( enqueue_input n (lit_neg_c (next + next)) (ms_qtail Mselected) (mt_assigns (ms_core Mselected))
    (mt_levels (ms_core Mselected)) (ms_reason_words Mselected) (mt_trail (ms_core Mselected)) ) as H_enqueue_input.
  assert (Hdecision : decision_lit = lit_neg_c (next + next)) by lia.
  subst decision_lit.
  pose proof H_solver_search_selection_state as Hsel.
  unfold solver_search_selection_state in Hsel.
  destruct Hsel as
    (Hweak & Hprop & Hwatch & Hreasonless & Hpending & Hdrain &
     Hseed & Hmodel & Hdecay & Htwice & Hnext & Hfresh & Hheap).
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_size Hweak) as Hsize.
  pose proof H_enqueue_input as Henq.
  unfold enqueue_input in Henq.
  destruct Henq as [Hlit [Htwice' [Haslen [Hlvlen [Hrslen
    [Htrlen [Hqrange [Hroom Hcells]]]]]]]].
  assert (Hvar : lit_var_c (lit_neg_c (next + next)) = next).
  { rewrite lit_var_c_neg. unfold lit_var_c.
    replace (next + next) with (next * 2) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hfreshl :
      Znth (lit_var_c (lit_neg_c (next + next)))
        (mt_assigns (ms_core Mselected)) 0 = 0).
  { rewrite Hvar. exact Hfresh. }
  assert (Hroomcap : ms_qtail Mselected < ms_cap Mselected).
  { specialize (Hroom Hfreshl). unfold solver_shape in Hshape. lia. }
  sep_apply (assume_post_refold__search
    search_wl s decision_asg levels (lit_neg_c (next + next))
    n (ms_cap Mselected) (ms_qtail Mselected)
    (mt_assigns (ms_core Mselected)) (mt_levels (ms_core Mselected))
    (ms_reason_words Mselected) (mt_trail (ms_core Mselected))
    (mt_lim (ms_core Mselected)) Mselected
    Hsize ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity)
    Hshape Hroomcap Hpending Hdrain Hfreshl).
  assert (Hcap_decision : ms_cap
    (msolver_assume Mselected (lit_neg_c (next + next))) =
    ms_cap Mselected) by reflexivity.
  lazymatch goal with
  | Hreuse : solver_search_reuse ?entry Mselected |- _ =>
      assert (Hreuse_decision : solver_search_reuse entry
        (msolver_assume Mselected (lit_neg_c (next + next))))
      by (intro Hbase;
          apply (minisat_base_watch_completed_assume__api_reentry
            n Mselected (lit_neg_c (next + next))
            (msw_db_wf Hweak) (msw_trail_wf Hweak) Hlit Hfreshl);
          exact (Hreuse Hbase))
  end.
  Exists (msolver_assume Mselected (lit_neg_c (next + next))).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + lia.
    + exact Hreuse_decision.
    + eapply solver_search_decision_pure__search; eauto.
    + exact Hdecay.
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_5_pure : solver_setnvars_partial_solve_wit_5_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_safety_wit_4 : solver_setnvars_safety_wit_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia).
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_6_split_goal_spatial : solver_setnvars_which_implies_wit_6_split_goal_spatial.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); snv_shape;
  sep_apply (dseg_snoc (ms_activity Mcur) actc 0 var (Z_to_fp64 0) ltac:(lia));
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_6 : solver_setnvars_which_implies_wit_6.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_setnvars_which_implies_wit_6_split_goal_spatial Mcur actc var PreH1 PreH2).
Qed.


Lemma proof_of_solver_simplify_entail_wit_2_2_split_goal_1 : solver_simplify_entail_wit_2_2_split_goal_1.
Abort.


Lemma proof_of_solver_simplify_entail_wit_2_2 : solver_simplify_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!; rewrite PreH12; rewrite sel_vec_prob; cancel.
Qed.


Lemma proof_of_solver_simplify_return_wit_1_split_goal_spatial : solver_simplify_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_simplify_finish_transition smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mdone
      (MiniSatTarget.uint64_sum_to_int (stats_clauses_literals (ms_stats Mdone))
        (stats_learnts_literals (ms_stats Mdone))) Mfinish ) as H_solver_simplify_finish_transition.
  bind_fact ( ms_model M_solver_simplify_spec = nil -> ms_model Mdone = nil ) as H_model_empty.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
    msat_fp32_positive_finite (ms_cla_decay Mdone) ) as H_decay_positive.
  unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at.
  Left.
  apply split_pure_and_spatial_goals.
  2: { dump_pre_spatial. reflexivity. }
  Exists Mfinish.
  unfold solver_simplify_finish_transition in H_solver_simplify_finish_transition.
  destruct H_solver_simplify_finish_transition as [Hfinish [Hinv [Hlim [Hqhead [Hpending [Hseed [Hmodel Hdecay]]]]]]].
  bind_fact (solver_simplify_reuse M_solver_simplify_spec Mdone) as Hreuse.
  assert (Hreuse_finish : solver_simplify_reuse M_solver_simplify_spec Mfinish).
  { rewrite Hfinish. exact Hreuse. }
  assert (Hcap_finish : ms_cap Mfinish = ms_cap Mdone).
  { rewrite Hfinish. reflexivity. }
  assert (Hroot_finish : ms_root_level Mfinish = ms_root_level Mdone).
  { rewrite Hfinish. reflexivity. }
  unfold msat_fp32_same in *.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    split; [exact PreH1 |].
    split; [exact PreH2 |].
    split; [exact Hinv |].
    split; [exact Hreuse_finish |].
    split; [exact Hlim |].
    split; [exact Hqhead |].
    split; [exact Hpending |].
    split; [exact Hseed |].
    split.
    + intro Hempty. rewrite Hmodel. exact (H_model_empty Hempty).
    + intro Hpositive. rewrite Hdecay. exact (H_decay_positive Hpositive).
Qed.


Lemma proof_of_solver_simplify_return_wit_1 : solver_simplify_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_simplify_return_wit_1_split_goal_spatial.
Qed.


Lemma proof_of_solver_simplify_safety_wit_18 : solver_simplify_safety_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Vecp.rep_ptr_bounds cs cls words_next).
  Intros.
  split_pures.
  - dump_pre_spatial.
    unfold solver_simplify_compaction_step, solver_simplify_db_compaction_inv in *.
    lia.
  - dump_pre_spatial.
    unfold solver_simplify_compaction_step, solver_simplify_db_compaction_inv in *.
    lia.
Qed.



Lemma proof_of_solver_simplify_which_implies_wit_1 : solver_simplify_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply solver_simplify_pre_split__simplify.
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_2 : solver_simplify_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply solver_simplify_lim_join_rep_levels__simplify.
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_3 : solver_simplify_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply solver_rep_levels_assigns_split__simplify.
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_8 : solver_simplify_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply solver_simplify_control_join_rep_reasons__simplify.
  cancel.
Qed.


Lemma proof_of_solver_solve_entail_wit_4_3 : solver_solve_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  msat_solve_lbool_cell_arm Mcur retval_5.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_16_pure : solver_solve_partial_solve_wit_16_pure.
Proof.
  msat_solve_close_assumption_lit_bounds k.
Qed.


Lemma proof_of_solver_solve_return_wit_1 : solver_solve_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_sat_arm_at. Intros.
  assert (Hsaved : ms_size Msat_2 = n_solver_solve_spec /\
    model_saved n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec Msat_2)
    by tauto.
  apply (proj1 (sat_arm_unfolded_iff n_solver_solve_spec F_solver_solve_spec
    A_arr_solver_solve_spec Msat_2)) in Hsaved.
  Exists Msat_2. msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_safety_wit_4 : solver_solve_safety_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_solve_close_assign_cell_not_int_min PreH27 raw k Mcur retval.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_9 : solver_solve_which_implies_wit_9.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold assumption_fresh_transition in PreH1. destruct PreH1 as (_ & Hinv & Hseed). msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_simplify_partial_solve_wit_33_pure : solver_simplify_partial_solve_wit_33_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_simplify_partial_solve_wit_34_pure : solver_simplify_partial_solve_wit_34_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.
