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
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part5.

Lemma proof_of_solver_addclause_entail_wit_7_6 : solver_addclause_entail_wit_7_6.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_3 : solver_addclause_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_split_after_llm;
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_new_return_wit_1 : solver_new_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists M_2.
  assert (Hflag : ms_capacity_root_propagation_pending M_2 = 0)
    by (destruct PreH4 as [_ [_ [_ [_ Hflag]]]]; exact Hflag).
  pose proof (solver_normal_root_query_ready__solve 0 cnf_nil M_2 PreH4)
    as Hready.
  pose proof (solver_query_update_ready__incremental_public 0 cnf_nil M_2 Hready)
    as Hupdate.
  unfold solver_incremental_ownership_at.
  msat_entailer_with ltac:(tauto || lia).
Qed.


Lemma proof_of_solver_new_which_implies_wit_4 : solver_new_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply solver_initial_layout_result. Intros M.
  Exists M. unfold cnf_nil.
  unfold solver_rep_growable at 1.
  Intros wl act asg opos rsn lvl trl tgs.
  split_pure_spatial.
  - unfold solver_rep_growable.
    Exists wl act asg opos rsn lvl trl tgs.
    msat_entailer_with ltac:(tauto).
  - split_pures; dump_pre_spatial; tauto.
Qed.


Lemma proof_of_solver_record_entail_wit_1_1 : solver_record_entail_wit_1_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst.
 sep_apply (record_pending_install s_pre learnt_ptr levels_ptr rec_n rec_F rec_A_arr rec_A_inst M0 rec_words retval rec_wl ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
 Intros Mstage.
 sep_apply (Veci.rep_ptr_intro cls_pre learnt_ptr rec_words cap);
   [ | first [reflexivity | lia | vec_buf_solve] .. ].
 Exists Mstage.
 split_pure_spatial.
 - sep_apply (store_ptr_undef_store_ptr (&( "endvar")) (learnt_ptr + Zlength rec_words * sizeof ( INT ))).
   cancel.
 - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.



Lemma proof_of_solver_search_entail_wit_2_2_split_goal_1 : solver_search_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( ms_root_level Manalyzed <= Znth (retval_5 - 0) (mt_levels (ms_core Manalyzed)) 0 ) as H_ms_root_level.
  bind_fact ( retval_5 = lit_var_c (Znth (1 - 0) words 0) ) as H_retval_5.
  bind_fact ( analyze_backjump_cert n Manalyzed words backjump ) as H_analyze_backjump_cert.
  unfold analyze_backjump_cert in H_analyze_backjump_cert.
  destruct H_analyze_backjump_cert as [_ [Hback _]].
  assert (Hlt : Z.ltb 1 (Zlength words) = true).
  { apply Z.ltb_lt. lia. }
  rewrite Hlt in Hback.
  rewrite H_retval_5 in H_ms_root_level.
  rewrite H_retval_5.
  replace (1 - 0) with 1 by lia.
  replace (lit_var_c (Znth 1 words 0) - 0)
    with (lit_var_c (Znth 1 words 0)) by lia.
  rewrite Hback.
  replace (1 - 0) with 1 in H_ms_root_level by lia.
  replace (lit_var_c (Znth 1 words 0) - 0)
    with (lit_var_c (Znth 1 words 0)) in H_ms_root_level by lia.
  symmetry.
  apply Z.max_r.
  lia.
Qed.


Lemma proof_of_solver_search_entail_wit_2_2 : solver_search_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_search_entail_wit_2_2_split_goal_1.
Qed.



Lemma proof_of_solver_search_which_implies_wit_10 : solver_search_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationStable A_inst) Mconf focus ) as H_propagation_cancel_ready.
  bind_fact ( propagation_conflict_cert n F Mconf Cconf ) as H_propagation_conflict_cert.
  bind_fact ( ms_model Mconf = nil ) as H_ms_model.
  unfold solver_search_conflict_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  Intros act asg opos rsn trl tgs.
  assert (Hsw : solver_propagation_weak n F A_arr
      (PropagationStable A_inst) Mconf) by exact (proj1 H_propagation_cancel_ready).
  assert (Hpending : ms_capacity_root_propagation_pending Mconf = 0)
    by exact (proj1 Hsw).
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mconf)
    by exact (proj2 Hsw).
  assert (Hlevel : prop_level (ms_core Mconf))
    by exact (proj1 (proj2 H_propagation_cancel_ready)).
  assert (Hroot : solver_at_root Mconf).
  { unfold solver_at_root. lia. }
  assert (Hcancel : cancel_bound_ready Mconf 0).
  { unfold cancel_bound_ready.
    destruct (Z_le_dec (Zlength (mt_lim (ms_core Mconf))) 0) as [Hlen|Hlen].
    - left; exact Hlen.
    - right.
      assert (Hidx : 0 <= 0 < Zlength (mt_lim (ms_core Mconf))) by lia.
      exact (Forall_Znth_elim _ _ _ 0 0 Hlevel Hidx). }
  assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)).
  { eapply unsat_endgame_at_root.
    - exact Hweak.
    - exact Hroot.
    - exact (proj1 H_propagation_conflict_cert).
    - exact (proj1 (proj2 H_propagation_conflict_cert)).
    - exact (proj1 (proj2 (proj2 H_propagation_conflict_cert))). }
  set (Mrootconf :=
    msolver_with_cla_inc_stats Mconf (ms_cla_inc Mconf)
      (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  assert (Hshape_root : solver_shape Mrootconf).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn.
    pose proof (msw_shape Hweak) as Hshape.
    assert (Hstats_len :
        Zlength (replace_Znth 4 conflicts_now (ms_stats Mconf)) = 11).
    { rewrite Zlength_replace_Znth.
      unfold solver_shape in Hshape; tauto. }
    unfold solver_shape in Hshape |- *.
    tauto. }
  assert (Hweak_root : msolver_inv_weak n F A_arr A_inst Mrootconf).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn.
    destruct Hweak.
    constructor; try assumption. }
  assert (Hroot_root : solver_at_root Mrootconf).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact Hroot. }
  assert (Hcancel_root : cancel_bound_ready Mrootconf 0).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact Hcancel. }
  assert (Hpending_root : ms_capacity_root_propagation_pending Mrootconf = 0).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact Hpending. }
  assert (Hmodel_root : ms_model Mrootconf = @nil Z).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact H_ms_model. }
  bind_fact (msolver_seed_shadow Mconf) as Hseed_conf.
  bind_fact (minisat_resident_false_clause Mconf) as Hresident_conf.
  assert (Hready_root : propagation_cancel_ready n F A_arr
      (PropagationStable A_inst) Mrootconf focus).
  { unfold propagation_cancel_ready. split.
    - split; [exact Hpending_root | exact Hweak_root].
    - unfold Mrootconf, msolver_with_cla_inc_stats; cbn.
      exact (proj2 H_propagation_cancel_ready). }
  lazymatch goal with
  | Hwatch : minisat_base_watch_completed ?entry ->
      minisat_watch_conflict_ready n Mconf |- _ =>
      assert (Hreuse_root : minisat_base_watch_completed entry ->
          solver_search_conflict_reuse n F A_arr A_inst Mrootconf)
        by (intro Hbase; split;
            [change (msolver_seed_shadow Mconf); exact Hseed_conf |
             left; exists focus; split; [exact Hready_root |]; split;
             [change (minisat_watch_conflict_ready n Mconf); exact (Hwatch Hbase) |
              change (minisat_resident_false_clause Mconf); exact Hresident_conf]])
  end.
  assert (Hstats_base_len : Zlength (ms_stats Mconf) = 11).
  { pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape; tauto. }
  assert (Hstats_root_len :
      Zlength (replace_Znth 4 conflicts_now (ms_stats Mconf)) = 11).
  { rewrite Zlength_replace_Znth; exact Hstats_base_len. }
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hconflicts_addr :
      &(s # "solver_t" ->ₛ "stats" .ₛ "conflicts") =
      &(stats_ptr # "stats_t" ->ₛ "conflicts"))
    by (unfold stats_ptr; csimpl; reflexivity).
  assert (Hstats_refold :
      (&(stats_ptr # "stats_t" ->ₛ "conflicts") # UInt64
          |-> conflicts_now) **
      stats_without_conflicts_rep stats_ptr (ms_stats Mconf)
      |-- stats_rep stats_ptr
          (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  { unfold stats_without_conflicts_rep, stats_rep.
    unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
      stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
      stats_learnts_literals, stats_max_literals, stats_tot_literals.
    rewrite Zlength_replace_Znth.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite !Znth_replace_Znth_Diff by lia.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]). }
  Exists Mrootconf.
  unfold Mrootconf.
  rewrite scalars_rep_cla_inc_stats_eq, vecs_rep_cla_inc_stats_eq, fp_rep_cla_inc_stats_eq.
  unfold msolver_with_cla_inc_stats.
  cbn.
  Exists act asg opos rsn trl tgs.
  rewrite Hconflicts_addr.
  fold stats_ptr.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  sep_apply Hstats_refold.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_41 : solver_search_which_implies_wit_41.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_select_transition n F A_arr A_inst Mdb next orderpos_after order_after seed_after
    stats_after Mselected ) as H_solver_search_select_transition.
  bind_fact ( next <> -1 ) as H_next.
  unfold solver_search_select_transition in H_solver_search_select_transition.
  destruct H_solver_search_select_transition as (_ & _ & _ & _ & _ & [[Hret Hready] | Hselected]).
  - exfalso. apply H_next. exact Hret.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_entail_wit_3_1 : solver_setnvars_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  snv_shape.
  assert (Hsh0 : solver_shape sn_M_setnvars_spec) by (unfold solver_shape; tauto).
  (* The RHS folds the eight arrays into [setnvars_arrays_at], so the engine
     does not pin their addresses -- supply the eight grow returns in the
     bundle's own order (trail BEFORE tags) and dissolve the bundle before
     [snv_set_cap_proj], whose rewrites have to reach the projections the
     bundle body carries. *)
  Exists retval retval_2 retval_3 retval_4 retval_5 retval_6 retval_8 retval_7
         (msolver_set_cap sn_M_setnvars_spec actual_8).
  unfold setnvars_arrays_at.
  snv_set_cap_proj.
  rewrite setnvars_frame_at_set_cap.
  pose proof (solver_shape_set_cap sn_M_setnvars_spec actual_8 Hsh0
                ltac:(lia) ltac:(lia)).
  match goal with
  | H : solver_support_inv _ _ _ _ ?root ?M |- _ =>
      pose proof (solver_support_inv_set_cap__api_reentry
        _ _ _ _ root M actual_8 H ltac:(lia))
  end.
  pose proof (minisat_watch_completed_set_cap__api_reentry
    sn_M_setnvars_spec actual_8) as Hcompletion.
  pose proof (setnvars_core_equiv_set_cap sn_M_setnvars_spec actual_8).
  pose proof (setnvars_bound_entry (ms_size sn_M_setnvars_spec) n_pre).
  unfold solver_double_tail, solver_char_tail, solver_int_tail, solver_ptr_tail, solver_wlists_tail, solver_array_tail.
  Exists actual_2 actual_3 actual_4 actual_5 actual_6 actual_7 actual_8 (2*actual).
  sep_apply (store_int_undef_store_int &("new_cap") actual_8).
  msat_manual_entailer_with ltac:(snv_dispatch).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_12_pure : solver_setnvars_partial_solve_wit_12_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_safety_wit_5 : solver_setnvars_safety_wit_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia).
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_7 : solver_setnvars_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_setnvars_order_update_pre; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_entail_wit_3_2_split_goal_1 : solver_simplify_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_simplify_db_compaction_inv, db_words.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [apply Zlength_nonneg |].
  rewrite Zsublist_nil by lia. simpl.
  symmetry. apply sublist_self. reflexivity.
Qed.



Lemma proof_of_solver_simplify_entail_wit_3_2 : solver_simplify_entail_wit_3_2.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_simplify_entail_wit_3_2_split_goal_1 M_solver_simplify_spec smp_A_arr_solver_simplify_spec smp_F_solver_simplify_spec smp_n_solver_simplify_spec type words_type Mtype p retval).
Qed.



Lemma proof_of_solver_simplify_partial_solve_wit_38_pure : solver_simplify_partial_solve_wit_38_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite minisat_signed32_sum_cast_eq_uint64_sum_to_int.
  (Intros; split_pures; dump_pre_spatial; solve [auto | (reflexivity)]).
Qed.


Lemma proof_of_solver_simplify_safety_wit_19 : solver_simplify_safety_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_simplify_outer_loop.
  Intros Mnext.
  LLM_pre_process ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_5 : solver_simplify_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (msolver_inv_assuming_strong smp_n_solver_simplify_spec
    smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec M_solver_simplify_spec) as Hentry.
  bind_fact (Zlength (mt_lim (ms_core M_solver_simplify_spec)) = 0) as Hdepth.
  bind_fact (solver_propagation_inv smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec (PropagationAssuming smp_A_arr_solver_simplify_spec) propagation_result) as Hinv.
  bind_fact (propagation_caller_frame M_solver_simplify_spec propagation_result) as Hframe.
  bind_fact (minisat_propagation_reuse_live M_solver_simplify_spec propagation_result) as Hreuse.
  bind_fact (mt_qhead (ms_core propagation_result) = ms_qtail propagation_result) as Hdrain.
    pose proof (solver_propagation_drained_assuming_strong
      _ _ _ _ propagation_result Hinv Hdrain) as Hstrong.
    destruct Hframe as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
    assert (Hlim0 : Zlength (mt_lim (ms_core propagation_result)) = 0).
    { rewrite Hlim. exact Hdepth. }
    assert (Hpending : ms_capacity_root_propagation_pending propagation_result = 0).
    { exact (proj1 Hinv). }
    assert (Hready : solver_simplify_reuse M_solver_simplify_spec propagation_result).
    { intros [Hcompleted | Hfalse].
      - apply (minisat_base_completion_at_depth_zero__api_reentry
          smp_n_solver_simplify_spec propagation_result
          (msa_trail_wf (msas_weak Hstrong))
          (msa_db_wf (msas_weak Hstrong)) Hlim0).
        apply (proj1 Hreuse).
        eapply minisat_full_completion_implies_base__api_reentry;
          [exact (msa_trail_wf (msas_weak Hentry))|
           exact (msa_db_wf (msas_weak Hentry))|exact Hcompleted].
      - exfalso. eapply minisat_resident_false_excludes_drained_success__api_reentry;
          [exact (msa_shape (msas_weak Hstrong))|
           exact (msa_db_wf (msas_weak Hstrong))|
           exact (msa_trail_wf (msas_weak Hstrong))|exact Hdrain|
           exact (msas_watch_frontier Hstrong)|exact (proj2 Hreuse Hfalse)]. }
    assert (Hmodel_empty : ms_model M_solver_simplify_spec = nil -> ms_model propagation_result = nil).
    { rewrite Hmodel. tauto. }
    assert (Hdecay_positive : msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
      msat_fp32_positive_finite (ms_cla_decay propagation_result)).
    { rewrite Hdecay. tauto. }
    Exists propagation_result. msat_manual_entailer_with ltac:(tauto || lia).
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_6 : solver_simplify_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply solver_rep_assigns_simplify_control_split__simplify.
Qed.


Lemma proof_of_solver_solve_solver_solve_spec_entail_solver_solve_incremental_spec :
  solver_solve_solver_solve_spec_entail_solver_solve_incremental_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto). Intros.
  pose proof (solver_incremental_update_entry_frame__api_reentry
    s_pre begin_pre endvar_pre n_solver_solve_incremental_spec F_solver_solve_incremental_spec A_arr_solver_solve_incremental_spec M_solver_solve_incremental_spec) as Hentry_frame.
  lazymatch type of Hentry_frame with
  | _ |-- ?Frame =>
    assert (Hsplit : solver_incremental_ownership_at s_pre M_solver_solve_incremental_spec **
      assumptions_array n_solver_solve_incremental_spec begin_pre endvar_pre A_arr_solver_solve_incremental_spec |-- Frame)
  end.
  { sep_apply_r_atomic Hentry_frame.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial. tauto. }
  sep_apply Hsplit.
  Intros wl.
  match goal with
  | Hfacts : solver_update_ready n_solver_solve_incremental_spec F_solver_solve_incremental_spec nil M_solver_solve_incremental_spec /\ solver_query_watch_ready M_solver_solve_incremental_spec /\
      msolver_seed_shadow M_solver_solve_incremental_spec /\ solver_query_reuse_guard M_solver_solve_incremental_spec /\
      2 * ms_cap M_solver_solve_incremental_spec <= INT_MAX |- _ =>
      destruct Hfacts as [Hupdate [Hready [Hseed [Hwatch Hbound]]]]
  end.
  Exists wl n_solver_solve_incremental_spec F_solver_solve_incremental_spec A_arr_solver_solve_incremental_spec M_solver_solve_incremental_spec.
  split_pure_spatial.
  - cancel (solver_rep_wl s_pre M_solver_solve_incremental_spec wl).
    cancel (assumptions_array n_solver_solve_incremental_spec begin_pre endvar_pre A_arr_solver_solve_incremental_spec).
    cancel.
    pre_process_default.
    Split.
    all: Intros Mret.
    all: assert (Hdomain : retval = 0 \/ retval = 1) by tauto.
    all: pose proof
      (solver_incremental_common_result_from_expanded__api_reentry
        s_pre begin_pre endvar_pre n_solver_solve_incremental_spec F_solver_solve_incremental_spec A_arr_solver_solve_incremental_spec M_solver_solve_incremental_spec retval wl Hwatch Hbound) as Hresult.
    all: lazymatch type of Hresult with
      | ?Raw |-- _ =>
        assert (Hraw :
          assumptions_array n_solver_solve_incremental_spec begin_pre endvar_pre A_arr_solver_solve_incremental_spec **
          (solver_rep_wl s_pre Mret wl **
           solver_wlists_tail wl (2 * n_solver_solve_incremental_spec) (2 * ms_cap M_solver_solve_incremental_spec)) |-- Raw) by
          (cancel (assumptions_array n_solver_solve_incremental_spec begin_pre endvar_pre A_arr_solver_solve_incremental_spec);
           cancel (solver_wlists_tail wl (2 * n_solver_solve_incremental_spec) (2 * ms_cap M_solver_solve_incremental_spec));
           first [solve [Left; Exists Mret;
                         msat_manual_entailer_with ltac:(tauto)]
                 |solve [Right; Exists Mret;
                         msat_manual_entailer_with ltac:(tauto)]])
      end.
    all: lazymatch type of Hresult with
      | ?Raw |-- ?Public =>
        assert (Hpublic_result :
          (assumptions_array n_solver_solve_incremental_spec begin_pre endvar_pre A_arr_solver_solve_incremental_spec ** solver_rep_wl s_pre Mret wl) **
          solver_wlists_tail wl (2 * n_solver_solve_incremental_spec) (2 * ms_cap M_solver_solve_incremental_spec) |-- Public) by
          (set (Hraw_asrt := Raw) in *; set (Hpublic_asrt := Public) in *;
           sep_apply_r_atomic Hresult; sep_apply_r_atomic Hraw; cancel; cancel)
      end.
    all: sep_apply Hpublic_result.
    all: Intros Mout.
    all: match goal with
      | Hfacts : solver_public_query_entry ?out_n ?out_F ?out_state /\
          solver_query_reuse_guard ?out_state /\
          solver_update_ready ?out_n ?out_F nil ?out_state /\ _ |- _ =>
          destruct Hfacts as [Hpublic [Hguard [Hupdate_out Hcases]]]
      end.
    all: destruct Hcases as
      [[Hret Hsat] | [Hret [Hunsat [Hpending_out Halt]]]];
      [ Left;
        Exists Mout; msat_entailer_with ltac:(tauto)
      | destruct Halt as [Hwatch_out | Hunsat_F];
        [ Right;
          Right;
          Exists Mout; msat_entailer_with ltac:(tauto)
        | Right;
          Left;
          Exists Mout; msat_entailer_with ltac:(tauto) ] ].
  - split_pures; try (dump_pre_spatial; assumption).
Qed.


Lemma proof_of_solver_solve_entail_wit_5_2_split_goal_1 : solver_solve_entail_wit_5_2_split_goal_1.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_2_split_goal_2 : solver_solve_entail_wit_5_2_split_goal_2.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_2_split_goal_3 : solver_solve_entail_wit_5_2_split_goal_3.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_2 : solver_solve_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Z.sub_0_r in *.
  subst retval_2.
  assert (Hcell : lbool_cell
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0)).
  { eapply Forall_Znth_elim.
    - exact (mtw_cells (msa_trail_wf (msas_weak PreH29))).
    - rewrite PreH28.
      assert (Hwf : lit_wf_c n_solver_solve_spec (Znth k raw 0))
        by (apply Forall_lit_wf_Znth; [assumption | lia]).
      exact (lit_var_c_in_range _ _ Hwf). }
  assert (Hrepr : signed_last_nbits
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0) 8 =
    Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
  { apply signed_last_nbits_eq; [lia |].
    unfold lbool_cell in Hcell.
    destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia. }
  assert (Hreprn : signed_last_nbits
    (- Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0) 8 =
    - Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
  { apply signed_last_nbits_eq; [lia |].
    unfold lbool_cell in Hcell.
    destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia. }
  rewrite ?Hrepr, ?Hreprn.
  assert (Hnonempty : raw <> nil)
    by (intro E; subst raw; rewrite Zlength_nil in *; lia).
  pose proof (lit_sign_c_range (Znth k raw 0)) as Hsign.
  split_pure_spatial.
  - assert (Hsign0 : lit_sign_c (Znth k raw 0) = 0) by lia.
    rewrite Hsign0. simpl.
    rewrite PreH20.
    cancel.
    destruct (Znth (lit_var_c (Znth k raw 0))
      (mt_assigns (ms_core Mcur)) 0); cancel.
  - split_pures; try assumption.
    all: entailer!.
Qed.


Lemma proof_of_solver_solve_entail_wit_7_1 : solver_solve_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists raw_2 (k_2 + 1) Mcur_2.
  unfold assumption_true_advance in PreH4.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (first [assumption | lia | tauto])] ..]).
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_13_pure : solver_solve_partial_solve_wit_13_pure.
Proof.
  msat_solve_close_assumption_lit_bounds k.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_12_split_goal_spatial : solver_solve_which_implies_wit_12_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename n_solver_solve_spec into n. rename F_solver_solve_spec into F. rename A_arr_solver_solve_spec into A_arr.
assert (Hfacts : solver_shape Mfailure /\ mtrail_wf n (ms_core Mfailure) /\ heap_wf n (msolver_heap Mfailure) /\ prop_level (ms_core Mfailure)).
{ assert (Hkind : failure_kind = 0 \/ failure_kind = 1) by lia. destruct Hkind as [Hkind | Hkind].
  - destruct (PreH8 Hkind) as [[Hstrong Hdrain] Hreuse]. pose proof (msas_weak Hstrong) as Hweak.
    exact (conj (msa_shape Hweak) (conj (msa_trail_wf Hweak) (conj (msa_heap_wf Hweak) (msas_prop_level Hstrong)))).
  - destruct (PreH9 Hkind) as [[Hready _] _]. unfold propagation_cancel_ready in Hready.
    destruct Hready as (Hweak & Hprop & Hlit & Hprocessed & Hlevel & Hfront & Hheap & Hcovers & Hreasonless).
    destruct Hweak as [Hpending Hweak]. cbn in Hweak.
    split; [exact (msa_shape Hweak)|]. split; [exact (msa_trail_wf Hweak)|]. tauto.
}
destruct Hfacts as [Hshape [Htrail [Hheap Hprop]]].
assert (Hcancel : cancel_bound_ready Mfailure 0).
{ unfold cancel_bound_ready. destruct (Z_lt_ge_dec 0 (Zlength (mt_lim (ms_core Mfailure)))).
  - right. unfold prop_level in Hprop. apply (Forall_Znth_elim Z (fun b => b <= mt_qhead (ms_core Mfailure)) (mt_lim (ms_core Mfailure)) 0 0 Hprop). lia.
  - left. pose proof (Zlength_nonneg (mt_lim (ms_core Mfailure))). lia. }
sep_apply (solver_rep_assigns_levels_cancel_split s Mfailure values levels_ptr solve_wl_solver_solve_spec).
unfold solver_cancel_pre. rewrite PreH2.
pose proof (Zlength_nonneg (mt_lim (ms_core Mfailure))). msat_manual_entailer_with ltac:(lia || assumption).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_12 : solver_solve_which_implies_wit_12.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_solve_which_implies_wit_12_split_goal_spatial M_solver_solve_spec A_arr_solver_solve_spec F_solver_solve_spec n_solver_solve_spec solve_wl_solver_solve_spec levels_ptr raw k Mfailure failure_kind failure_focus values s PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_19 : solver_solve_which_implies_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  unfold solver_restart_loop.
  Intros search_entry A_inst.
  match goal with
  | Hentry : ms_cap search_entry = ms_cap ?public_entry /\ _ |- _ =>
      destruct Hentry as (Hentry_cap & Hentry_watch)
  end.
  Split.
  - {
  unfold solver_search_result.
  Split.
  - Split.
    + Intros Mterminal.
      assert (Hstatus : status = 1) by lia.
      subst status.
      match goal with
      | Hfacts : ms_cap Mterminal = ms_cap search_entry /\ _ |- _ =>
          destruct Hfacts as (Hcap & Hreuse & Hinv & Hroot & Hdrain & Hpending & Hseed & Hmodel)
      end.
      lazymatch type of Hentry_watch with
      | solver_query_reuse_guard ?entry -> _ =>
          assert (Hterminal_reuse : solver_terminal_reuse n F A_arr entry Mterminal 1)
            by (intro Hready; split;
                [intros _; exact (Hreuse (Hentry_watch Hready))
                |intro Hbad; discriminate])
      end.
      assert (Hsat_ready : solver_sat_cancel_ready n F A_arr Mterminal).
      { exists A_inst. split; [exact Hinv|]. split; [exact Hdrain|].
        split; [exact Hpending|exact Hseed]. }
      pose proof (msi_size Hinv) as Hsize.
      pose proof (msi_prop_level Hinv) as Hprop.
      assert (Hcancel : cancel_bound_ready Mterminal 0).
      { unfold cancel_bound_ready.
        destruct (Z_lt_ge_dec 0 (Zlength (mt_lim (ms_core Mterminal)))).
        - right. unfold prop_level in Hprop.
          apply (Forall_Znth_elim Z
            (fun b => b <= mt_qhead (ms_core Mterminal))
            (mt_lim (ms_core Mterminal)) 0 0 Hprop). lia.
        - left. pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia. }
      sep_apply (solver_rep_cancel_split s Mterminal solve_wl).
      Intros terminal_levels.
      Exists terminal_levels Mterminal.
      unfold solver_cancel_pre.
      split_pure_spatial.
      -- cancel.
         cancel (solver_cancel_owned s Mterminal solve_wl).
      -- split_pures; dump_pre_spatial.
         ++ lia.
         ++ exact Hterminal_reuse.
         ++ lia.
         ++ lia.
         ++ lia.
         ++ lia.
         ++ intros _. split; [exact Hmodel | exact Hsat_ready].
         ++ intro Hbad. discriminate Hbad.
         ++ split; [exact (msi_shape Hinv) |].
            split; [rewrite <- Hsize; exact (msi_trail_wf Hinv) |].
            split; [exact Hcancel |].
            split; [rewrite <- Hsize; exact (msi_heap_wf Hinv) |].
            pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia.
    + Intros Mterminal.
      assert (Hstatus : status = -1) by lia.
      subst status.
      match goal with
      | Hfacts : ms_cap Mterminal = ms_cap search_entry /\ _ |- _ =>
          destruct Hfacts as (Hcap & Hreuse & Hweak & Hroot & Hcancel & Hpending & Hunsat)
      end.
      lazymatch type of Hentry_watch with
      | solver_query_reuse_guard ?entry -> _ =>
          assert (Hterminal_reuse : solver_terminal_reuse n F A_arr entry Mterminal (-1))
            by (intro Hready; split;
                [intro Hbad; discriminate
                |intros _; exists A_inst; exact (Hreuse (Hentry_watch Hready))])
      end.
      pose proof (msw_size Hweak) as Hsize.
      sep_apply (solver_rep_cancel_split s Mterminal solve_wl).
      Intros terminal_levels.
      Exists terminal_levels Mterminal.
      unfold solver_cancel_pre.
      split_pure_spatial.
      -- cancel.
         cancel (solver_cancel_owned s Mterminal solve_wl).
      -- split_pures; dump_pre_spatial.
         ++ lia.
         ++ exact Hterminal_reuse.
         ++ lia.
         ++ lia.
         ++ lia.
         ++ lia.
         ++ intro Hbad. discriminate Hbad.
         ++ intros _. exact Hunsat.
         ++ split; [exact (msw_shape Hweak) |].
            split; [rewrite <- Hsize; exact (msw_trail_wf Hweak) |].
            split; [exact Hcancel |].
            split; [rewrite <- Hsize; exact (msw_heap_wf Hweak) |].
            pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia.
  - Intros Mbad. Intros. cancel. exfalso; lia.
    }
  - Intros. cancel. exfalso; lia.
Qed.


Lemma proof_of_enqueue_partial_solve_wit_6_pure : enqueue_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst l_pre.
  unfold enqueue_input in PreH8.
  destruct PreH8 as (_ & _ & _ & _ & _ & _ & _ & Hroom & _).
  specialize (Hroom PreH1).
  split_pures; dump_pre_spatial; first [ exact PreH1 | exact PreH28 | lia ].
Qed.


Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_enqueue_assign_bump_close (-1) retval_2 l_pre retval_3 l0 assigns
    qtail levels0 reasons0 trail rsn trl asg lvl n lim reason_pre.
Qed.


Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold enqueue_state_at.
  Intros rsn trl.
  Exists trl rsn.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_addclause_entail_wit_9 : solver_addclause_entail_wit_9.
Proof.
LLM_pre_process ltac:(lia || int_auto).
sep_apply (store_ptr_undef_store_ptr &( "values") asg).
sep_apply (store_int_undef_store_int &( "last") last).
bind_fact (solver_shape Mnew) as Hshape.
bind_fact (Forall (lit_wf_c (ms_size Mnew)) kept) as Hwf.
bind_fact (clause_install_pending_cert (ms_size Mnew) ac_F_addclause_spec
  (msolver_set_root Mnew 0) kept (solver_selected_is_learnt 0)) as Hcert.
bind_fact (clause_allocator_fresh Mnew retval) as Hfresh.
bind_fact (lit_neg_c (Znth 0 kept 0) <> lit_neg_c (Znth 1 kept 0)) as Hne.
bind_fact (solver_support_inv (ms_size Mnew) ac_F_addclause_spec ac_A_arr_addclause_spec
  ac_A_inst_addclause_spec 0 Mnew) as Hsupport.
bind_fact (ms_capacity_root_propagation_pending Mnew = 0) as Hpend.
bind_fact (msolver_seed_shadow Mnew) as Hseed.
bind_fact (Zlength (mt_lim (ms_core Mnew)) = 0) as Hlim0.
bind_fact (minisat_watch_completed ac_M_addclause_spec -> minisat_watch_completed Mnew) as Hcompl.
pose proof (solver_shape_wm_len Mnew Hshape) as Hwm.
pose proof (lit_neg_c_wf _ _ (Forall_lit_wf_Znth (ms_size Mnew) kept 0 Hwf ltac:(lia))) as Hi.
pose proof (lit_neg_c_wf _ _ (Forall_lit_wf_Znth (ms_size Mnew) kept 1 Hwf ltac:(lia))) as Hj.
unfold lit_wf_c in Hi,Hj.
set (Minstalled := msolver_install_clause Mnew retval kept false).
assert (Hinstalled : clause_new_success_transition_root (ms_size Mnew) ac_F_addclause_spec
  ac_A_arr_addclause_spec ac_A_inst_addclause_spec Mnew kept retval 0 0 Minstalled).
{ split; [exact Hfresh|]. split; [reflexivity|]. split.
  - apply solver_support_inv_install_clause__api_reentry; try assumption; lia.
  - split; [exact Hpend|]. split; [exact Hseed|].
    apply clause_install_cert_at_root__api_reentry; [lia|exact Hcert]. }
assert (Hshape_installed : solver_shape Minstalled) by (apply solver_shape_install; exact Hshape).
assert (Hcomplete : minisat_watch_completed ac_M_addclause_spec -> minisat_watch_completed Minstalled).
{ intros H. eapply clause_new_problem_completed__api_reentry; [exact Hinstalled|]. apply Hcompl. exact H. }
Exists retval Minstalled.
unfold clause_new_transaction_rest_at_gen.
split_pure_spatial.
- cancel (solver_wlists_tail wlg (2 * ms_size Mnew) (2 * ms_cap Mnew)).
  sep_apply (wlists_clause_new_refold wlg Mnew retval kept Hwm ltac:(lia) ltac:(lia) Hne).
  assert (Hsingle : MiniSatClause.rep retval false kept |-- clause_db_rep ((retval,clause_obj_of kept false)::nil)).
  { simpl. cancel (MiniSatClause.rep retval false kept). cancel. }
  change (solver_selected_is_learnt 0) with false.
  sep_apply Hsingle.
  sep_apply (clause_db_rep_app_intro (ms_prob Mnew) ((retval,clause_obj_of kept false)::nil)).
  unfold solver_rep_levels_wl_at, clause_new_frame_at_gen, clause_new_vecs_frame_gen.
  rewrite ?sel_vec_prob, ?sel_db_prob.
  Intros act asg0 opos rsn trl tgs.
  Exists act asg0 opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
   solver_scalars_rep, solver_vecs_rep, clause_new_scalars_frame, clause_new_ptrs_frame,
   solver_fp_rep, solver_var_arrays_rep, solver_trail_array_rep, solver_wlists_handle, wlists_rep.
  unfold Minstalled, msolver_install_clause,
   msolver_propagation_overlay, msolver_propagation_update.
  cbn -[Znth replace_Znth clause_new_watch_map VecpArray.full DoubleArray.seg IntArray.seg PtrArray.seg CharArray.seg store_double store_float Z.mul].
  unfold db_words. rewrite map_app. cbn [map fst].
  split_pure_spatial.
  + msat_entailer_with ltac:(assumption || lia).
  + split_pures.
    * dump_pre_spatial. exact Hshape_installed.
    * dump_pre_spatial. rewrite clause_new_watch_map_Zlength. exact Hwm.
- msat_manual_entailer_with ltac:(assumption || lia).
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_18_pure : solver_addclause_partial_solve_wit_18_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst i endvar_pre.
assert (Hsizecap : 0 <= ms_size Mnew <= ms_cap Mnew).
{ match goal with H : solver_shape Mnew |- _ => unfold solver_shape in H; tauto end. }
msat_manual_entailer_with ltac:(lia || assumption).
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_47_pure : solver_addclause_partial_solve_wit_47_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_addclause_sort_cursor_close.
Qed.


Lemma proof_of_solver_addclause_return_wit_1 : solver_addclause_return_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
try (apply _derivable1_andp_intros; [solve [(Intros; split_pures; dump_pre_spatial; solve [auto | (lia)])]|]).
all: msat_split_after_llm.
all: ac_shape.
all: ac_sign.
all: ac_spatial.
rewrite ?sizeof_int in *.
match goal with
| H : j = begin_pre + ?q * 4 |- _ => replace (j - begin_pre) with (q * 4) by lia
end.
rewrite quot_mul_four.
rewrite !ulnb64_lo64.
(* The engine truncates the pointer difference before adding it; the model does
   not.  [lo64_add_idem] reconciles them by modular idempotence -- no range
   reasoning about the literal count is needed at all. *)
rewrite lo64_add_idem.
match goal with H : Zlength kept = q |- _ => rewrite <- H end.
sep_apply stats_rep_addclause_fold.
sep_apply addclause_stats_close_wl_finish.
match goal with
| H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
    destruct (clause_new_success_root_bounds__api_reentry _ _ _ _ _ _ _ _ _ _ H)
      as [Hcs Hcc]
end.
unfold addclause_support_post_at.
Exists (msolver_addclause_finish Mclause kept) (kept ++ tail)
       (ac_F_addclause_spec ++ (lits_denote kept :: nil)).
split_pure_spatial.
-   rewrite ?addclause_finish_size, ?addclause_finish_cap, ?Hcs, ?Hcc.
  replace (ms_size Mnew) with (ms_size (msolver_addclause_finish Mclause kept))
    by (rewrite ?addclause_finish_size; congruence).
  replace (ms_cap Mnew) with (ms_cap (msolver_addclause_finish Mclause kept))
    by (rewrite ?addclause_finish_cap; congruence).
  sep_apply solver_rep_growable_of_wl.
  sep_apply IntArray.seg_merge_to_seg.
  cancel.
  match goal with
  | H : Zlength (?k ++ ?t) = _ |- _ =>
      pose proof (Zlength_nonneg k); pose proof (Zlength_nonneg t);
      rewrite Zlength_app in H
  end; lia.
- dump_pre_spatial. ac_support_transition.
  match goal with
  | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
      destruct H as (Hfresh & Hinst & Hinv & Hpend & Hseed & Hcert)
  end.
  change (ms_size (msolver_set_root (msolver_addclause_finish Mclause kept) 0) =
    ms_size Mnew) in Hcs.
  change (ms_cap (msolver_set_root (msolver_addclause_finish Mclause kept) 0) =
    ms_cap Mnew) in Hcc.
  rewrite Hcs, Hcc.
  split; [ assumption |].
  split; [ assumption |].
  split; [ assumption |].
  split; [ lia |].
  split; [ intros _; split; [ assumption | split; assumption ] |].
  right.
  split; [ reflexivity |].
  split.
  + apply solver_support_inv_addclause_finish__api_reentry. rewrite cn_F_prob in Hinv. exact Hinv.
  + apply addclause_install_equiv. assumption.
- match goal with
  | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
      destruct H as (Hfresh & Hinst & Hinv & Hpend & Hseed & Hcert)
  end.
  assumption.
- match goal with
  | H : clause_new_success_transition_root _ _ _ _ _ _ _ _ 0 _ |- _ =>
      destruct H as (Hfresh & Hinst & Hinv & Hpend & Hseed & Hcert)
  end.
  assert (Sh : solver_shape Mclause) by assumption.
  unfold solver_shape in Sh; decompose [and] Sh; assumption.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_4_split_goal_1 : solver_addclause_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_4 : solver_addclause_which_implies_wit_4.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_addclause_which_implies_wit_4_split_goal_1 ac_input_addclause_spec arr p PreH1 PreH2 PreH3).
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_8_split_goal_1 : solver_addclause_which_implies_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_8 : solver_addclause_which_implies_wit_8.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_addclause_which_implies_wit_8_split_goal_1 ac_input_addclause_spec kept tail q j begin PreH1 PreH2 PreH3 PreH4).
Qed.


Lemma proof_of_solver_canceluntil_return_wit_2 : solver_canceluntil_return_wit_2.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  cancel (&( "l_Undef") # Char |-> 0).
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( bound = Znth level_pre (mt_lim (ms_core M0)) 0 ) as H_bound.
  bind_fact ( cancel_reinsert_loop_inv M0 level_pre c assigns_now reasons_now order_now orderpos_now )
      as H_cancel_reinsert_loop_inv.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  destruct H_cancel_reinsert_loop_inv as
    (Hassigns & Hreasons & Hlevel & Hcrange & Hwf & Hincl & Hreinserted).
  assert (Hcb : c = bound - 1) by (rewrite H_bound in *; lia).
  assert (Hreinserted' :
    cancel_reinserted (heap_of_lists order_now orderpos_now)
      (mt_trail (ms_core M0)) bound (mt_qhead (ms_core M0))).
  { replace bound with (c + 1) by lia. exact Hreinserted. }
  assert (Hbound_qtail : 0 <= bound <= ms_qtail M0).
  { assert (Htraillen0 :
      Zlength (mt_trail (ms_core M0)) = ms_qtail M0)
      by (unfold solver_shape in H_solver_shape; tauto).
    pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level_pre
      H_mtrail_wf Hlevel) as Hr. rewrite <- H_bound in Hr. lia. }
  assert (Hqtail_cap : ms_qtail M0 <= ms_cap M0)
    by (unfold solver_shape in H_solver_shape; tauto).
  unfold solver_cancel_post.
  right.
  exists orderpos_now, order_now.
  split.
  - assert (Hreinserted_goal :
      cancel_reinserted (heap_of_lists order_now orderpos_now)
        (mt_trail (ms_core M0))
        (Znth level_pre (mt_lim (ms_core M0)) 0)
        (mt_qhead (ms_core M0))).
    { rewrite <- H_bound. exact Hreinserted'. }
    exact (conj Hlevel (conj Hwf (conj Hincl Hreinserted_goal))).
  - unfold solver_cancel_owned.
    split.
    + destruct Hlevel as [Hlevel0 HlevelLt].
      pose proof H_solver_shape as Hshape.
      unfold solver_shape in Hshape.
      destruct Hshape as
        (Hsrange & Hcapmax & Htwice & Hassignlen & Hlevelslen &
         Hreasonlen & Horderposoriglen & Hactivitylen & Htagslen &
         Htraillen & Hqrange & Hpendingrange & Hflag & Hpending &
         Hqtailrange & Hwmlen & Hbinarylen & Hstatslen &
         Hroot & Hbinarynz & Hbinaryeven).
      pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level_pre
        H_mtrail_wf (conj Hlevel0 HlevelLt)) as Hboundrange.
      pose proof (heap_wf_orderpos_length (ms_size M0)
        (heap_of_lists order_now orderpos_now) Hwf) as Horderposlen.
      assert (Hflag0 : ms_capacity_root_propagation_pending M0 = 0).
      { destruct Hflag as [Hf|Hf]; [exact Hf|].
        exfalso. specialize (Hpending Hf). lia. }
      unfold solver_shape, msolver_cancel_project, msolver_core_heap_update.
      cbn [mt_cancel].
      simpl.
      repeat split; try lia; try assumption;
        try (rewrite Zlength_clear_vars; assumption);
        try (rewrite Zlength_ztake by lia; lia);
        try (rewrite Hflag0; auto).
    + match type of H with
      | ?P m =>
        assert (HP : P |-- (EX act asg opos rsn trl tgs : Z,
          solver_nonlevel_rep_at s_pre
            (msolver_cancel_project M0 level_pre orderpos_now order_now (ms_root_level M0)) wl act asg opos rsn trl tgs))
      end.
      * sep_apply Veci.rep_ptr_rep.
        unfold solver_cancel_undef_tail.
        change (solver_int_tail trail_ptr (ms_qtail M0) (ms_cap M0)) with
          (solver_array_tail IntArray.undef_seg trail_ptr (ms_qtail M0) (ms_cap M0)).
        unfold solver_array_tail at 1. Intros trail_physical.
        msat_forget_array_suffix
          IntArray.seg_split_to_seg IntArray.seg_to_undef_seg
          IntArray.undef_seg_merge_to_undef_seg
          trail_ptr bound (ms_qtail M0) trail_physical
          (mt_trail (ms_core M0)).
        sep_apply (solver_array_tail_exact IntArray.undef_seg trail_ptr bound trail_physical ltac:(lia) ltac:(tauto)).
        sep_apply (solver_array_tail_lower IntArray.undef_seg trail_ptr bound trail_physical (ms_cap M0) ltac:(lia)).
        fold (solver_int_tail trail_ptr bound (ms_cap M0)).
        unfold solver_cancel_frame.
        Intros tgs.
        Exists activity_ptr assigns_ptr orderpos_ptr reasons_ptr
          trail_ptr tgs.
        unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
          solver_vecs_rep, solver_trail_array_rep,
          msolver_cancel_project, msolver_core_heap_update.
        cbn [mt_cancel].
        simpl.
        rewrite Hassigns, Hreasons, H_bound.
        rewrite !sublist_zero_ztake__assume.
        (Intros; cancel).
        sep_apply_l_atomic
          (solver_fp_rep_cancel_project__assume s_pre M0
            level_pre orderpos_now order_now
            (ms_root_level M0)).
        unfold solver_fp_rep, msolver_cancel_project,
          msolver_core_heap_update.
        simpl.
        replace (Znth level_pre (mt_lim (ms_core M0)) 0 - 0)
          with (Znth level_pre (mt_lim (ms_core M0)) 0) by lia.
        change (ztake level_pre (mt_lim (ms_core M0)))
          with (sublist 0 level_pre (mt_lim (ms_core M0))).
        cancel.
      * exact (HP m H).
Qed.



Lemma proof_of_solver_record_which_implies_wit_1 : solver_record_which_implies_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold solver_record_pre_at. Intros.
sep_apply (Veci.rep_rep_ptr cls rec_words). Intros learnt_ptr.
 match goal with H : record_clause_cert _ _ _ _ /\ _ |- _ => pose proof (proj1 (proj1 H)) as Hlen end.
 Exists learnt_ptr. msat_manual_entailer_with ltac:(int_auto).
Qed.



Lemma proof_of_solver_search_entail_wit_6_split_goal_1 : solver_search_entail_wit_6_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_model_copy_entry H_model_ready n F A_arr A_inst Mselected.
Qed.


Lemma proof_of_solver_search_entail_wit_6_split_goal_2 : solver_search_entail_wit_6_split_goal_2.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_model_copy_entry H_model_ready n F A_arr A_inst Mselected.
Qed.


Lemma proof_of_solver_search_entail_wit_6_split_goal_3 : solver_search_entail_wit_6_split_goal_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_model_copy_entry H_model_ready n F A_arr A_inst Mselected.
Qed.


Lemma proof_of_solver_search_entail_wit_6_split_goal_4 : solver_search_entail_wit_6_split_goal_4.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_model_copy_entry H_model_ready n F A_arr A_inst Mselected.
Qed.


Lemma proof_of_solver_search_entail_wit_6_split_goal_5 : solver_search_entail_wit_6_split_goal_5.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_model_copy_entry H_model_ready n F A_arr A_inst Mselected.
Qed.
