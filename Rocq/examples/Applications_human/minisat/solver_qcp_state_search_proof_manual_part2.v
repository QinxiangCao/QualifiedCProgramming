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
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part1.

Lemma proof_of_solver_addclause_which_implies_wit_2_split_goal_1 : solver_addclause_which_implies_wit_2_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_2_split_goal_2 : solver_addclause_which_implies_wit_2_split_goal_2.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_2_split_goal_3 : solver_addclause_which_implies_wit_2_split_goal_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_2_split_goal_4 : solver_addclause_which_implies_wit_2_split_goal_4.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_2 : solver_addclause_which_implies_wit_2.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_addclause_which_implies_wit_2_split_goal_1 ac_input_addclause_spec ac_n_addclause_spec sorted rest k i begin endvar maxvar PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
- Goal_apply (proof_of_solver_addclause_which_implies_wit_2_split_goal_2 ac_input_addclause_spec ac_n_addclause_spec sorted rest k i begin endvar maxvar PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
- Goal_apply (proof_of_solver_addclause_which_implies_wit_2_split_goal_3 ac_input_addclause_spec ac_n_addclause_spec sorted rest k i begin endvar maxvar PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
- Goal_apply (proof_of_solver_addclause_which_implies_wit_2_split_goal_4 ac_input_addclause_spec ac_n_addclause_spec sorted rest k i begin endvar maxvar PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_9 : solver_addclause_which_implies_wit_9.
Proof.
(* The dedup invariant
   makes the kept literal unassigned, hence off the trail and safe to enqueue. *)
(LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign.
unfold enqueue_state_at, solver_enqueue_frame_wl,
  solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at, solver_scalars_without_qtail_rep,
  solver_vecs_without_lim_rep,
  solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
unfold solver_scalars_rep, solver_vecs_rep, solver_trail_array_rep,
  solver_levels_slice_at, solver_var_arrays_rep, solver_ptrs_rep.
(* [_wl_at] makes wl a PARAMETER, so the LHS has 5 binders, not 6. *)
Intros act opos rsn trl tgs.
Exists rsn trl act opos tgs.
repeat lazymatch goal with
| |- _ |-- _ && _ => apply _derivable1_andp_intros
end;
lazymatch goal with
| |- _ |-- “ _ ” =>
    apply dump_spatial_left;
    solve
      [ ac_close
      | match goal with
        | Hsupport : solver_support_inv _ ?F ?A_arr ?A_inst ?root ?M |- _ =>
            eapply (addclause_dedup_enqueue_input F A_arr A_inst
              (msolver_set_root M root));
              [ exact Hsupport | eassumption | ac_arith ]
        end ]
| |- _ |-- _ =>
    msat_cancel_sound; change (emp |-- emp); cancel
end.
Qed.


Lemma proof_of_solver_canceluntil_entail_wit_3 : solver_canceluntil_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_cancel_open_at in *.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( heap_wf (ms_size M0) (msolver_heap M0) ) as H_heap_wf.
  bind_fact ( cancel_bound_ready M0 level_pre ) as H_cancel_bound_ready.
  bind_fact ( cancel_clear_loop_inv M0 level_pre c assigns_now_2 reasons_now_2 ) as H_cancel_clear_loop_inv.
  unfold cancel_clear_loop_inv in H_cancel_clear_loop_inv.
  destruct H_cancel_clear_loop_inv as (Hlevel & Hc & Hass & Hreason).
  assert (Hcb : c = Znth level_pre (mt_lim (ms_core M0)) 0 - 1) by lia.
  pose proof H_cancel_bound_ready as Hready.
  unfold cancel_bound_ready in H_cancel_bound_ready.
  destruct H_cancel_bound_ready as [Hout | Hbound]; [lia|].
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  assert (Htrail_len : Zlength (mt_trail (ms_core M0)) = ms_qtail M0) by tauto.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hinv : cancel_reinsert_loop_inv M0 level_pre
    (mt_qhead (ms_core M0) - 1)
    assigns_now_2 reasons_now_2 (ms_order M0) (ms_orderpos M0)).
  { unfold cancel_reinsert_loop_inv.
    split.
    - rewrite Hass, Hcb.
      replace (Znth level_pre (mt_lim (ms_core M0)) 0 - 1 + 1)
        with (Znth level_pre (mt_lim (ms_core M0)) 0) by lia.
      rewrite <- Htrail_len, sublist_to_zdrop__assume. reflexivity.
    - split.
      + rewrite Hreason, Hcb.
        replace (Znth level_pre (mt_lim (ms_core M0)) 0 - 1 + 1)
          with (Znth level_pre (mt_lim (ms_core M0)) 0) by lia.
        rewrite <- Htrail_len, sublist_to_zdrop__assume. reflexivity.
      + split; [lia|].
        split; [lia|].
        split.
        * change (heap_wf (ms_size M0) (msolver_heap M0)). exact H_heap_wf.
        * split; [apply incl_refl|].
          replace (mt_qhead (ms_core M0) - 1 + 1)
            with (mt_qhead (ms_core M0)) by lia.
          apply cancel_reinserted_init. }
  Exists assigns_now_2 reasons_now_2 (ms_order M0) (ms_orderpos M0).
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.


Lemma proof_of_solver_canceluntil_partial_solve_wit_7_pure : solver_canceluntil_partial_solve_wit_7_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    replace (c - 0) with c by lia; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_canceluntil_partial_solve_wit_14_pure : solver_canceluntil_partial_solve_wit_14_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( order_unassigned_pre (ms_size M0) (lit_var_c (Znth c (mt_trail (ms_core M0)) 0))
      order_now orderpos_now ) as H_order_unassigned_pre.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial.
    rewrite H_retval.
    replace (c - 0) with c by lia.
    exact H_order_unassigned_pre.
Qed.


Lemma proof_of_solver_canceluntil_safety_wit_1 : solver_canceluntil_safety_wit_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_record_entail_wit_3 : solver_record_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : db_words (ms_learnt Menq) = _ |- _ => rewrite H end.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_101_pure : solver_search_partial_solve_wit_101_pure.
Proof.
msat_search_selection_state_range.
Qed.


Lemma proof_of_solver_search_return_wit_3 : solver_search_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_result.
  Left. Right.
  Exists Mrootconf.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_6_split_goal_spatial : solver_search_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst M0 ) as H_msolver_inv.
  bind_fact ( ms_capacity_root_propagation_pending M0 = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow M0 ) as H_msolver_seed_shadow.
  bind_fact ( msat_fp32_positive_finite cd ) as H_msat_fp32_positive_finite.
  rename M0 into Mbase.
  set (Mlive := msolver_runtime_update Mbase (@nil Z) (ms_var_inc Mbase) vd
    (ms_cla_inc Mbase) cd (ms_progress Mbase)
    (replace_Znth 0 starts_now (ms_stats Mbase))).
  pose proof (msi_shape H_msolver_inv) as HshapeM.
  assert (Hshape_live : solver_shape Mlive).
  { unfold solver_shape in HshapeM |- *.
    unfold Mlive, msolver_runtime_update. cbn -[replace_Znth].
    rewrite Zlength_replace_Znth. tauto. }
  assert (Hinv_live : msolver_inv n F A_arr A_inst Mlive).
  { destruct H_msolver_inv. constructor; cbn [Mlive msolver_runtime_update] in *;
      [destruct msi_weak; constructor; cbn [Mlive msolver_runtime_update] in *; assumption
      | assumption | assumption | assumption | assumption ]. }
  assert (Hprop_live :
      solver_propagation_inv n F A_arr (PropagationStable A_inst) Mlive).
  { unfold solver_propagation_inv.
    split.
    - cbn [Mlive msolver_runtime_update]. exact H_ms_capacity_root_propagation_pending.
    - apply msolver_inv_propagation_of_strong. exact Hinv_live. }
  assert (Hseed_live : msolver_seed_shadow Mlive).
  { cbn [Mlive msolver_runtime_update]. exact H_msolver_seed_shadow. }
  assert (Hmodel_live : ms_model Mlive = @nil Z).
  { cbn [Mlive msolver_runtime_update]. reflexivity. }
  assert (Hdecay_live : msat_fp32_positive_finite (ms_cla_decay Mlive)).
  { cbn [Mlive msolver_runtime_update]. exact H_msat_fp32_positive_finite. }
  assert (Hstats_len : Zlength (ms_stats Mbase) = 11).
  { unfold solver_shape in HshapeM. tauto. }

  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hstats_live :
      (&(s # "solver_t" ->ₛ "stats" .ₛ "starts") # UInt64 |-> starts_now) **
      stats_without_starts_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mbase)
      |-- stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mlive)).
  { change (ms_stats Mlive) with (replace_Znth 0 starts_now (ms_stats Mbase)).
    assert (Hstarts_addr :
        &(s # "solver_t" ->ₛ "stats" .ₛ "starts") =
        &(stats_ptr # "stats_t" ->ₛ "starts"))
      by (unfold stats_ptr; csimpl; reflexivity).
    rewrite Hstarts_addr.
    exact (msat_stats_starts_refold stats_ptr (ms_stats Mbase) starts_now
      Hstats_len). }

  assert (Hscalars_live :
      solver_scalars_rep s Mbase |-- solver_scalars_rep s Mlive).
  { unfold solver_scalars_rep, Mlive. cbn. cancel. }

  assert (Hfp_live :
      (&(s # "solver_t" ->ₛ "var_decay") # Double |-> vd) **
      (&(s # "solver_t" ->ₛ "cla_decay") # Float |-> cd) **
      solver_fp_without_decays_rep s Mbase |-- solver_fp_rep s Mlive).
  { unfold solver_fp_without_decays_rep, solver_fp_rep, Mlive.
    cbn. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]). }

  assert (Hvecs_live :
      Veci.rep &(s # "solver_t" ->ₛ "model") (@nil Z) **
      solver_vecs_without_model_rep s Mbase |-- solver_vecs_rep s Mlive).
  { unfold solver_vecs_without_model_rep, solver_vecs_rep, Mlive.
    cbn. cancel. }

  assert (Hlevels_live :
      solver_levels_slice_at s Mbase levels |-- solver_levels_slice_at s Mlive levels).
  { unfold solver_levels_slice_at, Mlive. cbn. cancel. }

  rewrite Zsublist_nil by lia.
  unfold solver_search_loop.
  Exists Mlive (@nil Z).
  apply derivable1s_coq_prop_andp_r.
  2: { exact (conj eq_refl (conj (fun Hbase => Hbase)
      (conj Hprop_live (conj Hseed_live (conj Hmodel_live Hdecay_live))))). }
  cancel.
  unfold solver_search_init_frame_at, solver_search_bundle_at, solver_search_payload, solver_payload_cells.
  pose (stable_payload := solver_payload_cells s Mbase search_wl).
  fold (solver_payload_cells s Mbase search_wl).
  fold stable_payload.
  assert (Hstable_payload : stable_payload = stable_payload) by reflexivity.
  unfold stable_payload at 2 in Hstable_payload.
  unfold solver_payload_cells in Hstable_payload.
  clearbody stable_payload.
  Intros.
  sep_apply_l_atomic Hscalars_live.
  sep_apply_l_atomic Hfp_live.
  sep_apply_l_atomic Hvecs_live.
  sep_apply_l_atomic Hstats_live.
  sep_apply_l_atomic Hlevels_live.
  assert (Hassemble :
      solver_scalars_rep s Mlive ** solver_fp_rep s Mlive **
      solver_vecs_rep s Mlive **
      stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mlive) **
      stable_payload |-- solver_cancel_owned s Mlive search_wl).
  { rewrite Hstable_payload. unfold solver_cancel_owned.
    Intros act asg opos rsn trl tgs.
    Exists act asg opos rsn trl tgs.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_trail_array_rep, Mlive.
    cbn -[DoubleArray.seg IntArray.seg PtrArray.seg CharArray.seg].
    split_pure_spatial.
    - cancel (clause_db_rep (ms_prob Mbase)).
      cancel.
    - dump_pre_spatial. exact Hshape_live. }
  sep_apply_l_atomic Hassemble.
  unfold solver_rep_levels_wl_at.
  apply derivable1s_coq_prop_andp_r.
  2: { exact Hshape_live. }
  unfold solver_cancel_owned.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  cancel.
Qed.


Lemma proof_of_solver_search_which_implies_wit_6 : solver_search_which_implies_wit_6.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_search_which_implies_wit_6_split_goal_spatial M0 A_inst A_arr F n search_wl cd vd starts_now s levels PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_8_pure : solver_setnvars_partial_solve_wit_8_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_9_pure : solver_setnvars_partial_solve_wit_9_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_simplify_entail_wit_5 : solver_simplify_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_simplify_compaction_step smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec type Mcur_2 words_2 i jcur Mnext words_next j )
      as H_solver_simplify_compaction_step.
  Exists asg_2 words_next Mnext.
  unfold solver_simplify_compaction_step in H_solver_simplify_compaction_step.
  msat_manual_entailer_with ltac:(int_auto).
Qed.



Lemma proof_of_solver_simplify_entail_wit_6 : solver_simplify_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( Zlength (mt_lim (ms_core Mcur)) = 0 ) as H_Zlength_2.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  unfold solver_simplify_outer_loop. Exists Mcur.
  unfold msat_fp32_same in *.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [[Htype | Htype] [Hj [Hji [Hi Hmap]]]].
  - subst type.
    assert (Htail : sublist i (Zlength words) words = z_nil).
    { unfold z_nil. apply Zsublist_nil. lia. }
    assert (Hdbw : db_words (solver_selected_db 0 Mcur) = sublist 0 j words).
    { unfold db_words. rewrite Hmap, Htail. unfold z_nil.
      rewrite app_nil_r. reflexivity. }
    assert (Hlimnil : mt_lim (ms_core Mcur) = (@nil Z)) by
      (apply Zlength_nil_inv; exact H_Zlength_2).
    pose proof (msa_shape (msas_weak H_msolver_inv)) as Hshape.
    subst cs.
    sep_apply (Vecp.rep_ptr_rep (solver_selected_vec s_pre 0) cls (sublist 0 j words)).
    rewrite <- Hdbw.
    unfold z_nil.
    sep_apply (solver_rep_reasons_simplify_close_0__simplify
      s_pre Mcur reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec asg Hlimnil Hshape).
    repeat sep_apply store_ptr_undef_store_ptr.
    repeat sep_apply store_int_undef_store_int.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. intuition lia.
  - subst type.
    assert (Htail : sublist i (Zlength words) words = z_nil).
    { unfold z_nil. apply Zsublist_nil. lia. }
    assert (Hdbw : db_words (solver_selected_db 1 Mcur) = sublist 0 j words).
    { unfold db_words. rewrite Hmap, Htail. unfold z_nil.
      rewrite app_nil_r. reflexivity. }
    assert (Hlimnil : mt_lim (ms_core Mcur) = (@nil Z)) by
      (apply Zlength_nil_inv; exact H_Zlength_2).
    pose proof (msa_shape (msas_weak H_msolver_inv)) as Hshape.
    subst cs.
    sep_apply (Vecp.rep_ptr_rep (solver_selected_vec s_pre 1) cls (sublist 0 j words)).
    rewrite <- Hdbw.
    unfold z_nil.
    sep_apply (msat_simplify_close_learnt
      s_pre Mcur reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec asg Hlimnil Hshape).
    repeat sep_apply store_ptr_undef_store_ptr.
    repeat sep_apply store_int_undef_store_int.
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_simplify_which_implies_wit_9 : solver_simplify_which_implies_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_simplify_outer_loop.
  Intros Mtype.
  destruct H as
    [Hcap [Hroot [Hreuse [Htype_range [Hinv [Hlim [Hqhead [Hpending [Hseed [Hmodel Hdecay]]]]]]]]]].
  assert (Htype : type = 0 \/ type = 1) by lia.
  assert (Hlim_nil : mt_lim (ms_core Mtype) = (@nil Z)).
  { apply Zlength_nil_inv. exact Hlim. }
  destruct Htype as [Htype | Htype].
  - subst type.
    Right.
    sep_apply
      (solver_rep_reasons_simplify_open
        s Mtype 0 reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec Hlim_nil).
    Intros asg_type.
    Exists asg_type
      (db_words (solver_selected_db 0 Mtype)) Mtype.
    unfold msat_fp32_same, z_nil.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - subst type.
    Left.
    sep_apply
      (solver_rep_reasons_simplify_open
        s Mtype 1 reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec Hlim_nil).
    Intros asg_type.
    Exists asg_type
      (db_words (solver_selected_db 1 Mtype)) Mtype.
    unfold msat_fp32_same, z_nil.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_12 : solver_simplify_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  bind_fact ( Zlength (mt_lim (ms_core Mcur)) = 0 ) as H_Zlength.
  bind_fact ( mt_qhead (ms_core Mcur) = ms_qtail Mcur ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mcur = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow Mcur ) as H_msolver_seed_shadow.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [Htype [Hj0 [Hji [HiN Hdb]]]].
  assert (Hinv_keep : solver_simplify_db_compaction_inv type Mcur
      (solver_simplify_keep_words words i j) (i + 1) (j + 1)).
  { apply solver_simplify_keep_compaction_inv__simplify;
      try assumption.
    unfold solver_simplify_db_compaction_inv.
    repeat split; assumption. }
  assert (Hstep : solver_simplify_compaction_step
      smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec
      type Mcur words i j Mcur
      (solver_simplify_keep_words words i j) (j + 1)).
  { unfold solver_simplify_compaction_step,
      solver_simplify_keep_words.
    split.
    - left. split; [ | split ]; reflexivity.
    - split; [exact H_msolver_inv |].
      split; [exact H_Zlength |].
      split; [exact H_mt_qhead |].
      split; [exact H_ms_capacity_root_propagation_pending |].
      split; [exact H_msolver_seed_shadow |].
      split; [reflexivity |].
      split.
      + unfold msat_fp32_same. reflexivity.
      + exact Hinv_keep. }
  assert (Htail_current : sublist i (Zlength words) words =
      Znth i words 0 :: sublist (i + 1) (Zlength words) words).
  { rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
    rewrite (sublist_single 0 i words) by lia. reflexivity. }
  assert (Hinword : In (Znth i words 0)
      (map fst (solver_selected_db type Mcur))).
  { rewrite Hdb, Htail_current. apply in_or_app. right. left. reflexivity. }
  apply in_map_iff in Hinword.
  destruct Hinword as [[p co0] [Hp Hinselected]].
  cbn in Hp. subst p.
  assert (Hinfull : In (Znth i words 0, co0) (msolver_db Mcur)).
  { eapply solver_selected_db_in; eassumption. }
  assert (Hptrpos : 0 < Znth i words 0).
  { eapply db_wf_ptr_pos; [exact (msa_db_wf (msas_weak H_msolver_inv)) | exact Hinfull]. }
  assert (Hptreven : Znth i words 0 mod 2 = 0).
  { apply clause_ptr_mod2. eapply db_wf_even;
      [exact (msa_db_wf (msas_weak H_msolver_inv)) | exact Hinfull]. }
  unfold solver_simplify_compaction_step,
    solver_simplify_keep_words.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - replace (i - 0) with i by lia.
    unfold clause_db_pair_remainder.
    Split; Intros co1 pre post; destruct H as [Hpre [Hlits Hlearnt]];
      rewrite <- Hlits, <- Hlearnt; destruct Htype as [-> | ->];
      unfold solver_selected_prob_db, solver_selected_learnt_db in Hpre; simpl in Hpre;
      try (destruct pre; discriminate Hpre);
      unfold solver_selected_db; simpl; rewrite Hpre;
      msat_simplify_keep_db_close words i j cls co1 pre post.
Qed.



Lemma proof_of_solver_solve_entail_wit_3_1 : solver_solve_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hprefix0 : assumption_prefix raw_entry 0 = @nil literal).
  { unfold assumption_prefix.
    rewrite Zsublist_nil by lia.
    reflexivity. }
  Right.
  Exists raw_entry 0 Mready.
  rewrite Hprefix0.
  pose proof (Zlength_nonneg raw_entry).
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (first [assumption | lia | tauto])] ..]).
Qed.


Lemma proof_of_solver_solve_entail_wit_4_2 : solver_solve_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  msat_solve_lbool_cell_arm Mcur retval_3.
Qed.


Lemma proof_of_solver_solve_return_wit_3 : solver_solve_return_wit_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold solver_unsat_arm_at. Intros. Exists Mfalse_unsat. msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_3 : solver_solve_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (solver_update_ready n_solver_solve_spec F_solver_solve_spec nil Mready) as Hupdate.
  bind_fact (ms_capacity_root_propagation_pending Mready = 0) as Hpending.
  bind_fact (A_arr_solver_solve_spec <> nil -> mt_qhead (ms_core Mready) = ms_qtail Mready) as Hconditional.
  unfold solver_update_ready, msolver_resume_pending in Hupdate.
  rewrite Hpending in Hupdate. cbn in Hupdate.
  destruct Hupdate as [Hbase [Hlim _]].
  pose proof (msas_weak Hbase) as Hinv.
  pose proof (msa_shape Hinv) as Hshape.
  unfold assumptions_array.
  Intros raw.
  lazymatch goal with
  | Harray : endvar = _ /\ A_arr_solver_solve_spec = lits_denote raw /\ _ |- _ =>
      destruct Harray as [Hend [HA [Hrawwf Hempty]]]
  end.
  assert (HAwf : Forall (literal_wf n_solver_solve_spec) A_arr_solver_solve_spec).
  { rewrite HA. apply lits_denote_wf. exact Hrawwf. }
  pose proof (solver_query_assumptions__solve n_solver_solve_spec F_solver_solve_spec Mready A_arr_solver_solve_spec Hbase HAwf) as Hstrong.
  assert (Hprefix : A_arr_solver_solve_spec = assumption_prefix raw (Zlength raw)).
  { unfold assumption_prefix.
    rewrite (sublist_self raw (Zlength raw) eq_refl).
    exact HA. }
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_assigns_focus_frame_wl_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  destruct raw as [|z raw'].
  - assert (Hvalid : valid_int_position begin).
    { apply Hempty. reflexivity. }
    Right. Exists (@nil Z) act opos rsn trl tgs.
    pose proof (msa_size Hinv) as Hsize.
    subst n_solver_solve_spec.
    unfold solver_shape in Hshape.
    unfold solver_scalars_rep, solver_vecs_rep.
    split_pure_spatial.
    + msat_cancel_sound; cancel.
    + split_pures; dump_pre_spatial; solve [auto | lia].
  - assert (Hqhead : mt_qhead (ms_core Mready) = ms_qtail Mready).
    { apply Hconditional. rewrite HA. unfold lits_denote. discriminate. }
    Left. Exists (z :: raw') act opos rsn trl tgs.
    pose proof (msa_size Hinv) as Hsize.
    subst n_solver_solve_spec.
    unfold solver_shape in Hshape.
    unfold solver_scalars_rep, solver_vecs_rep.
    split_pure_spatial.
    + msat_cancel_sound; cancel.
    + split_pures; dump_pre_spatial; solve [auto | discriminate | lia].
Qed.


Lemma proof_of_solver_solve_which_implies_wit_20 : solver_solve_which_implies_wit_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (-1 <= status) as Hlow.
  bind_fact (status <= 1) as Hhigh.
  bind_fact (status <> 0) as Hnonzero.
  bind_fact (solver_terminal_reuse n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec M_solver_solve_spec Mterminal status) as Hreuse.
  bind_fact (ms_size Mterminal = n_solver_solve_spec) as Hsize.
  assert (Hsplit : status = 1 \/ status = -1) by lia.
  destruct Hsplit as [Hstatus | Hstatus].
  - Left.
    bind_fact (status = 1 -> model_saved n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec Mterminal /\
      solver_sat_cancel_ready n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec Mterminal) as Hsat.
    destruct (Hsat Hstatus) as [Hmodel Hready].
    pose proof Hready as Hready_copy.
    destruct Hready_copy as [A_inst [Hinv [Hdrain [Hpending Hseed_old]]]].
    assert (Hbase : solver_query_reuse_guard M_solver_solve_spec -> minisat_base_watch_completed Mterminal).
    { intro Hentry. exact (proj1 (Hreuse Hentry) Hstatus). }
    unfold solver_cancel_post.
    Split.
    + Intros.
      assert (Hlen : Zlength (mt_lim (ms_core Mterminal)) <= 0) by assumption.
      assert (Hdepth : Zlength (mt_lim (ms_core Mterminal)) = 0).
      { pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia. }
      destruct (solver_sat_query_ready_empty__solve n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec Mterminal Hready Hlen)
        as [Hquery Hseed].
      assert (Hwatch : solver_query_reuse_guard M_solver_solve_spec -> minisat_watch_completed Mterminal).
      { intro Hentry.
        exact (minisat_base_completion_at_depth_zero__api_reentry n_solver_solve_spec Mterminal
          (msi_trail_wf Hinv) (msi_db_wf Hinv) Hdepth (Hbase Hentry)). }
      Exists Mterminal. unfold solver_sat_arm_at.
      split_pure_spatial.
      * sep_apply (solver_cancel_join_rep s Mterminal terminal_levels solve_wl_solver_solve_spec).
        cancel.
      * split_pures; dump_pre_spatial; intuition lia.
    + Intros orderpos order.
      destruct H as (Hlevel & Hheap & Hincl & Hreinserted).
      set (Mpost := msolver_cancel_project Mterminal 0 orderpos order
        (ms_root_level Mterminal)).
      assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mterminal))) by lia.
      destruct (solver_sat_query_ready_cancel__solve n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec Mterminal
        orderpos order Hready Hpositive Hheap Hincl Hreinserted)
        as [Hquery Hseed].
      assert (Hbound : Znth 0 (mt_lim (ms_core Mterminal)) 0 <=
        mt_qhead (ms_core Mterminal)).
      { exact (Forall_Znth_elim _ _ _ 0 0 (msi_prop_level Hinv) Hlevel). }
      assert (Hwatch : solver_query_reuse_guard M_solver_solve_spec -> minisat_watch_completed Mpost).
      { intro Hentry.
        exact (minisat_base_completion_cancel_zero__api_reentry n_solver_solve_spec Mterminal
          orderpos order (ms_root_level Mterminal)
          (msi_trail_wf Hinv) (msi_db_wf Hinv) Hpositive Hbound (Hbase Hentry)). }
      Exists Mpost. unfold solver_sat_arm_at.
      split_pure_spatial.
      * unfold Mpost.
        sep_apply (solver_cancel_project_join_rep s Mterminal terminal_levels 0
          orderpos order (ms_root_level Mterminal) solve_wl_solver_solve_spec).
        cancel.
      * unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
        cbn. msat_manual_entailer_with ltac:(lia).
  - Right.
    bind_fact (status = -1 -> cnf_unsat n_solver_solve_spec (cnf_with_units F_solver_solve_spec A_arr_solver_solve_spec)) as Hverdict.
    assert (Hunsat : cnf_unsat n_solver_solve_spec (cnf_with_units F_solver_solve_spec A_arr_solver_solve_spec)) by
      (apply Hverdict; exact Hstatus).
    unfold solver_cancel_post.
    Split.
    + Intros.
      assert (Hdepth : Zlength (mt_lim (ms_core Mterminal)) = 0).
      { pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia. }
      assert (Hrecovery : solver_query_reuse_guard M_solver_solve_spec ->
        solver_base_recovery n_solver_solve_spec F_solver_solve_spec Mterminal /\ solver_query_reentry n_solver_solve_spec F_solver_solve_spec Mterminal /\ msolver_seed_shadow Mterminal).
      { intro Hentry.
        destruct (proj2 (Hreuse Hentry) Hstatus)
          as [A_inst [Hseed [Hconflict|Hbase]]].
        - destruct Hconflict as [focus [Hready [Hwatch Hfalse]]].
          pose proof (solver_propagation_conflict_base_recovery__api_reentry
            n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec (PropagationStable A_inst) Mterminal focus
            Hready Hwatch Hfalse Hdepth) as Hbase_post.
          split; [exact Hbase_post|]. split; [|exact Hseed].
          exact (solver_base_recovery_false_reentry__api_reentry
            n_solver_solve_spec F_solver_solve_spec Mterminal Hbase_post Hfalse).
        - destruct Hbase as [Hbase_post Hfalse].
          split; [exact Hbase_post|]. split; [|exact Hseed].
          exact (solver_base_recovery_false_reentry__api_reentry
            n_solver_solve_spec F_solver_solve_spec Mterminal Hbase_post Hfalse). }
      Exists Mterminal. unfold solver_unsat_arm_at.
      split_pure_spatial.
      * sep_apply (solver_cancel_join_rep s Mterminal terminal_levels solve_wl_solver_solve_spec).
        cancel.
      * (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
    + Intros orderpos order.
      destruct H as (Hlevel & Hheap & Hincl & Hreinserted).
      set (Mpost := msolver_cancel_project Mterminal 0 orderpos order
        (ms_root_level Mterminal)).
      assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mterminal))) by lia.
      assert (Hheap_n : heap_wf n_solver_solve_spec (heap_of_lists order orderpos)).
      { rewrite <- Hsize. exact Hheap. }
      assert (Hrecovery : solver_query_reuse_guard M_solver_solve_spec ->
        solver_base_recovery n_solver_solve_spec F_solver_solve_spec Mpost /\ solver_query_reentry n_solver_solve_spec F_solver_solve_spec Mpost /\ msolver_seed_shadow Mpost).
      { intro Hentry.
        destruct (proj2 (Hreuse Hentry) Hstatus)
          as [A_inst [Hseed [Hconflict|Hbase]]].
        - destruct Hconflict as [focus [Hready [Hwatch Hfalse]]].
          destruct (solver_conflict_cancel_zero_base_recovery__api_reentry
            n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec (PropagationStable A_inst) Mterminal focus
            orderpos order Hready Hwatch Hseed Hpositive
            Hheap_n Hincl Hreinserted) as [Hbase_post [_ Hseed_post]].
          split; [exact Hbase_post|]. split; [|exact Hseed_post].
          exact (solver_cancel_project_reentry__api_reentry
            n_solver_solve_spec F_solver_solve_spec Mterminal orderpos order (ms_root_level Mterminal) Hbase_post).
        - destruct Hbase as [[[ _ [Hdepth _]] _] _]. lia. }
      Exists Mpost. unfold solver_unsat_arm_at.
      split_pure_spatial.
      * unfold Mpost.
        sep_apply (solver_cancel_project_join_rep s Mterminal terminal_levels 0
          orderpos order (ms_root_level Mterminal) solve_wl_solver_solve_spec).
        cancel.
      * unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
        cbn. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_addclause_entail_wit_2_2 : solver_addclause_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout].
  assert (Hrne : rest <> nil).
  { intro Hn; rewrite Hn in *;
    rewrite ?Zlength_app, ?Zlength_nil in *; lia. }
  destruct rest as [|r0 rst]; [contradiction|].
  try (replace (k - 0) with (Zlength sorted) in * by lia).
  try (replace (Zlength sorted - 0) with (Zlength sorted) in * by lia).
  rewrite (Znth_app_hd sorted r0 rst 0) in *.
  subst endvar_pre.
  Exists (sorted ++ r0 :: rst) r0 rst (@nil Z) sorted (Zlength sorted).
  rewrite app_nil_r.
  split_pure_spatial.
  - msat_cancel_sound; lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel.
  - split_pures; dump_pre_spatial; try solve [ac_close].
    + unfold addclause_sort_inner_inv; rewrite ?app_nil_r.
      repeat split; [ assumption | constructor ].
    + reflexivity.
Qed.


Lemma proof_of_solver_addclause_return_wit_6_split_goal_spatial : solver_addclause_return_wit_6_split_goal_spatial.
Abort.


Lemma proof_of_solver_addclause_return_wit_6 : solver_addclause_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!.
  ac_shape; ac_sign; ac_spatial.
  rewrite ?Z.sub_0_r in *.
  assert (Hin : In (Znth k (kept ++ tail) 0) ac_input_addclause_spec)
    by (eapply all_from_Znth; ac_prem).
  assert (Hent : entails_clause ac_F_addclause_spec
      (lits_denote ac_input_addclause_spec)).
  { msat_addclause_root_input Mnew Hin.
    unfold lit_true, lit_sig.
    repeat match goal with
    | H : ?r = lit_var_c _ |- _ => is_var r; subst r
    end.
    ac_selfrepl. rewrite ?Z.sub_0_r in *.
    unfold lit_sign_c in *.
    destruct (Z.odd (Znth k (kept ++ tail) 0)); simpl in *; lia. }
  msat_addclause_entailed_return Mnew kept tail Hent.
Qed.
Lemma proof_of_solver_addclause_safety_wit_4 : solver_addclause_safety_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_split_after_llm;
  msat_addclause_shape_spatial_close.
  change (ac_n_addclause_spec <=
    Z.max (ms_cap ac_M_addclause_spec) 536870911) in PreH12.
  destruct (Z_le_gt_dec (ms_cap ac_M_addclause_spec) 536870911)
    as [Hcap | Hcap].
  - rewrite Z.max_r in PreH12 by lia. lia.
  - rewrite Z.max_l in PreH12 by lia. lia.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_5_split_goal_1 : solver_addclause_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_5 : solver_addclause_which_implies_wit_5.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_addclause_which_implies_wit_5_split_goal_1 ac_input_addclause_spec arr p j begin PreH1 PreH2 PreH3 PreH4).
Qed.


Lemma proof_of_solver_canceluntil_which_implies_wit_2 : solver_canceluntil_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( cancel_clear_loop_inv M0 level c assigns_now reasons_now ) as H_cancel_clear_loop_inv.
  unfold cancel_clear_loop_inv in H_cancel_clear_loop_inv.
  assert (Hlev : 0 <= level < Zlength (mt_lim (ms_core M0))) by tauto.
  pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level H_mtrail_wf Hlev)
    as Hbound.
  assert (Hcrange : 0 <= c < Zlength (mt_trail (ms_core M0))).
  { unfold solver_shape in H_solver_shape. lia. }
  pose proof (Forall_Znth_elim _ _ _ 0 c (mtw_trail_lits H_mtrail_wf) Hcrange)
    as Hlit.
  pose proof (lit_var_c_in_range (ms_size M0)
    (Znth c (mt_trail (ms_core M0)) 0) Hlit) as Hvar.
  unfold lit_wf_c in Hlit.
  unfold solver_shape in H_solver_shape.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_nclauses_solver_nclauses_spec_entail_solver_nclauses_incremental_spec : solver_nclauses_solver_nclauses_spec_entail_solver_nclauses_incremental_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (db_words (ms_prob M_solver_nclauses_incremental_spec)).
  sep_apply (solver_incremental_clauses_frame__public s_pre
    M_solver_nclauses_incremental_spec
    (solver_clauses_rep s_pre
      (db_words (ms_prob M_solver_nclauses_incremental_spec)))
    (solver_incremental_ownership_at s_pre
      M_solver_nclauses_incremental_spec)).
  cancel.
  Intros_r retval.
  pre_process_default.
  entailer_with ltac:(tauto).
  sep_apply derivable1_wand_elim1.
  all: cancel.
Qed.



Lemma proof_of_solver_record_entail_wit_5 : solver_record_entail_wit_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 match goal with H : record_enqueue_success _ _ _ _ _ _ _ _ _ |- _ => pose proof H as Hsucc end.
 bind_fact (msat_fp32_nonnegative cla_inc1) as Hcla_inc1_nonnegative.
 destruct Hsucc as [Henq [Hinv [Hp [Hseed [Hmodel [Hdecay [Hcap Hreuse]]]]]]].
 assert (Hstatslen : Zlength (record_stats_update rec_words (ms_stats Menq)) = 11).
 { rewrite record_stats_update_length__record. pose proof (msi_shape Hinv) as Hshape. unfold solver_shape in Hshape. tauto. }
 pose proof (msolver_inv_with_cla_inc_stats__record rec_n rec_F rec_A_arr rec_A_inst Menq cla_inc1
   (record_stats_update rec_words (ms_stats Menq)) Hinv Hcla_inc1_nonnegative Hstatslen) as Hinvstats.
 assert (Hreusefinish : minisat_record_reuse M0 rec_words (msolver_record_finish Menq rec_words c cla_inc1)).
 { intros Hentry. apply record_finish_base_completion__record. exact (Hreuse Hentry). }
 set (finished := msolver_record_finish Menq rec_words c cla_inc1).
 assert (Hfinish : record_finish_success rec_n rec_F rec_A_arr rec_A_inst M0 Menq rec_words c cla_inc1 finished).
 { unfold record_finish_success. split; [reflexivity|].
   unfold finished, msolver_record_finish in *.
   destruct (Z.eq_dec c 0); [congruence|].
   repeat first [assumption | reflexivity | split]. }
 assert (Hpublish : record_finish_with_capacity rec_n rec_F rec_A_arr rec_A_inst M0 Menq rec_words c cla_inc1 finished).
 { exact Hfinish. }
 Exists finished.
 subst retval. rewrite !ulnb64_lo64. rewrite ?lo64_add_idem.
 sep_apply (solver_record_finish_refold__record s_pre Menq levels_ptr rec_words cla_inc1 rec_wl).
 unfold finished, msolver_record_finish in Hpublish |- *.
 destruct (Z.eq_dec c 0); [congruence|].
 msat_manual_entailer_with ltac:(lia || assumption).
Qed.



Lemma proof_of_solver_search_entail_wit_5_3 : solver_search_entail_wit_5_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
sep_apply (Vecp.rep_ptr_rep &( s_pre # "solver_t" ->ₛ "learnts") p (db_words (ms_learnt Mclean))).
Exists Mclean.
unfold solver_search_reducedb_frame_at, solver_search_bundle_at, solver_search_payload, solver_rep_levels_wl_at.
unfold solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_scalars_rep, solver_scalars_without_qtail_rep, clause_new_scalars_frame,
  solver_vecs_rep, solver_vecs_without_learnts_rep.
Intros act asg opos rsn trl tgs.
Exists act asg opos rsn trl tgs.
msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_search_entail_wit_8_split_goal_spatial : solver_search_entail_wit_8_split_goal_spatial.
Abort.


Lemma proof_of_solver_search_entail_wit_8 : solver_search_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_loop.
  destruct PreH3 as (_ & Hprop & Hseed & Hmodel & Hfinite & _).
  Exists Mdecision learnt_words.
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_int_undef_store_int (&( "next")) retval).
    cancel.
  - msat_entailer_with ltac:(tauto).
Qed.
