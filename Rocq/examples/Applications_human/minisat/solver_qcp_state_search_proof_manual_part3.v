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
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part2.

Lemma proof_of_solver_search_partial_solve_wit_49_pure : solver_search_partial_solve_wit_49_pure.
Proof.
  msat_search_cla_inc_nonneg H_msolver_inv n F A_arr A_inst Mrecord.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_63_pure : solver_search_partial_solve_wit_63_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mstable ) as H_msolver_inv.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  unfold solver_shape in Hshape.
  destruct Hshape as
    [Hnonneg [Hcap [Htwosize [Hassign [Hlevels _]]]]].
  split_pures.
  - dump_pre_spatial. exact Hlevels.
  - dump_pre_spatial. exact Hassign.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_88_pure : solver_search_partial_solve_wit_88_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_model_ready in PreH1.
  destruct PreH1 as [Hinv [Hqtail [Horder [Hcap [Hseed Hmodel]]]]].
  split_pures; dump_pre_spatial.
  - exact Hmodel.
  - symmetry; exact (msi_size Hinv).
Qed.


Lemma proof_of_solver_search_which_implies_wit_12 : solver_search_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( ms_model Manalyze = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Manalyze) ) as H_msat_fp32_positive_finite.
  bind_fact ( msat_fp32_same (ms_cla_decay Manalyze) (ms_cla_decay Mcur) ) as H_msat_fp32_same.
  bind_fact (solver_search_reuse M0 Manalyze) as Hentry_reuse.
  unfold solver_analyze_post.
  Intros M' words backjump.
  destruct H as
    [Hanalysis [Hseed [Hmodel_eq [Hcap_eq [Hreuse [Hdecay_eq [Hlen
      [Hwords [Hnodup [Hclause [Hbackjump [Htags Htagged]]]]]]]]]]]].
  assert (Hresult_reuse : solver_search_reuse M0 M').
  { unfold solver_search_reuse in *. intro Hentry.
    apply Hreuse. exact (Hentry_reuse Hentry). }
  destruct (analysis_cancel_ready_reason_core
    n F A_arr (PropagationStable A_inst) M' focus Hanalysis)
    as [HsizeA [Hreasons Hbinary]].
  assert (Hinc : msat_fp32_nonnegative (ms_cla_inc M')).
  { pose proof Hanalysis as Hanalysis0.
    destruct Hanalysis0 as
      [Mbase [_ [_ [_ [_ [_ [_ Hinc]]]]]]].
    exact Hinc. }
  assert (Hmodel : ms_model M' = @nil Z).
  { rewrite Hmodel_eq. exact H_ms_model. }
  assert (Hfinite : msat_fp32_positive_finite (ms_cla_decay M')).
  { rewrite Hdecay_eq. exact H_msat_fp32_positive_finite. }
  assert (Hsame : msat_fp32_same
      (ms_cla_decay M') (ms_cla_decay Mcur)).
  { rewrite Hdecay_eq. exact H_msat_fp32_same. }
  assert (Hvar_range :
      0 <= lit_var_c (Znth 1 words 0) /\
      lit_var_c (Znth 1 words 0) < ms_size M').
  { destruct (Z.eq_dec (Zlength words) 1) as [Hone|Hgt].
    - assert (Hwf0 : lit_wf_c n (Znth 0 words 0)).
      { apply (Forall_Znth_elim Z (lit_wf_c n) words 0 0 Hwords).
        lia. }
      assert (Hnpos : 0 < n) by (destruct Hwf0; lia).
      assert (Hdefault : Znth 1 words 0 = 0).
      { apply znth_out_of_bounds; lia. }
      rewrite Hdefault.
      unfold lit_var_c.
      cbn.
      rewrite <- HsizeA.
      lia.
    - assert (Hidx : 0 <= 1 < Zlength words) by lia.
      assert (Hwf1 : lit_wf_c n (Znth 1 words 0)).
      { apply (Forall_Znth_elim Z (lit_wf_c n) words 0 1 Hwords).
        exact Hidx. }
      pose proof (lit_var_c_in_range n (Znth 1 words 0) Hwf1) as Hv.
      rewrite <- HsizeA.
      exact Hv. }
  replace (1 - 0) with 1 by lia.
  Exists backjump.
  Exists words.
  Exists M'.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_18 : solver_search_which_implies_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( ms_model Mback = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mback) ) as H_msat_fp32_positive_finite.
  unfold solver_record_post_at.
  Intros Mrecord.
  match goal with
  | Hpost : msolver_inv n F A_arr A_inst Mrecord /\ _ |- _ =>
      destruct Hpost as (Hinv & Hpending & Hseed & Hmodel & Hdecay & Hcap & Hreuse)
  end.
  assert (Hmodel_nil : ms_model Mrecord = (@nil Z))
    by (rewrite Hmodel; exact H_ms_model).
  assert (Hdecay_pos : msat_fp32_positive_finite (ms_cla_decay Mrecord))
    by (rewrite Hdecay; exact H_msat_fp32_positive_finite).
  bind_fact (record_watch1_positive Mback words) as Hpositive.
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mback |- _ =>
      assert (Hreuse_out : solver_search_reuse entry Mrecord)
        by (intro Hbase; apply Hreuse; split;
            [exact (Hentry Hbase)|exact Hpositive])
  end.
  Exists Mrecord.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
Qed.


Lemma proof_of_solver_search_which_implies_wit_20 : solver_search_which_implies_wit_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mrecord ) as H_msolver_inv.
  bind_fact ( ms_capacity_root_propagation_pending Mrecord = 0 ) as H_ms_capacity_root_propagation_pending.
  unfold solver_search_loop.
  pose (Mnew := msolver_runtime_update Mrecord (ms_model Mrecord) var_inc_now var_decay_now
    cla_inc_now cla_decay_now (ms_progress Mrecord) (ms_stats Mrecord)).
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mnew).
  { destruct (msi_weak H_msolver_inv). constructor; assumption. }
  assert (Hinv : msolver_inv n F A_arr A_inst Mnew).
  { constructor.
    - exact Hweak.
    - exact (msi_prop_level H_msolver_inv).
    - exact (msi_watch_frontier H_msolver_inv).
    - exact (msi_heap_covers H_msolver_inv).
    - exact (msi_reasonless_current H_msolver_inv). }
  assert (Hprop :
    solver_propagation_inv n F A_arr (PropagationStable A_inst) Mnew).
  { split; [exact H_ms_capacity_root_propagation_pending|].
    apply msolver_inv_propagation_of_strong. exact Hinv. }
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mrecord |- _ =>
      assert (Hreuse_new : solver_search_reuse entry Mnew)
        by (change (solver_search_reuse entry Mrecord); exact Hentry)
  end.
  Exists Mnew. Exists words.
  unfold solver_search_decay_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_fp_without_decay_incs_rep,
    solver_rep_levels_wl_at, solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold Mnew, msolver_runtime_update. cbn [ms_size ms_cap ms_qtail ms_capacity_pending_qhead ms_capacity_root_propagation_pending ms_core ms_root_level ms_reason_words ms_reason_of ms_prob ms_learnt ms_binary ms_binary_lits ms_wm ms_activity ms_orderpos ms_order ms_model ms_tags ms_tagged ms_stack ms_var_inc ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_return_wit_2 : solver_setnvars_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (snv_shape);
    (match goal with
  | HS : ms_size ?M = ?v,
    HI : solver_support_inv ?v ?F ?A ?B ?root ?M |- _ =>
      let H := fresh "HIsz" in
      pose proof HI as H; rewrite <- HS in H
  end).
  all: match goal with H : setnvars_core_equiv ?M0 ?M |- _ =>
    pose proof (setnvars_core_equiv_root_summary M0 M H) as Hroot_summary;
    assert (Hphysical_root : ms_root_level M = ms_root_level M0)
      by (unfold setnvars_core_equiv in H; tauto)
  end.
  all: (Exists Mcur);
    (pose proof (setnvars_bound_exit (ms_size sn_M_setnvars_spec) var n_pre
                ltac:(assumption) ltac:(lia)));
    (match goal with HS : ms_size ?M = ?v |- _ => rewrite <- HS end).
  all: (snv_unfold_all_unfolded_post);
    (Exists wlc actc asgc oposc rsnc lvlc trlc tgsc).
assert (Hpublish : ms_size sn_M_setnvars_spec = ms_size Mcur).
{ pose proof (setnvars_bound_exit (ms_size sn_M_setnvars_spec) var n_pre ltac:(assumption) ltac:(lia)); lia. }
rewrite Hpublish. msat_manual_entailer_with ltac:(snv_dispatch).
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_4 : solver_setnvars_which_implies_wit_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold solver_wlists_tail, solver_array_tail. Intros physical. sep_apply (proj1 (VecpArray.undef_seg_unfold wlc (2*var+1) physical ltac:(lia))). Exists physical. unfold VecpArray.vec_undef_store. rewrite Vecp.slot_eq. replace (2*var+1+1) with (2*var+2) by lia. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_return_wit_4 : solver_simplify_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec smp_A_arr_solver_simplify_spec M_solver_simplify_spec) as Hentry.
  bind_fact (Zlength (mt_lim (ms_core M_solver_simplify_spec)) = 0) as H_Zlength.
  bind_fact (propagation_cancel_ready smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec (PropagationAssuming smp_A_arr_solver_simplify_spec) propagation_result result_focus) as Hready.
  bind_fact (propagation_caller_frame M_solver_simplify_spec propagation_result) as Hframe.
  bind_fact (minisat_base_watch_completed M_solver_simplify_spec -> minisat_watch_conflict_ready smp_n_solver_simplify_spec propagation_result) as Hreuse.
  bind_fact (minisat_resident_false_clause propagation_result) as Hresident.
  bind_fact (msolver_seed_shadow propagation_result) as Hseed.
  bind_fact (propagation_conflict_cert smp_n_solver_simplify_spec smp_F_solver_simplify_spec propagation_result result_clause) as Hcert.
      pose proof Hready as Hcancel.
      destruct Hready as [[Hcap Hweak] Hready_tail].
      cbn in Hweak.
      assert (Hlen : Zlength (mt_lim
        (ms_core propagation_result)) = 0).
      { rewrite (proj1 Hframe). exact H_Zlength. }
      destruct Hframe as [_ [Hroot [_ [_ Hcapacity]]]].
      assert (Hrecovery : minisat_watch_completed M_solver_simplify_spec ->
        solver_base_recovery smp_n_solver_simplify_spec smp_F_solver_simplify_spec propagation_result /\
        msolver_seed_shadow propagation_result).
      { intro Hcompleted. split; [|exact Hseed].
        eapply solver_propagation_conflict_base_recovery__api_reentry;
          [exact Hcancel| |exact Hresident|exact Hlen].
        apply Hreuse.
        eapply minisat_full_completion_implies_base__api_reentry;
          [exact (msa_trail_wf (msas_weak Hentry))|
           exact (msa_db_wf (msas_weak Hentry))|exact Hcompleted]. }
      destruct Hcert as [Hent [Hfalse [Hwf Hcert_tail]]].
      assert (Hunsat : sat_shared_lib.cnf_unsat smp_n_solver_simplify_spec
        (sat_shared_lib.cnf_with_units smp_F_solver_simplify_spec
           smp_A_arr_solver_simplify_spec)).
      { eapply assuming_conflict_unsat; eauto. }
      sep_apply_l_atomic
        (solver_rep_assigns_levels_at_levels_at
           s_pre propagation_result assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec).
  unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at. Right. Exists propagation_result.
  assert (Hbound : cancel_bound_ready propagation_result 0) by (unfold cancel_bound_ready; left; lia).
  msat_manual_entailer_with ltac:(lia || tauto).
Qed.


Lemma proof_of_solver_solve_entail_wit_4_4 : solver_solve_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  msat_solve_lbool_cell_arm Mcur retval_6.
Qed.


Lemma proof_of_solver_solve_entail_wit_5_1_split_goal_1 : solver_solve_entail_wit_5_1_split_goal_1.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_1_split_goal_2 : solver_solve_entail_wit_5_1_split_goal_2.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_1_split_goal_3 : solver_solve_entail_wit_5_1_split_goal_3.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_1 : solver_solve_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - repeat rewrite Z.sub_0_r in *.
    subst retval_2.
    assert (Hcell : lbool_cell
      (Znth (lit_var_c (Znth k raw 0))
        (mt_assigns (ms_core Mcur)) 0)).
    { eapply Forall_Znth_elim.
      - exact (mtw_cells (msa_trail_wf (msas_weak PreH29))).
      - rewrite PreH28.
        assert (Hwf : lit_wf_c n_solver_solve_spec (Znth k raw 0))
          by (apply Forall_lit_wf_Znth; [assumption | lia]).
        exact (lit_var_c_in_range _ _ Hwf). }
    assert (Hreprn :
      signed_last_nbits
        (- Znth (lit_var_c (Znth k raw 0))
          (mt_assigns (ms_core Mcur)) 0) 8 =
      - Znth (lit_var_c (Znth k raw 0))
          (mt_assigns (ms_core Mcur)) 0).
    { apply signed_last_nbits_eq; [lia |].
      unfold lbool_cell in Hcell.
      destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia. }
    pose proof (lit_sign_c_range (Znth k raw 0)) as Hsign.
    assert (Hsign1 : lit_sign_c (Znth k raw 0) = 1) by lia.
    rewrite Hreprn, Hsign1, <- PreH20.
    replace ((1 - 2 * 1) *
      Znth (lit_var_c (Znth k raw 0))
        (mt_assigns (ms_core Mcur)) 0)
      with (- Znth (lit_var_c (Znth k raw 0))
        (mt_assigns (ms_core Mcur)) 0) by ring.
    cancel.
  - entailer_with ltac:(lia || auto).
    all: assert (Hraw : raw <> nil)
      by (intro E; subst raw; cbn in PreH9; lia); auto.
Qed.


Lemma proof_of_solver_solve_entail_wit_7_2 : solver_solve_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  bind_fact ( assumption_propagation_success n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec raw_2 (k_2 + 1) Mprop ) as Hsucc.
  bind_fact ( endvar_pre = begin_pre + Zlength raw_2 * sizeof ( INT ) ) as Hend.
  Exists raw_2 (k_2 + 1) Mprop.
  unfold assumption_propagation_success in Hsucc.
  destruct Hsucc as (Hinv & Hqh & Hpend & Hseed).
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.


Lemma proof_of_solver_solve_entail_wit_7_3 : solver_solve_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (msas_weak PreH13) as Hweak.
  pose proof (msa_trail_wf Hweak) as Hwf.
  assert (Hcurrent_wf : lit_wf_c n_solver_solve_spec (Znth k_2 raw_2 0)).
  { apply (Forall_Znth_elim Z (lit_wf_c n_solver_solve_spec) raw_2 0 k_2 PreH7). lia. }
  pose proof (lit_var_c_in_range _ _ Hcurrent_wf) as Hrange.
  assert (Hcell : lbool_cell (Znth (lit_var_c (Znth k_2 raw_2 0)) (mt_assigns (ms_core Mcur_2)) 0)).
  { apply Forall_Znth_elim; [exact (mtw_cells Hwf)|]. rewrite (mtw_assigns_len Hwf). exact Hrange. }
  exfalso.
  unfold lbool_cell in Hcell.
  unfold lit_sign_c in PreH17, PreH18, PreH19.
  destruct (Z.odd (Znth k_2 raw_2 0)); cbn [Z.mul] in PreH17, PreH18, PreH19;
    unfold lit_var_c in *; intuition nia.
Qed.


Lemma proof_of_solver_solve_entail_wit_8_1_split_goal_spatial : solver_solve_entail_wit_8_1_split_goal_spatial.
Abort.


Lemma proof_of_solver_solve_entail_wit_8_1 : solver_solve_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  assert (HA : A_arr = lits_denote raw).
  { rewrite PreH15.
    unfold assumption_prefix.
    rewrite sublist_self by reflexivity.
    reflexivity. }
  unfold assumption_root_install in PreH3.
  destruct PreH3 as
    [HAinst [HMroot [Hinv [Hatroot [Hpending Hshadow]]]]].
  assert (Hrestart_frame :
      ms_cap Mroot = ms_cap M_solver_solve_spec /\
      (solver_query_reuse_guard M_solver_solve_spec ->
       minisat_base_watch_completed Mroot)).
  { split; assumption. }
  assert (Harray_facts :
      endvar_pre = begin_pre + Zlength raw * sizeof (INT) /\
      A_arr = lits_denote raw /\ Forall (lit_wf_c n) raw /\
      (raw = nil -> valid_int_position begin_pre)).
  { split; [exact PreH13 |].
    split; [exact HA |].
    split; [exact PreH16 |].
    intros _. exact PreH17. }
  unfold solver_restart_loop, assumptions_array.
  Exists raw.
  cancel.
  Exists Mroot A_inst.
  Right.
  unfold solver_search_pre.
  rewrite <- PreH13.
  pre_process_default.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_21_pure : solver_solve_partial_solve_wit_21_pure.
Proof.
  msat_solve_close_assumption_lit_bounds k.
Qed.


Lemma proof_of_solver_solve_return_wit_2 : solver_solve_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_unsat_arm_at. Intros. Exists Munsat_2.
  msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_safety_wit_5 : solver_solve_safety_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_solve_assign_cell_not_int_min retval.
Qed.


Lemma proof_of_assume_return_wit_1 : assume_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst s_pre.
  bind_fact ( Zlength assigns = n ) as H_Zlength.
  bind_fact ( Zlength trail = qtail ) as H_Zlength_2.
  unfold assume_post_at.
  unfold enqueue_post_at.
  Intros qtail' assigns' levels' reasons' trail'.
  rename H into Htrans.
  assert (Hret : retval = 1).
  { unfold enqueue_transition in Htrans.
    destruct Htrans as
      [(Hassigned & _)|[(Hnonzero & _)|(Hzero & Hret & _)]];
      try congruence.
    exfalso.
    apply (lit_sig_nonzero l0).
    congruence. }
  subst retval.
  Exists qtail' assigns' levels' reasons' trail'.
  rewrite H_Zlength_2 in Htrans.
  rewrite H_Zlength, H_Zlength_2.
  msat_manual_entailer_with lia.
Qed.


Lemma proof_of_assume_which_implies_wit_2 : assume_which_implies_wit_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 prop_apply_p (CharArray.seg_Zlength asg 0 n assigns). Intros. assert (Hlen : Zlength assigns = n) by lia. rewrite Hlen. sep_apply_l_atomic (CharArray.seg_split_to_missing_i asg 0 (lit_var_c l0) n assigns 0 ltac:(lia)). unfold StoreCharAsElement.storeA. rewrite !Z.sub_0_r. cancel.
Qed.


Lemma proof_of_enqueue_partial_solve_wit_7_pure : enqueue_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_manual_entailer_with ltac:(unfold enqueue_input in PreH8; intuition lia).
Qed.


Lemma proof_of_solver_addclause_entail_wit_5 : solver_addclause_entail_wit_5.
Proof.
(* After setnvars, rebuild literal well-formedness from literal-variable
   bounds. The old caller bound need not be below the new size, so monotonic
   transport is unavailable. *)
(LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign.
sep_apply (store_ptr_undef_store_ptr &( "i")).
match goal with
| HI : solver_support_inv _ _ _ _ 0 ac_M_addclause_spec |- _ =>
    pose proof (msw_F_wf (msi_weak HI)) as Hinput_formula_wf
end.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
try ac_shape.
assert (Hnil : rest = nil) by (apply (app_nil_of_Zlength sorted rest); ac_arith).
subst rest. try rewrite app_nil_r in *.
match goal with
| H : Permutation sorted _ |- _ =>
    pose proof (all_from_of_Permutation _ _ H)
end.
assert (Hwf : Forall (lit_wf_c (ms_size Mnew_2)) sorted).
{ match goal with
  | Hp : Forall (fun x : Z => 0 <= x) sorted,
    Hb : Forall (fun x : Z => lit_var_c x <= maxvar) sorted |- _ =>
      rewrite Forall_forall in Hp, Hb |- *;
      intros x Hx; apply (lit_wf_c_of_var_bound maxvar);
        [ apply Hp, Hx | apply Hb, Hx | ac_arith ]
  end.
}
assert (Hinput_wf : Forall (lit_wf_c ac_n_addclause_spec)
    ac_input_addclause_spec).
{ eapply Permutation_Forall; eassumption. }
match goal with
| H : (_ /\ _ /\ _ ->
       Zlength (mt_lim (ms_core Mnew_2)) = 0 /\
       ms_capacity_root_propagation_pending Mnew_2 = 0 /\ msolver_seed_shadow Mnew_2) |- _ =>
    let Hroot := fresh "Hroot" in
    pose proof (H ltac:(split; [ | split ]; assumption)) as Hroot;
    destruct Hroot as [Hlim0 [Hpending0 Hseed0]]
end.
assert (Hphysical_shape : solver_shape Mnew_2).
{ eapply (solver_shape_restore_physical_root__api_reentry Mnew_2 0).
  - match goal with HI : solver_support_inv _ _ _ _ 0 Mnew_2 |- _ =>
      exact (msi_shape HI)
    end.
  - match goal with Hr : ms_root_level Mnew_2 = ms_root_level ac_M_addclause_spec |- _ =>
      rewrite Hr
    end. assumption.
  - intro Hpending. rewrite Hpending0 in Hpending. discriminate. }
sep_apply solver_rep_growable_focus_open_wl.
Intros asg lvl wl.
Exists wl lvl asg sorted Mnew_2.
msat_manual_entailer_with ltac:(ac_close).
Qed.


Lemma proof_of_solver_addclause_entail_wit_7_2 : solver_addclause_entail_wit_7_2.
Proof.
(* KEEP branch of the dedup-loop entailment; same body as entail_wit_7_1. *)
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_keep sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 last Mnew endvar_pre.
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_1_pure : solver_addclause_partial_solve_wit_1_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst.
pose proof (Zlength_nonneg ac_input_addclause_spec).
pose proof (Z.max_spec (ms_cap ac_M_addclause_spec) (INT_MAX ÷ 4)) as Hmax.
split_pures.
- dump_pre_spatial. assumption.
- dump_pre_spatial. reflexivity.
- dump_pre_spatial. assumption.
- dump_pre_spatial. assumption.
- dump_pre_spatial.
  assert (Hdiv : (2147483647 ÷ 4) = 536870911) by reflexivity.
  rewrite Hdiv in *; destruct Hmax as [[? ?]|[? ?]]; lia.
- dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_addclause_partial_solve_wit_17_pure : solver_addclause_partial_solve_wit_17_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Hmax : 0 <= maxvar /\ maxvar < ac_n_addclause_spec).
{ match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ => unfold addclause_sort_outer_inv in H; tauto end. }
msat_manual_entailer_with ltac:(lia || assumption).
Qed.


Lemma proof_of_solver_addclause_return_wit_3_split_goal_spatial : solver_addclause_return_wit_3_split_goal_spatial.
Proof.
Abort.


Lemma proof_of_solver_addclause_return_wit_3 : solver_addclause_return_wit_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  assert (Hnil : kept = nil) by (apply Zlength_nil_inv; ac_arith).
  assert (Hunsat : cnf_unsat
      (Z.max (ms_size ac_M_addclause_spec) ac_n_addclause_spec)
      (ac_F_addclause_spec ++ (lits_denote ac_input_addclause_spec :: nil))).
  { apply addclause_empty_unsat.
    - apply addclause_formula_wf; assumption.
    - rewrite Hnil in *; assumption. }
  split_pure_spatial.
  - msat_addclause_return_frame Mnew kept tail ac_F_addclause_spec
      (left; split; [reflexivity |]; split; [reflexivity |];
       split; [assumption | exact Hunsat]).
  - msat_manual_entailer_with ltac:(reflexivity || lia).
Qed.


Lemma proof_of_solver_addclause_return_wit_8_split_goal_spatial : solver_addclause_return_wit_8_split_goal_spatial.
Proof.
Abort.


Lemma proof_of_solver_addclause_return_wit_8 : solver_addclause_return_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  ac_shape.
  assert (Hnil : ac_input_addclause_spec = nil)
    by (apply Zlength_nil_inv; rewrite ?sizeof_int in *; lia).
  rewrite Hnil; split_pure_spatial.
  - sep_apply (addclause_support_post_empty__api_reentry s_pre begin_pre
      ac_n_addclause_spec ac_F_addclause_spec ac_A_arr_addclause_spec
      ac_A_inst_addclause_spec ac_M_addclause_spec PreH4 PreH9); cancel.
  - msat_manual_entailer_with ltac:(reflexivity).
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_6 : solver_addclause_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_split_after_llm;
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_nconflicts_return_wit_1 : solver_nconflicts_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_conflict_count_cell in *.
  rewrite minisat_signed32_cast_eq_signed_low32.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (reflexivity)] ..]).
Qed.


Lemma proof_of_solver_nconflicts_which_implies_wit_1 : solver_nconflicts_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_progress_return_wit_1 : solver_progress_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_record_return_wit_1 : solver_record_return_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
pose proof (record_finish_publish_inv _ _ _ _ _ _ _ _ _ _ PreH1) as Hpost.
 unfold solver_record_post_at. Exists Mstats.
 sep_apply Veci.rep_ptr_rep. msat_manual_entailer_with ltac:(lia || tauto).
Qed.



Lemma proof_of_solver_record_return_wit_2 : solver_record_return_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst c. pose proof PreH2 as Hsucc. pose proof PreH3 as Halloc.
 destruct Halloc as [[[Hlen [Hc Hstage]]|[Hlen [Hnz Htrans]]] Hrest]; [|contradiction].
 subst Mstage. destruct Hsucc as [Henq [Hinv [Hp [Hseed [Hmodel [Hdecay [Hcap Hreuse]]]]]]].
 assert (Hdb : ms_learnt Menq = ms_learnt M0) by (subst Menq; reflexivity).
 rewrite <- Hdb. sep_apply record_rep_close.
 unfold solver_record_post_at. Exists Menq.
 sep_apply Veci.rep_ptr_rep. msat_manual_entailer_with ltac:(lia || tauto).
Qed.



Lemma proof_of_solver_search_entail_wit_4_2 : solver_search_entail_wit_4_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at. Split.
- Intros Mclean. Exists Mclean.
  sep_apply (store_ptr_undef_store_ptr &( "confl")).
  match goal with
  | H : ms_cap Mclean = ms_cap Mstable /\ _ |- _ =>
    destruct H as [Hcap [Hroot [Hstrong [Hreuse [Hdepth [Hdrain [Hpending [Hseed [Hmodel Hdecay]]]]]]]]]
  end.
  assert (Hinv : msolver_inv n F A_arr nil Mclean).
  { apply solver_assuming_zero_stable__api_reentry; [exact Hstrong|exact Hdepth|lia]. }
  assert (Hreuse_new : solver_search_reuse M0 Mclean).
  { intro Hbase. eapply minisat_full_completion_implies_base__api_reentry.
    - exact (msi_trail_wf Hinv).
    - exact (msi_db_wf Hinv).
    - apply Hreuse. left. eapply minisat_base_completion_at_depth_zero__api_reentry.
      + exact (msi_trail_wf PreH10).
      + exact (msi_db_wf PreH10).
      + lia.
      + apply PreH9. exact Hbase. }
  subst A_inst. msat_manual_entailer_with ltac:(lia || tauto).
- Intros Mclean. (repeat split; solve [auto | (lia)]).
Qed.


Lemma proof_of_solver_search_return_wit_1 : solver_search_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_result.
  Left. Left.
  Exists Mmodel_root.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_1 : solver_search_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_pre.
  Intros.
  sep_apply solver_rep_cancel_split.
  Intros lvl.
  Exists lvl.
  unfold solver_levels_slice_at.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_4_split_goal_1 : solver_search_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_4 : solver_search_which_implies_wit_4.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_search_which_implies_wit_4_split_goal_1 M0 PreH1).
Qed.


Lemma proof_of_solver_search_which_implies_wit_17 : solver_search_which_implies_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_backjump_ready n F A_arr A_inst Mcur Mback words ) as H_solver_search_backjump_ready.
  unfold solver_search_backjump_ready in H_solver_search_backjump_ready.
  destruct H_solver_search_backjump_ready as
    [Hinv [Hrecord [Hpositive [Hqtail [Hpending [Hseed [Hmodel [Hdecay Hdecay_eq]]]]]]]].
  unfold solver_record_pre_at.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_entail_wit_3_2_split_goal_1 : solver_setnvars_entail_wit_3_2_split_goal_1.
Proof.
Abort.


Lemma proof_of_solver_setnvars_entail_wit_3_2_split_goal_2 : solver_setnvars_entail_wit_3_2_split_goal_2.
Proof.
Abort.


Lemma proof_of_solver_setnvars_entail_wit_3_2 : solver_setnvars_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists wl act asg opos rsn lvl trl tgs sn_M_setnvars_spec.
  split_pure_spatial.
  - repeat cancel; apply store_int_undef_store_int.
  - split_pures; dump_pre_spatial.
    all: first [reflexivity | assumption | apply setnvars_core_equiv_refl
      | apply setnvars_bound_entry; unfold solver_shape in PreH3; tauto
      | lia | tauto].
Qed.


Lemma proof_of_solver_setnvars_return_wit_1 : solver_setnvars_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpublish : n_pre = ms_size Mcur).
  { pose proof (setnvars_bound_exit (ms_size sn_M_setnvars_spec) var n_pre PreH5 ltac:(lia)) as Heq. lia. }
  rewrite Hpublish.
  all: (snv_shape);
    (match goal with
  | HS : ms_size ?M = ?v,
    HI : solver_support_inv ?v ?F ?A ?B ?root ?M |- _ =>
      let H := fresh "HIsz" in
      pose proof HI as H; rewrite <- HS in H
  end).
  all: match goal with H : setnvars_core_equiv ?M0 ?M |- _ =>
    pose proof (setnvars_core_equiv_root_summary M0 M H) as Hroot_summary;
    assert (Hphysical_root : ms_root_level M = ms_root_level M0)
      by (unfold setnvars_core_equiv in H; tauto)
  end.
  all: (Exists Mcur);
    (pose proof (setnvars_bound_exit (ms_size sn_M_setnvars_spec) var n_pre
                ltac:(assumption) ltac:(lia)));
    (match goal with HS : ms_size ?M = ?v |- _ => rewrite <- HS end).
  all: (snv_unfold_all_unfolded_post);
    (Exists wlc actc asgc oposc rsnc lvlc trlc tgsc);
    (msat_manual_entailer_with ltac:(snv_dispatch)).
Qed.


Lemma proof_of_solver_simplify_entail_wit_1 : solver_simplify_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( ms_model M_solver_simplify_spec = nil -> ms_model Mprop = nil ) as H_model_empty.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
    msat_fp32_positive_finite (ms_cla_decay Mprop) ) as H_decay_positive.
  unfold solver_simplify_outer_loop.
  Exists Mprop.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    intuition lia.
Qed.


Lemma proof_of_solver_simplify_partial_solve_wit_17_pure : solver_simplify_partial_solve_wit_17_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  pose proof H_solver_simplify_db_compaction_inv as Hcompact.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [_ [Hj [Hji _]]].
  assert (Hi : i < Zlength words) by lia. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_11 : solver_simplify_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( db_lookup (solver_selected_db type Mcur) (Znth (i - 0) words 0) co ) as H_db_lookup.
  bind_fact ( Znth (lit_var_c (Znth (0 - 0) (co_lits co) 0) - 0) (ms_reason_words Mcur) 0 <> Znth (i - 0) words 0 ) as
      H_Znth.
  bind_fact ( Znth (i - 0) words 0 % 2 = 0 ) as H_Znth_2.
  pose proof (msas_weak H_msolver_inv) as Hweak.
  bind_fact (Zlength (mt_lim (ms_core Mcur)) = 0) as Hdepth.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    smp_n_solver_simplify_spec smp_F_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mcur H_msolver_inv Hdepth) as Hnormal.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof (msa_size Hweak) as Hsize.
  assert (Hin_selected :
    In (Znth (i - 0) words 0, co) (solver_selected_db type Mcur)).
  { exact H_db_lookup. }
  assert (Hin_db : In (Znth (i - 0) words 0, co) (msolver_db Mcur)).
  { eapply solver_selected_db_in_any__simplify.
    exact Hin_selected. }
  assert (Hready_n : clause_remove_ready smp_n_solver_simplify_spec
    (Znth (i - 0) words 0) (co_lits co) (ms_wm Mcur) (ms_stats Mcur)).
  { eapply clause_remove_ready_of_inv__simplify with
      (M := msolver_set_root Mcur 0); [exact Hnormal|exact Hin_db]. }
  assert (Hready : clause_remove_ready (ms_size Mcur)
    (Znth (i - 0) words 0) (co_lits co) (ms_wm Mcur) (ms_stats Mcur)).
  { rewrite <- Hsize. exact Hready_n. }
  assert (Hunlocked : clause_unlocked_words (Znth (i - 0) words 0)
    (ms_reason_words Mcur)).
  { eapply solver_simplify_head_unlocked with (M := msolver_set_root Mcur 0);
      [exact (msi_weak Hnormal) | exact Hin_db |].
    unfold co_watch0.
    replace (0 - 0) with 0 in H_Znth by lia.
    replace (lit_var_c (Znth 0 (co_lits co) 0) - 0)
      with (lit_var_c (Znth 0 (co_lits co) 0)) in H_Znth by lia.
    exact H_Znth. }
  unfold clause_remove_pre, MiniSatClause.rep.
  unfold solver_shape in Hshape.
  rewrite Z.rem_mod_nonneg in H_Znth_2 by lia.
  split_pure_spatial.
  - cancel (solver_wlists_handle s smp_wl_solver_simplify_spec).
    cancel.
  - split_pures; dump_pre_spatial; intuition lia.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_8_pure : solver_solve_partial_solve_wit_8_pure.
Proof.
  msat_solve_close_assumption_lit_bounds k.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_4 : solver_solve_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( i = begin + k * sizeof ( INT ) ) as H_i.
  bind_fact ( endvar = begin + Zlength raw * sizeof ( INT ) ) as H_endvar.
  bind_fact ( Forall (lit_wf_c n_solver_solve_spec) raw ) as H_Forall.
  assert (Hklt : k < Zlength raw).
  { rewrite sizeof_int in H_i, H_endvar. lia. }
  assert (Hlit : lit_wf_c n_solver_solve_spec (Znth k raw 0)).
  { apply (Forall_Znth_elim Z (lit_wf_c n_solver_solve_spec) raw 0 k H_Forall). lia. }
  assert (Hvar : 0 <= lit_var_c (Znth k raw 0) < n_solver_solve_spec).
  { apply lit_var_c_in_range. exact Hlit. }
  unfold lit_wf_c in Hlit.
  replace (k - 0) with k by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_6 : solver_solve_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hweak.
  pose proof (msa_trail_wf Hweak) as Hwf.
  pose proof (msa_shape Hweak) as Hshape.
  assert (Hcurrent_wf : lit_wf_c n (Znth k raw 0)).
  { eapply Forall_Znth_elim; eauto. }
  assert (Hvar_range : 0 <= lit_var_c (Znth k raw 0) < n)
    by (apply lit_var_c_in_range; exact Hcurrent_wf).
  assert (Hmissing : ~ In (lit_var_c (Znth k raw 0))
      (map lit_var_c (mt_trail (ms_core Mcur)))).
  { intro Hin.
    apply (proj2 (mtw_assigned_iff Hwf _ Hvar_range)) in Hin.
    contradiction. }
  assert (Htrail_lits :
      Forall (lit_wf_c n)
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil))).
  { apply Forall_app. split; [exact (mtw_trail_lits Hwf)|].
    constructor; [exact Hcurrent_wf|constructor]. }
  assert (Htrail_nodup :
      NoDup (map lit_var_c
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)))).
  { rewrite map_app. simpl. apply NoDup_snoc.
    - exact (mtw_trail_nodup Hwf).
    - exact Hmissing. }
  assert (Htrail_lt : Zlength (mt_trail (ms_core Mcur)) < n).
  { pose proof (msat_map_lit_var_c_in_range n
      (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)) Htrail_lits) as Hall.
    pose proof (NoDup_Z_bounded_length
      (map lit_var_c
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)))
      n (mtw_n_nonneg Hwf) Htrail_nodup Hall) as Hle.
    assert (Hle' : Zlength
        (mt_trail (ms_core Mcur) ++ (Znth k raw 0 :: nil)) <= n).
    { rewrite length_map in Hle. rewrite Zlength_correct. exact Hle. }
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hle'. lia. }
  assert (Hlim_le : Zlength (mt_lim (ms_core Mcur)) <=
      Zlength (mt_trail (ms_core Mcur))).
  { eapply strict_sorted_bounded_length__solve.
    - apply Zlength_nonneg.
    - exact (mtw_lim_sorted Hwf).
    - exact (mtw_lim_range Hwf). }
  assert (Henqueue : enqueue_input n (Znth k raw 0) (ms_qtail Mcur)
      (mt_assigns (ms_core Mcur)) (mt_levels (ms_core Mcur))
      (ms_reason_words Mcur) (mt_trail (ms_core Mcur))).
  { unfold enqueue_input.
    unfold solver_shape in Hshape.
    rewrite <- (msa_size Hweak) in Hshape.
    split; [exact Hcurrent_wf|].
    repeat split; try tauto; try lia.
    pose proof (mtw_cells Hwf) as Hcells. revert Hcells.
    apply Forall_impl. intros x Hx. unfold lbool_cell in Hx.
    destruct Hx as [Hx|[Hx|Hx]]; subst x; lia. }
  unfold assumption_fresh_ready.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      split; [rewrite <- (msa_size Hweak); reflexivity |].
      split; [lia |].
      split; [lia |].
      split; [lia | exact Henqueue].
Qed.


Lemma proof_of_solver_solve_which_implies_wit_17 : solver_solve_which_implies_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstatus : status = 0) by lia.
  subst status.
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
    + Intros Mbad. Intros. cancel. exfalso; lia.
    + Intros Mbad. Intros. cancel. exfalso; lia.
  - Intros Msearch.
    match goal with
    | Hpost : ms_cap Msearch = ms_cap search_entry /\ _ |- _ =>
        destruct Hpost as (Hcap & Hreuse & Hinv & Hroot & Hdrain & Hpending & Hseed)
    end.
    lazymatch type of Hentry_watch with
    | solver_query_reuse_guard ?entry -> _ =>
        assert (Hwatch : solver_query_reuse_guard entry ->
            minisat_base_watch_completed Msearch)
          by (intro Hready; exact (Hreuse (Hentry_watch Hready)))
    end.
    sep_apply (store_char_undef_store_char &("status") 0).
    Exists A_inst Msearch.
    unfold solver_search_pre.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
    }
  - unfold solver_search_pre. Intros.
    sep_apply (store_char_undef_store_char &("status") 0).
    Exists A_inst search_entry.
    unfold solver_search_pre.
    msat_manual_entailer_with ltac:(tauto).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_18 : solver_solve_which_implies_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_restart_loop.
  Exists Msearch A_search.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (tauto)] ..]).
  Left. cancel.
Qed.


Lemma proof_of_solver_record_partial_solve_wit_13_pure : solver_record_partial_solve_wit_13_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 match goal with Hs : record_enqueue_success _ _ _ _ _ _ _ _ _ |- _ => pose proof (msi_cla_inc_nonnegative (proj1 (proj2 Hs))) as Hcla end.
 split_pures; dump_pre_spatial; tauto.
Qed.



Lemma proof_of_solver_record_partial_solve_wit_15_pure : solver_record_partial_solve_wit_15_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 match goal with H : record_enqueue_success _ _ _ _ _ _ _ _ _ |- _ => pose proof H as Hsucc end.
 match goal with H : record_allocated _ _ _ _ _ _ _ _ |- _ => pose proof H as Halloc end.
 destruct Hsucc as [Henq [Hinv Hrest]].
 pose proof (msi_learnt_db Hinv) as Hlearnt.
 destruct Halloc as [[[Hlen [Hzero Hsame]]|[Hlen [Hcnz Htrans]]] _]; [congruence|].
 pose proof (clause_new_success_installs_word__record _ _ _ _ _ _ _ _ Htrans) as Hin_stage.
 assert (Heq : ms_learnt Menq = ms_learnt Mstage) by (subst Menq; reflexivity).
 assert (Hin : In c (db_words (ms_learnt Menq))) by (rewrite Heq; exact Hin_stage).
 split_pures; dump_pre_spatial; tauto.
Qed.



Lemma proof_of_solver_record_which_implies_wit_3 : solver_record_which_implies_wit_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 destruct rec_words as [|a l0].
 - unfold IntArray.missing_i; simpl. Intros. contradiction.
 - pose proof (IntArray.missing_i_merge_to_seg learnt_ptr 0 0 (Zlength (a :: l0))
     (Znth 0 (a :: l0) 0) (a :: l0) ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l0); lia)) as Hm.
   rewrite Z.sub_0_r, replace_Znth_Znth in Hm.
   unfold StoreIntAsElement.storeA in Hm. rewrite Z.mul_0_l, Z.add_0_r in Hm.
   sep_apply Hm. cancel.
Qed.
