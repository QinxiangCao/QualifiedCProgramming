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
Lemma proof_of_assume_entail_wit_2_split_goal_1 : assume_entail_wit_2_split_goal_1.
Abort.


Lemma proof_of_assume_entail_wit_2_split_goal_2 : assume_entail_wit_2_split_goal_2.
Abort.


Lemma proof_of_assume_entail_wit_2 : assume_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH12 as Hinput.
  unfold enqueue_input in Hinput.
  destruct Hinput as (_ & _ & _ & _ & _ & _ & Htail & _ & _).
  pose proof (Zlength_nonneg (lim ++ (qtail :: nil))) as Hlength.
  unfold enqueue_state_at.
  Exists rsn trl.
  entailer!.
Qed.


Lemma proof_of_solver_addclause_entail_wit_2_1 : solver_addclause_entail_wit_2_1.
Proof.
  (* Inner-loop ESTABLISHMENT, `lv > maxvar' branch: j = i, so the sorted prefix
     is all of [sorted] with an empty [suf], and the element being inserted is
     the HEAD of the unsorted remainder.  maxvar is raised to its var. *)
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout].
  subst retval endvar_pre.
  assert (Hrne : rest <> nil).
  { intro Hn; rewrite Hn in *;
    rewrite ?Zlength_app, ?Zlength_nil in *; lia. }
  destruct rest as [|r0 rst]; [contradiction|].
  (* the read index appears as [k - 0] in some places and, once k has been
     substituted, as [Zlength sorted - 0] in others -- normalise both. *)
  try (replace (k - 0) with (Zlength sorted) in * by lia).
  try (replace (Zlength sorted - 0) with (Zlength sorted) in * by lia).
  rewrite (Znth_app_hd sorted r0 rst 0) in *.
  Exists (sorted ++ r0 :: rst) r0 rst (@nil Z) sorted k.
  rewrite app_nil_r.
  split_pure_spatial.
  - msat_manual_entailer_with ltac:(lia).
  - split_pures; dump_pre_spatial; try solve [ auto | ac_close ].
    + unfold addclause_sort_inner_inv; rewrite ?app_nil_r;
        repeat split; [ assumption | constructor ].
    + apply (addclause_sort_outer_maxvar_mono ac_n_addclause_spec maxvar (lit_var_c r0));
        [ exact Hout | lia
        | pose proof (lit_var_c_in_range ac_n_addclause_spec r0 ltac:(assumption)); lia
        | pose proof (lit_var_c_in_range ac_n_addclause_spec r0 ltac:(assumption)); lia ].
    (* [ac_znth] will NOT pose the var-range fact here: its arm is guarded on
       [0 <= x] not already being known, and the annotation already supplies
       that -- so the whole arm, including the range, is skipped. Pose it. *)
    + pose proof (lit_var_c_in_range ac_n_addclause_spec r0 ltac:(assumption)). lia.
Qed.


Lemma proof_of_solver_addclause_entail_wit_6 : solver_addclause_entail_wit_6.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign.
  assert (Hl : Zlength sortedf = Zlength ac_input_addclause_spec)
    by (eapply Permutation_Zlength_Z; eassumption).
  assert (Hprefix : addclause_prefix_equiv ac_F_addclause_spec
      (sublist 0 0 sortedf) nil).
  { rewrite Zsublist_nil by lia. apply addclause_prefix_nil. }
  Exists sortedf (@nil Z) 0 0.
  (* the engine SOLVES [tail] from [tail == sublist(q, n, sortedf)]; at entry
     q = 0, so the witness it picks is [sublist (Zlength nil) n sortedf] --
     a redex.  Normalise it back to [sortedf] BEFORE entailing, or every
     conjunct is stated about an un-reduced term and nothing matches. *)
  (* A bare [rewrite Zlength_nil] finds no subterm here -- the goal's occurrence
     is [@Zlength Z nil] and the lemma's implicit does not line up through the
     entailment.  Routing through an explicitly-typed equation does match. *)
  assert (Hz : Zlength (@nil Z) = 0) by apply Zlength_nil.
  assert (Hs0 : sublist 0 (Zlength ac_input_addclause_spec) sortedf = sortedf)
    by (rewrite <- Hl; apply sublist_self; reflexivity).
  rewrite Hz, Hs0, ?app_nil_l.
  sep_apply (store_int_undef_store_int &( "maxvar") maxvar).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try solve [ auto | ac_close ].
    + eapply all_ge_sentinel; eassumption.
    + apply addclause_dedup_inv_nil.
Qed.


Lemma proof_of_solver_addclause_return_wit_7_split_goal_spatial : solver_addclause_return_wit_7_split_goal_spatial.
Abort.


Lemma proof_of_solver_addclause_return_wit_7 : solver_addclause_return_wit_7.
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
  all: try solve [msat_manual_entailer_with ltac:(reflexivity || lia)].
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_1 : solver_addclause_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_split_after_llm;
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_canceluntil_partial_solve_wit_8_pure : solver_canceluntil_partial_solve_wit_8_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto));
    replace (c - 0) with c in * by lia; subst retval; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_canceluntil_which_implies_wit_1 : solver_canceluntil_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- solver_cancel_pre ?s ?level ?M ?wl |-- _ =>
      sep_apply (solver_cancel_pre_open s level M wl)
  end.
  Intros activity assigns orderpos reasons trail.
  Exists activity assigns orderpos reasons trail.
  msat_manual_entailer_with ltac:(intuition lia).
Qed.


Lemma proof_of_solver_canceluntil_which_implies_wit_3 : solver_canceluntil_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (CharArray.seg_split_to_missing_i assigns_ptr 0 x (ms_size M0)
      assigns_now 0).
  - dump_pre_spatial. lia.
  - replace (x - 0) with x by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_canceluntil_which_implies_wit_4 : solver_canceluntil_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (PtrArray.seg_split_to_missing_i reasons_ptr 0 x (ms_size M0)
      reasons_now 0).
  - dump_pre_spatial. lia.
  - replace (x - 0) with x by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_new_which_implies_wit_3 : solver_new_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (Z.rem initial_binary_raw 2 = 0) as Hrem.
  assert (Hmod : Z.modulo initial_binary_raw 2 = 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact Hrem. }
  Exists initial_binary_raw.
  lazymatch goal with
  | |- ?L |-- _ => set (Hlhs := L)
  end.
  unfold solver_initial_layout, stats_rep, binary_scratch_rep.
  split_pure_spatial.
  2: (split_pures; dump_pre_spatial; first [reflexivity | tauto | lia]).
  unfold solver_vecs_rep.
  cbn [solver_initial_model solver_initial_core ms_prob ms_learnt ms_tagged
    ms_stack ms_order ms_core mt_lim ms_model map].
  unfold Hlhs.
  unfold solver_scalars_rep, solver_fp_rep, solver_ptrs_rep.
  unfold clause_hdr_addr, clause_act_addr, clause_lits_addr, clause_hdr_word,
    activity_state, stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals,
    solver_initial_model, solver_initial_core, msat_fp64_seed.
  cbn.
  unfold clause_act_addr, clause_lits_addr, msat_seed_default.
  cbn [Pos.to_nat].
  rewrite <- !msat_dot_field_addr_arrow.
  unfold Pos.to_nat.
  cbn [Pos.iter_op Nat.add].
  msat_cancel_sound.
  solve [ change (emp |-- emp); cancel | Intros; cancel ].
Qed.


Lemma proof_of_solver_nvars_return_wit_1 : solver_nvars_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_search_entail_wit_2_1_split_goal_1 : solver_search_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( ms_root_level Manalyzed > Znth (retval_5 - 0) (mt_levels (ms_core Manalyzed)) 0 ) as H_ms_root_level.
  bind_fact ( retval_5 = lit_var_c (Znth (1 - 0) words 0) ) as H_retval_5.
  bind_fact ( analyze_backjump_cert n Manalyzed words backjump ) as H_analyze_backjump_cert.
  unfold analyze_backjump_cert in H_analyze_backjump_cert.
  destruct H_analyze_backjump_cert as [_ [Hback _]].
  assert (Hlt : Z.ltb 1 (Zlength words) = true).
  { apply Z.ltb_lt. lia. }
  rewrite Hlt in Hback.
  rewrite Hback.
  rewrite H_retval_5 in H_ms_root_level.
  replace (1 - 0) with 1 in H_ms_root_level by lia.
  replace (lit_var_c (Znth 1 words 0) - 0)
    with (lit_var_c (Znth 1 words 0)) in H_ms_root_level by lia.
  symmetry.
  apply Z.max_l.
  lia.
Qed.


Lemma proof_of_solver_search_entail_wit_2_1 : solver_search_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_search_entail_wit_2_1_split_goal_1.
Qed.



Lemma proof_of_solver_search_entail_wit_4_3 : solver_search_entail_wit_4_3.
Proof.
LLM_pre_process ltac:(lia || int_auto). unfold solver_simplify_post_at, solver_simplify_post_sat_at, solver_simplify_post_unsat_at in *.
    Split.
- Intros Mclean. (repeat split; solve [auto | (lia)]).
- Intros Mclean. (repeat split; solve [auto | (lia)]).
Qed.


Lemma proof_of_solver_search_entail_wit_4_6 : solver_search_entail_wit_4_6.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists Mstable.
sep_apply (store_ptr_undef_store_ptr &( "confl") 0).
unfold solver_search_root_frame_at, solver_search_bundle_at, solver_search_payload, solver_rep_levels_wl_at.
unfold solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_scalars_rep, solver_scalars_without_root_rep, clause_new_scalars_frame,
  solver_vecs_rep, solver_vecs_without_lim_rep.
Intros act asg opos rsn trl tgs.
Exists act asg opos rsn trl tgs.
msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_return_wit_2 : solver_search_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_result.
  Right.
  Exists Mrestart.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_16 : solver_search_which_implies_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready n F A_arr (PropagationStable A_inst) Manalyzed focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert n F Manalyzed words ) as H_analyze_clause_cert.
  bind_fact ( analyze_backjump_cert n Manalyzed words blevel ) as H_analyze_backjump_cert.
  bind_fact ( msolver_seed_shadow Manalyzed ) as H_msolver_seed_shadow.
  bind_fact ( ms_model Manalyzed = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Manalyzed) ) as H_msat_fp32_positive_finite.
  bind_fact ( ms_model Mcur = nil ) as H_ms_model_2.
  bind_fact ( msat_fp32_same (ms_cla_decay Manalyzed) (ms_cla_decay Mcur) ) as H_msat_fp32_same.
  sep_apply (store_int_undef_store_int &( "blevel") blevel).
  unfold solver_cancel_post.
  Split.
  - Intros.
    destruct H_analyze_backjump_cert as [Hlen [Hleveldef [Hrootle [Hlevel Hrest]]]].
    (repeat split; solve [auto | (lia)]).
  - Intros orderpos order.
    destruct H as (Hlevel & Hheap & Hincl & Hreinserted).
    set (Mback := msolver_cancel_project Manalyzed blevel
      orderpos order (ms_root_level Manalyzed)).
    Exists Mback.
    split_pure_spatial.
    + unfold Mback.
      sep_apply (solver_cancel_project_join_rep_levels_at s Manalyzed levels
        blevel orderpos order (ms_root_level Manalyzed) search_wl).
      cancel.
    + unfold solver_cancel_owned.
      Intros act asg opos rsn trl tgs.
      bind_fact (solver_shape Mback) as Hshape_back.
      pose proof H_analysis_cancel_ready as Hreadycopy.
      destruct Hreadycopy as [Morigin [Hcancel0 [Hequiv Hreadyrest]]].
      destruct Hcancel0 as [[Hpending0 Hweak0] Hcancelrest].
      destruct Hreadyrest as [Hheap_cur Hreadyrest].
      assert (Hsize_cur : n = ms_size Manalyzed).
      { pose proof Hequiv as Hequiv_size.
        unfold analysis_core_equiv in Hequiv_size.
        destruct Hequiv_size as [Esize _].
        rewrite Esize. exact (msw_size Hweak0). }
      assert (Horderpos_cur :
          Zlength (ms_orderpos Manalyzed) = ms_size Manalyzed).
      { pose proof (proj1 Hheap_cur) as Horderpos_n.
        unfold msolver_heap in Horderpos_n; simpl in Horderpos_n.
        rewrite Horderpos_n. exact Hsize_cur. }
      assert (Hshape_cur : solver_shape Manalyzed).
      { eapply solver_shape_before_cancel_project__search
          with (M0 := Morigin) (level := blevel) (orderpos := orderpos)
            (order := order)
            (root := ms_root_level Manalyzed).
        - exact Hequiv.
        - exact (msw_shape Hweak0).
        - exact Horderpos_cur.
        - exact Hshape_back. }
      assert (Hweak_cur : msolver_inv_weak n F A_arr A_inst Manalyzed).
      { eapply analysis_cancel_ready_weak__search; eauto. }
      destruct (analysis_cancel_ready_cancel_facts__search
        n F A_arr A_inst Manalyzed focus H_analysis_cancel_ready) as
        [Hpending [Hprop [Hfocuswf [Hfocuslevel
          [Hfront [Hcovers Hreasonless]]]]]].
      destruct H_analyze_backjump_cert as
        [Hlen [Hleveldef [Hrootle [Hblevel [Hheadlevel Htaillevels]]]]].
      assert (Hweak_back : msolver_inv_weak n F A_arr A_inst Mback).
      { unfold Mback.
        eapply msolver_inv_weak_cancel_below__search;
          eauto. }
      assert (Htrail : mtrail_wf n (ms_core Manalyzed)).
      { exact (msw_trail_wf Hweak_cur). }
      assert (Hprop_back : prop_level (ms_core Mback)).
      { unfold Mback. eapply prop_level_cancel; eauto. }
      assert (Hwatch_back : minisat_watch_frontier n (msolver_db Mback)
          (mt_assigns (ms_core Mback)) (mt_trail (ms_core Mback))
          (mt_qhead (ms_core Mback))).
      { unfold Mback. simpl.
        eapply minisat_watch_frontier_cancel_current_level; eauto. }
      assert (Hbound : Znth blevel (mt_lim (ms_core Manalyzed)) 0 <=
          mt_qhead (ms_core Manalyzed)).
      { eapply Forall_Znth_elim; [exact Hprop|lia]. }
      assert (Hheap_back : heap_covers n (msolver_heap Mback)
          (mt_assigns (ms_core Mback)) (mt_trail (ms_core Mback))
          (mt_qhead (ms_core Mback))).
      { unfold Mback. simpl.
        eapply heap_covers_cancel_project__canceluntil_cap; eauto.
        rewrite <- Hsize_cur in Hheap. exact Hheap. }
      assert (Hreasonless_back : current_reasonless_earliest n Mback).
      { unfold Mback.
        eapply current_reasonless_cancel_project__search;
          eauto. }
      assert (Hinv_back : msolver_inv n F A_arr A_inst Mback).
      { constructor; assumption. }
      assert (Hrecord : record_ready_cert n F Mback words).
      { unfold Mback.
        eapply record_ready_cert_cancel_project__search
          with (A_inst := A_inst) (focus := focus).
        - exact Hweak_cur.
        - exact H_analysis_cancel_ready.
        - exact H_analyze_clause_cert.
        - repeat split; assumption.
        - reflexivity. }
      assert (Hqtail : mt_qhead (ms_core Mback) = ms_qtail Mback).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. reflexivity. }
      assert (Hpending_back :
          ms_capacity_root_propagation_pending Mback = 0).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. exact Hpending. }
      assert (Hseed_back : msolver_seed_shadow Mback).
      { unfold Mback, msolver_seed_shadow, msolver_cancel_project,
          msolver_core_heap_update in *; simpl in *; exact H_msolver_seed_shadow. }
      assert (Hmodel_back : ms_model Mback = ms_model Mcur).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. rewrite H_ms_model, H_ms_model_2. reflexivity. }
      assert (Hdecay_back :
          msat_fp32_positive_finite (ms_cla_decay Mback)).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. exact H_msat_fp32_positive_finite. }
      assert (Hdecay_eq : ms_cla_decay Mback = ms_cla_decay Mcur).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. unfold msat_fp32_same in H_msat_fp32_same. exact H_msat_fp32_same. }
      assert (Hpositive : record_watch1_positive Mback words).
      { unfold Mback. apply record_watch1_positive_cancel__record.
        apply (learned_tail_positive_watch1__record n Manalyzed words Htrail).
        exact (proj2 (proj2 H_analyze_clause_cert)). }
      lazymatch goal with
      | Hreuse : solver_search_reuse ?entry Manalyzed |- _ =>
          assert (Hreuse_back : solver_search_reuse entry Mback)
            by (intro Hbase; unfold Mback;
                exact (minisat_base_completion_cancel__api_reentry
                  n Manalyzed blevel orderpos order
                  (ms_root_level Manalyzed) Htrail (msw_db_wf Hweak_cur)
                  Hlevel Hbound (Hreuse Hbase)))
      end.
      assert (Hbackjump :
          solver_search_backjump_ready n F A_arr A_inst Mcur Mback words).
      { unfold solver_search_backjump_ready, record_clause_cert.
        exact (conj Hinv_back (conj Hrecord (conj Hpositive
          (conj Hqtail (conj Hpending_back (conj Hseed_back
            (conj Hmodel_back (conj Hdecay_back Hdecay_eq)))))))). }
      msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_21 : solver_search_which_implies_wit_21.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists propagation_result.
pose proof (solver_propagation_drained_strong n F A_arr A_inst propagation_result PreH6 PreH10) as Hinv.
assert (Hpending : ms_capacity_root_propagation_pending propagation_result = 0) by (exact (proj1 PreH6)).
destruct PreH7 as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
assert (Hreuse : solver_search_reuse M0 propagation_result).
{ intro Hbase. apply (proj1 PreH8). apply PreH3. exact Hbase. }
assert (Hmodel_nil : ms_model propagation_result = nil) by (rewrite Hmodel; assumption).
assert (Hdecay_positive : msat_fp32_positive_finite (ms_cla_decay propagation_result)) by (rewrite Hdecay; assumption).
subst confl. msat_manual_entailer_with ltac:(lia || tauto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_25 : solver_search_which_implies_wit_25.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mprogress ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mprogress) = ms_qtail Mprogress ) as H_mt_qhead.
  assert (Hshape : solver_shape Mprogress).
  { exact (msi_shape H_msolver_inv). }
  pose proof (msi_size H_msolver_inv) as Hsize.
  assert (Htrail :
      mtrail_wf (ms_size Mprogress) (ms_core Mprogress)).
  { rewrite <- Hsize. exact (msi_trail_wf H_msolver_inv). }
  assert (Hheap :
      heap_wf (ms_size Mprogress) (msolver_heap Mprogress)).
  { rewrite <- Hsize. exact (msi_heap_wf H_msolver_inv). }
  assert (Hrange :
      0 <= ms_root_level Mprogress <=
        Zlength (mt_lim (ms_core Mprogress))).
  { exact (msi_root_range H_msolver_inv). }
  assert (Htrail_len :
      Zlength (mt_trail (ms_core Mprogress)) = ms_qtail Mprogress).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hcancel :
      cancel_bound_ready Mprogress (ms_root_level Mprogress)).
  { unfold cancel_bound_ready.
    destruct (Z_lt_le_dec (ms_root_level Mprogress)
      (Zlength (mt_lim (ms_core Mprogress)))) as [Hlt | Hge].
    - right.
      pose proof (lim_lt_trail (ms_size Mprogress)
        (ms_core Mprogress) (ms_root_level Mprogress) Htrail
        (conj (proj1 Hrange) Hlt)) as Hlim.
      rewrite Htrail_len in Hlim.
      rewrite <- H_mt_qhead in Hlim.
      lia.
    - left. exact Hge. }
  unfold solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_cancel_pre, solver_cancel_owned,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
    solver_scalars_without_root_rep,
    solver_vecs_rep, solver_vecs_without_lim_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(first [assumption | lia]).
Qed.


Lemma proof_of_solver_search_which_implies_wit_26 : solver_search_which_implies_wit_26.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mprogress ) as H_msolver_inv.
  unfold solver_cancel_post.
  Split.
  - Intros.
    Exists Mprogress.
    split_pure_spatial.
    + apply solver_cancel_join_rep_levels_at.
    + pose proof (msw_root_range (msi_weak H_msolver_inv)) as Hr.
      assert (Hroot : solver_at_root Mprogress).
      { unfold solver_at_root. lia. }
      (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - Intros orderpos order.
    destruct H as (Hlevel & Hheap & Hincl & Hre).
    set (Mrestart := msolver_cancel_project Mprogress
      (ms_root_level Mprogress) orderpos order
      (ms_root_level Mprogress)).
    assert (Hweak : msolver_inv_weak n F A_arr A_inst Mrestart).
    { unfold Mrestart. apply msolver_inv_weak_cancel__search
        with (M := Mprogress) (level := ms_root_level Mprogress)
             (orderpos := orderpos) (order := order).
      - exact (msi_weak H_msolver_inv).
      - exact Hlevel.
      - reflexivity.
      - exact Hheap.
      - exact Hincl.
      - exact Hre. }
    Exists Mrestart.
    split_pure_spatial.
    + unfold Mrestart. apply solver_cancel_project_join_rep_levels_at.
    + pose proof (msi_trail_wf H_msolver_inv) as Htrail.
      assert (Hbound : Znth (ms_root_level Mprogress)
          (mt_lim (ms_core Mprogress)) 0 <= mt_qhead (ms_core Mprogress)).
      { apply Forall_Znth_elim; [exact (msi_prop_level H_msolver_inv)|lia]. }
      lazymatch goal with
      | Hreuse : solver_search_reuse ?entry Mprogress |- _ =>
          assert (Hreuse_restart : solver_search_reuse entry Mrestart)
            by (intro Hbase; unfold Mrestart;
                exact (minisat_base_completion_cancel__api_reentry
                  n Mprogress (ms_root_level Mprogress) orderpos order
                  (ms_root_level Mprogress) Htrail
                  (msw_db_wf (msi_weak H_msolver_inv)) Hlevel Hbound
                  (Hreuse Hbase)))
      end.
      assert (Hprop : prop_level (ms_core Mrestart)).
      { unfold Mrestart. apply (prop_level_cancel n (ms_core Mprogress)
          (ms_root_level Mprogress)).
        - exact Htrail.
        - exact Hlevel. }
      assert (Hwatch : minisat_watch_frontier n (msolver_db Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply minisat_watch_frontier_cancel__search
          with (M := Mprogress) (level := ms_root_level Mprogress)
               (orderpos := orderpos) (order := order)
               (root := ms_root_level Mprogress).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_watch_frontier H_msolver_inv). }
      assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
      { rewrite (msi_size H_msolver_inv). exact Hheap. }
      assert (Hheapcov : heap_covers n (msolver_heap Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply heap_covers_cancel_project__canceluntil_cap
          with (M := Mprogress) (level := ms_root_level Mprogress)
               (orderpos := orderpos) (order := order).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_heap_wf H_msolver_inv).
        - exact Hheap_n.
        - exact Hincl.
        - exact (msi_heap_covers H_msolver_inv).
        - exact Hre. }
      assert (Hreasonless : current_reasonless_earliest n Mrestart).
      { unfold current_reasonless_earliest.
        intros d Hd v Hlev Hword.
        unfold Mrestart, msolver_cancel_project, msolver_core_heap_update in Hd.
        simpl in Hd. rewrite Zlength_ztake in Hd by lia. lia. }
      assert (Hinv : msolver_inv n F A_arr A_inst Mrestart).
      { refine {| msi_weak := Hweak; msi_prop_level := Hprop;
                 msi_watch_frontier := Hwatch; msi_heap_covers := Hheapcov;
                 msi_reasonless_current := Hreasonless |}. }
      assert (HrootM : solver_at_root Mrestart).
      { unfold solver_at_root, Mrestart, msolver_cancel_project,
          msolver_core_heap_update. simpl. rewrite Zlength_ztake by lia.
        lia. }
      assert (Hqtail : mt_qhead (ms_core Mrestart) = ms_qtail Mrestart).
      { unfold Mrestart, msolver_cancel_project, msolver_core_heap_update.
        reflexivity. }
      msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_30 : solver_search_which_implies_wit_30.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_reducedb_pre_at, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_reducedb_frame_at,
    solver_search_bundle_at, solver_search_payload, solver_payload_cells, solver_scalars_rep,
    solver_scalars_without_qtail_rep,
    solver_fp_rep, solver_vecs_without_learnts_rep,
    solver_var_arrays_rep, solver_trail_array_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold solver_vecs_rep, solver_levels_slice_at.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_31_split_goal_1 : solver_search_which_implies_wit_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mdb ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mdb) = ms_qtail Mdb ) as H_mt_qhead.
  unfold order_select_pre.
  Intros.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  unfold solver_shape in Hshape.
  destruct Hshape as
    (Hsize & Hcap & Htwice & Hassign & Hlevels & Hreasons & Hopos & Hactivity &
     Htags & Htrail & Hqhead & Hpending & Hflag & Hflag_pending & Hqtail &
     Hwm & Hbinary_lits & Hstats & Hroot & Hbinary & Heven).
  pose proof (msi_size H_msolver_inv) as Hn.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - lia.
  - unfold order_heap_wf.
    rewrite <- Hn.
    exact (msi_heap_wf H_msolver_inv).
  - rewrite <- Hn.
    exact (msi_heap_covers H_msolver_inv).
  - rewrite <- Hn.
    apply mtrail_wf_assigned_below_qhead.
    + exact (msi_trail_wf H_msolver_inv).
    + transitivity (ms_qtail Mdb).
      * exact H_mt_qhead.
      * symmetry; exact Htrail.
  - exact Hassign.
  - exact (mtw_cells (msi_trail_wf H_msolver_inv)).
Qed.


Lemma proof_of_solver_search_which_implies_wit_31 : solver_search_which_implies_wit_31.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_search_which_implies_wit_31_split_goal_1 A_inst A_arr F n Mdb PreH1 PreH2).
Qed.


Lemma proof_of_solver_search_which_implies_wit_34_split_goal_1 : solver_search_which_implies_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_search_select_transition n F A_arr A_inst Mdb next orderpos_after order_after seed_after
    stats_after Mselected ) as H_solver_search_select_transition.
  unfold solver_search_select_transition in H_solver_search_select_transition.
  destruct H_solver_search_select_transition as (_ & _ & _ & _ & _ & [[Hret Hready] | Hselected]).
  - exact Hready.
  - unfold solver_search_selection_state in Hselected. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_34 : solver_search_which_implies_wit_34.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_search_which_implies_wit_34_split_goal_1 A_inst A_arr F n Mdb Mselected orderpos_after order_after stats_after seed_after next PreH1 PreH2).
Qed.


Lemma proof_of_solver_setnvars_entail_wit_4 : solver_setnvars_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  snv_shape.
  match goal with
  | HS : ms_size ?M = ?v, HO : order_update_post _ ?v _ _ _ _ |- _ =>
      rewrite <- HS in HO
  end.
  (* the eight array addresses are existential on
     the RHS, and the bundle has to be dissolved before [snv_sift_proj]
     so its rewrites reach the projections inside the bundle body. *)
  Exists wlc_2 actc_2 asgc_2 oposc_2 rsnc_2 lvlc_2 trlc_2 tgsc_2
         (msolver_heap_project
            (msolver_add_var Mcur_2 (Z_to_fp64 0))
            orderpos1 heap1).
  unfold setnvars_arrays_at.
  snv_sift_proj.
  rewrite setnvars_frame_at_add_var_sift.
  match goal with
  | HI : solver_support_inv (ms_size ?M) _ _ _ ?root ?M,
    HO : order_update_post _ _ _ _ ?o1 ?op |- _ =>
      let Hs := fresh "Hsift" in
      let Hshape := fresh "Hshape" in
      assert (Hshape : solver_shape M) by (unfold solver_shape; tauto);
      pose proof (solver_support_inv_add_var_sift__api_reentry
        _ _ _ _ root M (Z_to_fp64 0) o1 op
        HI ltac:(lia) ltac:(lia) HO) as Hs;
      pose proof (setnvars_shape_from_support_view__api_reentry M _ root
        Hshape (setnvars_core_equiv_add_var_sift M
          (Z_to_fp64 0) op o1) (msi_shape Hs));
      match goal with HS : ms_size M = _ |- _ => rewrite HS in Hs end
  end.
  match goal with
  | H : setnvars_core_equiv ?A ?B |- _ =>
      pose proof (setnvars_core_equiv_trans A B _ H
        (setnvars_core_equiv_add_var_sift B (Z_to_fp64 0)
           orderpos1 heap1))
  end.
  assert (Hcompletion : minisat_watch_completed sn_M_setnvars_spec ->
    minisat_watch_completed (msolver_heap_project
      (msolver_add_var Mcur_2 (Z_to_fp64 0))
      orderpos1 heap1)).
  { intro Hentry. apply minisat_watch_completed_heap_project__api_reentry.
    match goal with
    | HI : solver_support_inv ?n _ _ _ _ Mcur_2,
      HC : minisat_watch_completed sn_M_setnvars_spec ->
           minisat_watch_completed Mcur_2 |- _ =>
        exact (minisat_watch_completed_add_var__api_reentry
          n Mcur_2 (Z_to_fp64 0)
          (msi_trail_wf HI) (msw_db_wf (msi_weak HI)) (HC Hentry))
    end. }
  pose proof (setnvars_bound_step (ms_size sn_M_setnvars_spec) var n_pre
                ltac:(lia)).
  pose proof (wlists_rep_add_var wlc_2 var (ms_wm Mcur_2) ltac:(lia)) as Hcells.
  rewrite !Vecp.slot_eq in Hcells.
  sep_apply Hcells.
  match goal with HS : ms_size ?M = ?v |- _ => rewrite HS end.
  replace (2 * (var + 1)) with (2 * var + 2) by lia.
  split_pure_spatial.
  - cancel.
    unfold solver_char_tail, solver_int_tail, solver_ptr_tail, solver_array_tail.
    Exists physical physical_2 physical_3 physical_4 physical_5.
    msat_manual_entailer_with ltac:(lia || vec_buf_solve).
  - msat_manual_entailer_with ltac:(snv_dispatch).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_6_pure : solver_setnvars_partial_solve_wit_6_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_10_pure : solver_setnvars_partial_solve_wit_10_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_simplify_partial_solve_wit_21_pure : solver_simplify_partial_solve_wit_21_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Forall (lit_wf_c (ms_size Mcur)) (co_lits co) ) as H_Forall.
  rewrite Forall_forall in H_Forall.
  assert (Hlit : lit_wf_c (ms_size Mcur) (Znth (0 - 0) (co_lits co) 0)).
  { apply H_Forall. apply Znth_In. lia. }
  unfold lit_wf_c in Hlit. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_10 : solver_simplify_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j <= i ) as H_j_2.
  bind_fact ( i < Zlength words ) as H_i.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  replace (i - 0) with i in * by lia.
  replace (0 - 0) with 0 in * by lia.
  destruct
    (solver_simplify_compaction_lookup__simplify
      type Mcur words i j H_j H_j_2 H_i H_solver_simplify_db_compaction_inv)
    as [co [Htype Hin_selected]].
  pose proof (msas_weak H_msolver_inv) as Hweak.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof (msa_size Hweak) as Hsize.
  pose proof (msa_trail_wf Hweak) as Htrail.
  pose proof (mtw_cells Htrail) as Hcells.
  assert (Hin_db :
    In (Znth i words 0, co) (msolver_db Mcur)).
  { eapply solver_selected_db_in;
      [exact Htype | exact Hin_selected]. }
  assert (Hobj : obj_wf smp_n_solver_simplify_spec co).
  { eapply db_wf_obj; [exact (msa_db_wf Hweak) | exact Hin_db]. }
  destruct Hobj as [Hlen [Hlits Hnodup]].
  assert (Hlits_size : Forall (lit_wf_c (ms_size Mcur)) (co_lits co)).
  { rewrite <- Hsize. exact Hlits. }
  assert (Hhead :
    0 <= lit_var_c (Znth 0 (co_lits co) 0) < ms_size Mcur).
  { assert (Hwf : lit_wf_c (ms_size Mcur)
        (Znth 0 (co_lits co) 0)).
    { apply Forall_Znth_elim; [exact Hlits_size | lia]. }
    apply lit_var_c_in_range. exact Hwf. }
  sep_apply
    (solver_selected_clause_focus__simplify
      type Mcur (Znth i words 0) co Htype Hin_selected).
  Exists co j.
  unfold solver_simplify_db_rest_at, MiniSatClause.rep.
  unfold solver_shape in Hshape.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_entail_wit_1_split_goal_1 : solver_solve_entail_wit_1_split_goal_1.
Proof.
(LLM_pre_process ltac:(lia || int_auto));
unfold solver_assumptions_entry_ready in PreH4;
pose proof (solver_update_watch_ready_base_completed__api_reentry _ _ _ PreH1 PreH3) as Hbase; unfold msolver_resume_pending in Hbase; rewrite PreH2 in Hbase; cbn in Hbase; assert (Hreuse : solver_query_reuse M_solver_solve_spec M_solver_solve_spec) by (intro Hguard; exact Hbase).

all: intuition lia.
Qed.


Lemma proof_of_solver_solve_entail_wit_1_split_goal_2 : solver_solve_entail_wit_1_split_goal_2.
Proof.
(LLM_pre_process ltac:(lia || int_auto));
unfold solver_assumptions_entry_ready in PreH4;
pose proof (solver_update_watch_ready_base_completed__api_reentry _ _ _ PreH1 PreH3) as Hbase; unfold msolver_resume_pending in Hbase; rewrite PreH2 in Hbase; cbn in Hbase; assert (Hreuse : solver_query_reuse M_solver_solve_spec M_solver_solve_spec) by (intro Hguard; exact Hbase).

all: intuition lia.
Qed.


Lemma proof_of_solver_solve_entail_wit_1 : solver_solve_entail_wit_1.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_solve_entail_wit_1_split_goal_1 M_solver_solve_spec A_arr_solver_solve_spec F_solver_solve_spec n_solver_solve_spec PreH1 PreH2 PreH3 PreH4 PreH5).
- Goal_apply (proof_of_solver_solve_entail_wit_1_split_goal_2 M_solver_solve_spec A_arr_solver_solve_spec F_solver_solve_spec n_solver_solve_spec PreH1 PreH2 PreH3 PreH4 PreH5).
Qed.


Lemma proof_of_solver_solve_entail_wit_5_4_split_goal_1 : solver_solve_entail_wit_5_4_split_goal_1.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_4 : solver_solve_entail_wit_5_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!.
  rewrite <- PreH20.
  cancel.
  assert (Hstatus :
    signed_last_nbits
      (Znth (retval_2 - 0) (mt_assigns (ms_core Mcur)) 0) 8 =
    (1 - 2 * lit_sign_c (Znth k raw 0)) *
      Znth (lit_var_c (Znth k raw 0))
        (mt_assigns (ms_core Mcur)) 0).
  { msat_solve_selector_join k raw Mcur n_solver_solve_spec retval_2. }
  rewrite Hstatus.
  cancel.
Qed.


Lemma proof_of_enqueue_which_implies_wit_2_split_goal_spatial : enqueue_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  sep_apply_l_atomic
    (CharArray.seg_split_to_missing_i asg 0 (lit_var_c l0) n assigns 0).
  - dump_pre_spatial. exact Hrange.
  - replace (lit_var_c l0 - 0) with (lit_var_c l0) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_enqueue_which_implies_wit_2_split_goal_1 : enqueue_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  dump_pre_spatial; lia.
Qed.


Lemma proof_of_enqueue_which_implies_wit_2_split_goal_2 : enqueue_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n)
    by (apply lit_var_c_in_range; exact Hlit).
  dump_pre_spatial; lia.
Qed.


Lemma proof_of_enqueue_which_implies_wit_2 : enqueue_which_implies_wit_2.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_enqueue_which_implies_wit_2_split_goal_spatial trail reasons0 levels0 assigns l0 qtail n asg PreH1).
- Goal_apply (proof_of_enqueue_which_implies_wit_2_split_goal_1 trail reasons0 levels0 assigns l0 qtail n asg PreH1).
- Goal_apply (proof_of_enqueue_which_implies_wit_2_split_goal_2 trail reasons0 levels0 assigns l0 qtail n asg PreH1).
Qed.


Lemma proof_of_solver_addclause_entail_wit_3 : solver_addclause_entail_wit_3.
Proof.
  (* Inner-loop SHIFT step (`*j = *(j-1); j--').  The hole moves one slot left,
     so the split point of [pre ++ suf] moves -- but the CONCATENATION is the
     same list, which is why both sort invariants carry over with no new
     sortedness reasoning.  The element shifted right is [last pre 0], and the
     loop-continue test [*(j-1) > l] is exactly what puts it above l. *)
  LLM_pre_process ltac:(lia || int_auto).
  try ac_selfrepl.
  match goal with H : addclause_sort_outer_inv _ _ _ _ _ |- _ =>
    pose proof (conj I H) as Hout end.
  match goal with H : addclause_sort_inner_inv _ _ _ _ |- _ =>
    pose proof (conj I H) as Hin end.
  ac_shape; ac_sign.
  destruct Hout as [_ Hout]; destruct Hin as [_ Hin].
  assert (Hne : pre_2 <> nil)
    by (intro Hn; rewrite Hn in *; rewrite Zlength_nil in *; lia).
  replace (p_2 - 1) with (p_2 + -1) in * by lia.
  replace (p_2 + -1 - 0) with (p_2 + -1) in * by lia.
  match goal with Harr : arr_2 = _ |- _ =>
    assert (Ha : Znth (p_2 + -1) arr_2 0 = last pre_2 0)
      by (rewrite Harr;
          replace (p_2 + -1) with (Zlength pre_2 - 1) by lia;
          apply Znth_pred_app_last; exact Hne) end.
  rewrite Ha in *.
  subst arr_2.
  Exists (removelast pre_2 ++ last pre_2 0 :: (last pre_2 0 :: suf_2) ++ rest2_2)
    (last pre_2 0) rest2_2 (last pre_2 0 :: suf_2) (removelast pre_2) (Zlength (removelast pre_2)).
  try (rewrite replace_Znth_twice).
  replace p_2 with (Zlength pre_2) by lia.
  rewrite (replace_Znth_hole pre_2 junk_2 (suf_2 ++ rest2_2) (last pre_2 0)).
  rewrite <- app_comm_cons.
  rewrite (removelast_app_last pre_2 (last pre_2 0 :: suf_2 ++ rest2_2) Hne).
  sep_apply IntArray.full_to_seg.
  rewrite (removelast_app_last pre_2 suf_2 Hne), (Zlength_removelast pre_2 Hne).
  assert (Hin2 : addclause_sort_inner_inv l (pre_2 ++ suf_2) (removelast pre_2) (last pre_2 0 :: suf_2)).
  { unfold addclause_sort_inner_inv; repeat split;
      [ symmetry; exact (removelast_app_last pre_2 suf_2 Hne)
      | assumption
      | constructor; [ lia | assumption ] ]. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [auto | ac_close].
Qed.


Lemma proof_of_solver_addclause_entail_wit_7_3 : solver_addclause_entail_wit_7_3.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
  msat_addclause_dedup_skip sortedf ac_input_addclause_spec tail_2 kept_2 q_2 k_2 endvar_pre.
Qed.


Lemma proof_of_solver_addclause_return_wit_2 : solver_addclause_return_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Left.
apply _derivable1_andp_intros.
{

  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
rewrite ?Z.sub_0_r in *.
rewrite ?sizeof_int in *.
destruct Hded as (HdIn & HdSS & HdNA & HdPos & HdWF & HdUn & HdLe & HdLast & HdLst).
assert (Hq1 : q = 1).
{ match goal with
  | Hj : j = begin_pre + q * 4, Hd : (j - begin_pre) ÷ 4 = 1 |- _ =>
      rewrite Hj in Hd;
      replace (begin_pre + q * 4 - begin_pre) with (q * 4) in Hd by lia;
      rewrite quot_mul_four in Hd; exact Hd
  end. }
assert (Hk1 : Zlength kept = 1)
  by (match goal with H : Zlength kept = q |- _ => rewrite H; exact Hq1 end).
assert (Hk : 1 <= Zlength kept) by lia.
assert (Hhd : Znth 0 (kept ++ tail) 0 = Znth 0 kept 0).
{ destruct kept as [|a r]; [ rewrite Zlength_nil in Hk; lia | reflexivity ]. }
assert (Hfresh : Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                      (mt_assigns (ms_core Mnew)) 0 = 0).
{ rewrite Hhd. rewrite Forall_forall in HdUn. apply HdUn.
  apply ac_Znth_In. ac_lia. }
assert (Hlwf : lit_wf_c (ms_size Mnew) (Znth 0 (kept ++ tail) 0)).
{ rewrite Hhd. rewrite Forall_forall in HdWF. apply HdWF.
  apply ac_Znth_In. ac_lia. }
assert (Hkeq : lits_denote kept = lit_denote (Znth 0 (kept ++ tail) 0) :: nil).
{ rewrite Hhd. pose proof (singleton_of_Zlength_one kept Hk1) as Hs.
  unfold lits_denote. rewrite Hs at 1. reflexivity. }
match goal with H : solver_support_inv _ _ _ _ 0 Mnew |- _ =>
  assert (HshapeM : solver_shape Mnew) by assumption end.
match goal with H : enqueue_input _ _ _ _ _ _ _ |- _ =>
  pose proof H as Hein end.
unfold enqueue_input in Hein.
assert (Hroom : ms_qtail Mnew < ms_cap Mnew).
{ unfold solver_shape in HshapeM. decompose [and] HshapeM.
  decompose [and] Hein.
  match goal with Himp : (Znth _ _ 0 = 0 -> _) |- _ =>
    specialize (Himp Hfresh) end.
  lia. }
assert (HshapeE : solver_shape
   (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)).
{ apply solver_shape_enqueue_fresh__record;
    [ exact HshapeM | exact Hroom | assumption ]. }
unfold enqueue_post_at.
Intros qtail' assigns' levels' reasons' trail'.
match goal with H : enqueue_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rename H into Htr end.
pose proof Htr as Htr0.
unfold enqueue_transition in Htr.
destruct Htr as [Hsame | [Hconf | Hnew]].
{ destruct Hsame as [Hs _]. rewrite Hfresh in Hs.
  pose proof (lit_sig_nonzero (Znth 0 (kept ++ tail) 0)). lia. }
{ destruct Hconf as [Hne _]. contradiction. }
destruct Hnew as [Hz [Hret [Ha' [Hl' [Hr' [Ht' Hq']]]]]].
subst qtail' assigns' levels' reasons' trail' retval.
msat_manual_entailer_with ltac:(reflexivity || lia). }
{

  (LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign; ac_spatial.
rewrite ?Z.sub_0_r in *.
rewrite ?sizeof_int in *.
destruct Hded as (HdIn & HdSS & HdNA & HdPos & HdWF & HdUn & HdLe & HdLast & HdLst).
assert (Hq1 : q = 1).
{ match goal with
  | Hj : j = begin_pre + q * 4, Hd : (j - begin_pre) ÷ 4 = 1 |- _ =>
      rewrite Hj in Hd;
      replace (begin_pre + q * 4 - begin_pre) with (q * 4) in Hd by lia;
      rewrite quot_mul_four in Hd; exact Hd
  end. }
assert (Hk1 : Zlength kept = 1)
  by (match goal with H : Zlength kept = q |- _ => rewrite H; exact Hq1 end).
assert (Hk : 1 <= Zlength kept) by lia.
assert (Hhd : Znth 0 (kept ++ tail) 0 = Znth 0 kept 0).
{ destruct kept as [|a r]; [ rewrite Zlength_nil in Hk; lia | reflexivity ]. }
assert (Hfresh : Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                      (mt_assigns (ms_core Mnew)) 0 = 0).
{ rewrite Hhd. rewrite Forall_forall in HdUn. apply HdUn.
  apply ac_Znth_In. ac_lia. }
assert (Hlwf : lit_wf_c (ms_size Mnew) (Znth 0 (kept ++ tail) 0)).
{ rewrite Hhd. rewrite Forall_forall in HdWF. apply HdWF.
  apply ac_Znth_In. ac_lia. }
assert (Hkeq : lits_denote kept = lit_denote (Znth 0 (kept ++ tail) 0) :: nil).
{ rewrite Hhd. pose proof (singleton_of_Zlength_one kept Hk1) as Hs.
  unfold lits_denote. rewrite Hs at 1. reflexivity. }
match goal with H : solver_support_inv _ _ _ _ 0 Mnew |- _ =>
  assert (HshapeM : solver_shape Mnew) by assumption end.
match goal with H : enqueue_input _ _ _ _ _ _ _ |- _ =>
  pose proof H as Hein end.
unfold enqueue_input in Hein.
assert (Hroom : ms_qtail Mnew < ms_cap Mnew).
{ unfold solver_shape in HshapeM. decompose [and] HshapeM.
  decompose [and] Hein.
  match goal with Himp : (Znth _ _ 0 = 0 -> _) |- _ =>
    specialize (Himp Hfresh) end.
  lia. }
assert (HshapeE : solver_shape
   (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)).
{ apply solver_shape_enqueue_fresh__record;
    [ exact HshapeM | exact Hroom | assumption ]. }
unfold enqueue_post_at.
Intros qtail' assigns' levels' reasons' trail'.
match goal with H : enqueue_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rename H into Htr end.
pose proof Htr as Htr0.
unfold enqueue_transition in Htr.
destruct Htr as [Hsame | [Hconf | Hnew]].
{ destruct Hsame as [Hs _]. rewrite Hfresh in Hs.
  pose proof (lit_sig_nonzero (Znth 0 (kept ++ tail) 0)). lia. }
{ destruct Hconf as [Hne _]. contradiction. }
destruct Hnew as [Hz [Hret [Ha' [Hl' [Hr' [Ht' Hq']]]]]].
subst qtail' assigns' levels' reasons' trail' retval.
assert (Hsz : ms_size (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
              = ms_size Mnew) by reflexivity.
assert (Hcp : ms_cap (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
              = ms_cap Mnew) by reflexivity.
assert (Htrans : addclause_support_transition ac_n_addclause_spec ac_F_addclause_spec
    ac_A_arr_addclause_spec ac_A_inst_addclause_spec ac_M_addclause_spec
    ac_input_addclause_spec 1
    (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
    (kept ++ tail) (ac_F_addclause_spec ++ (lits_denote kept :: nil))).
{ ac_support_transition.
  change (ms_size (msolver_set_root
    (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None) 0) =
    ms_size Mnew) in Hsz.
  change (ms_cap (msolver_set_root
    (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None) 0) =
    ms_cap Mnew) in Hcp.
  split; [ assumption | ].
  split; [ change (ms_size ac_M_addclause_spec <= ms_size Mnew); assumption | ].
  split; [ change (ms_cap ac_M_addclause_spec <= ms_cap Mnew); assumption | ].
  split; [ change (2 * ms_cap Mnew <= INT_MAX); assumption | ].
  split; [ intros _; split; [ assumption | split; assumption ] | ].
  right.
  split; [ reflexivity | ].
  split.
  - rewrite Hkeq.
    apply solver_support_inv_addclause_unit__api_reentry;
      [ assumption | exact Hlwf | exact Hfresh | assumption | exact Hroom
      | assumption ].
  - apply addclause_install_equiv. assumption. }
unfold addclause_support_post_at.
Exists (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None)
       (kept ++ tail) (ac_F_addclause_spec ++ (lits_denote kept :: nil)).
split_pure_spatial; [ | dump_pre_spatial; exact Htrans ].
eassert (Href : _ |-- enqueue_post_at s_pre asg lvlp
    (Znth 0 (kept ++ tail) 0) 0 (ms_size Mnew) (ms_cap Mnew) (ms_qtail Mnew) 1
    (mt_assigns (ms_core Mnew)) (mt_levels (ms_core Mnew)) (ms_reason_words Mnew)
    (mt_trail (ms_core Mnew)) (mt_lim (ms_core Mnew))).
{ unfold enqueue_post_at.
  Exists (ms_qtail Mnew + 1)
    (replace_Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                  (lit_sig (Znth 0 (kept ++ tail) 0)) (mt_assigns (ms_core Mnew)))
    (replace_Znth (lit_var_c (Znth 0 (kept ++ tail) 0))
                  (Zlength (mt_lim (ms_core Mnew))) (mt_levels (ms_core Mnew)))
    (replace_Znth (lit_var_c (Znth 0 (kept ++ tail) 0)) 0 (ms_reason_words Mnew))
    (mt_trail (ms_core Mnew) ++ (Znth 0 (kept ++ tail) 0) :: nil).
  apply split_pure_and_spatial_goals;
    [ lazymatch goal with | |- ?A |-- ?B => unify A B end; cancel
    | dump_pre_spatial; exact Htr0 ]. }
sep_apply Href.
sep_apply (enqueue_post_record_refold_wl s_pre asg lvlp
  (Znth 0 (kept ++ tail) 0) 0 (ms_size Mnew) (ms_cap Mnew) (ms_qtail Mnew)
  (mt_assigns (ms_core Mnew)) (mt_levels (ms_core Mnew)) (ms_reason_words Mnew)
  (mt_trail (ms_core Mnew)) (mt_lim (ms_core Mnew)) Mnew None wlg
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  HshapeE Hfresh).
replace (ms_size Mnew) with (ms_size (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None))
  by (rewrite ?addclause_finish_size; congruence).
replace (ms_cap Mnew) with (ms_cap (msolver_enqueue_fresh Mnew (Znth 0 (kept ++ tail) 0) 0 None))
  by (rewrite ?addclause_finish_cap; congruence).
sep_apply solver_rep_growable_of_wl.
sep_apply (int_head_merge begin_pre (Zlength ac_input_addclause_spec)
             (kept ++ tail) ltac:(ac_lia) ltac:(ac_lia)).
msat_manual_entailer_with lia.
 }
Qed.
