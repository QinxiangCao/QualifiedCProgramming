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
Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_state_search_proof_manual_part6.

Lemma proof_of_solver_search_entail_wit_6_split_goal_6 : solver_search_entail_wit_6_split_goal_6.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_model_copy_entry H_model_ready n F A_arr A_inst Mselected.
Qed.


Lemma proof_of_solver_search_entail_wit_6 : solver_search_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_search_entail_wit_6_split_goal_1 M0 A_inst A_arr F n conflictC Mdb select_seed_shadow retval order_now orderpos_now seed_now seed_shadow_now Mselected orderpos_after order_after stats_after seed_after PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25).
  - Goal_apply (proof_of_solver_search_entail_wit_6_split_goal_2 M0 A_inst A_arr F n conflictC Mdb select_seed_shadow retval order_now orderpos_now seed_now seed_shadow_now Mselected orderpos_after order_after stats_after seed_after PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25).
  - Goal_apply (proof_of_solver_search_entail_wit_6_split_goal_3 M0 A_inst A_arr F n conflictC Mdb select_seed_shadow retval order_now orderpos_now seed_now seed_shadow_now Mselected orderpos_after order_after stats_after seed_after PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25).
  - Goal_apply (proof_of_solver_search_entail_wit_6_split_goal_4 M0 A_inst A_arr F n conflictC Mdb select_seed_shadow retval order_now orderpos_now seed_now seed_shadow_now Mselected orderpos_after order_after stats_after seed_after PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25).
  - Goal_apply (proof_of_solver_search_entail_wit_6_split_goal_5 M0 A_inst A_arr F n conflictC Mdb select_seed_shadow retval order_now orderpos_now seed_now seed_shadow_now Mselected orderpos_after order_after stats_after seed_after PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25).
  - Goal_apply (proof_of_solver_search_entail_wit_6_split_goal_6 M0 A_inst A_arr F n conflictC Mdb select_seed_shadow retval order_now orderpos_now seed_now seed_shadow_now Mselected orderpos_after order_after stats_after seed_after PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25).
Qed.


Lemma proof_of_solver_search_which_implies_wit_2 : solver_search_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | |- _ |-- solver_rep_levels_wl_at ?s ?M ?wl ?lvl =>
      sep_apply_r_atomic (solver_cancel_join_rep_levels_at s M lvl wl)
  end.
  unfold solver_levels_slice_at.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_33 : solver_search_which_implies_wit_33.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv n F A_arr A_inst Mdb ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mdb) = ms_qtail Mdb ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mdb = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( ms_model Mdb = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mdb) ) as H_msat_fp32_positive_finite.
  bind_fact ( order_select_post (ms_size Mdb) next (ms_order Mdb) order_now orderpos_now (mt_assigns (ms_core Mdb))
    (mt_trail (ms_core Mdb)) (mt_qhead (ms_core Mdb)) ) as H_order_select_post.
  bind_fact ( fp64_eq seed_now (Z_to_fp64 seed_shadow_now) ) as H_fp64_eq.
  assert (Hseedok : seed_ok seed_shadow_now).
  { unfold seed_ok. lia. }
  destruct (solver_search_select_transition_intro__search
    A_inst A_arr F n Mdb orderpos_now order_now seed_now seed_shadow_now next
    H_msolver_inv H_mt_qhead H_ms_capacity_root_propagation_pending H_ms_model H_msat_fp32_positive_finite
      H_order_select_post Hseedok H_fp64_eq)
    as [Mselected Htransition].
  assert (HM : Mselected = msolver_search_select Mdb orderpos_now order_now
      seed_now (search_decision_stats_update (ms_stats Mdb))).
  { unfold solver_search_select_transition in Htransition. tauto. }
  assert (Hcap_selected : ms_cap Mselected = ms_cap Mdb).
  { rewrite HM. reflexivity. }
  lazymatch goal with
  | Hreuse : solver_search_reuse ?entry Mdb |- _ =>
      assert (Hreuse_selected : solver_search_reuse entry Mselected)
        by (rewrite HM; exact Hreuse)
  end.
  assert (Hdecay_selected :
      msat_fp32_positive_finite (ms_cla_decay Mselected)).
  { unfold solver_search_select_transition in Htransition. tauto. }
  assert (Hshape_selected : solver_shape Mselected).
  { unfold solver_search_select_transition in Htransition.
    destruct Htransition as (_ & _ & _ & _ & _ & [Hready | Hselected]).
    - destruct Hready as [_ Hready].
      unfold solver_search_model_ready in Hready.
      exact (msi_shape (proj1 Hready)).
    - unfold solver_search_selection_state in Hselected.
      exact (msw_shape (proj1 Hselected)). }
  Exists orderpos_now order_now seed_now
    (search_decision_stats_update (ms_stats Mdb)) Mselected.
  split_pure_spatial.
  - sep_apply (solver_search_select_join_rep_levels_at__search
      Mdb Mselected activity_ptr assigns_select orderpos_ptr s levels search_wl
      seed_now orderpos_now order_now HM Hshape_selected).
    cancel.
  - split_pures; dump_pre_spatial;
      try exact Hreuse_selected; try exact Htransition;
      try exact Hdecay_selected; lia.
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_7_pure : solver_setnvars_partial_solve_wit_7_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_safety_wit_2 : solver_setnvars_safety_wit_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia).
Qed.


Lemma proof_of_solver_simplify_entail_wit_4_1 : solver_simplify_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_4. subst jcur.
  rename M_solver_simplify_spec into M.
  rename smp_wl_solver_simplify_spec into smp_wl.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  bind_fact ( i < Zlength words ) as H_i.
  bind_fact ( clause_simplify_result (co_lits co) (mt_assigns (ms_core Mcur)) 1 ) as H_clause_simplify_result.
  bind_fact ( Zlength (mt_lim (ms_core Mcur)) = 0 ) as H_Zlength.
  bind_fact ( mt_qhead (ms_core Mcur) = ms_qtail Mcur ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mcur = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow Mcur ) as H_msolver_seed_shadow.
  bind_fact ( db_lookup (solver_selected_db type Mcur) (Znth (i - 0) words 0) co ) as H_db_lookup.
  bind_fact (solver_simplify_reuse M Mcur) as Hreuse.
  pose proof H_solver_simplify_db_compaction_inv as Hcomp_seed.
  unfold solver_simplify_db_compaction_inv in Hcomp_seed.
  destruct Hcomp_seed as [Htype _].
  replace (i - 0) with i in * by lia.
  sep_apply (Vecp.rep_ptr_intro cs cls words cap _ _ _ eq_refl eq_refl eq_refl
    ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  unfold clause_remove_post.
  Intros wm' stats'.
  destruct H as [Hremove [Hstats [Hreasons Hunlocked]]].
  unfold clause_db_pair_remainder.
  Split.
  - Intros co1 pre post.
    destruct H as [Hprob [Hlits Hlearnt]].
    destruct Htype as [-> | ->].
    + destruct (msat_simplify13_delete_arm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (or_introl (conj eq_refl eq_refl)) H_msolver_inv Hprob H_db_lookup
        H_clause_simplify_result H_Zlength H_mt_qhead
        H_ms_capacity_root_propagation_pending H_msolver_seed_shadow
        H_solver_simplify_db_compaction_inv H_i Hremove Hstats Hunlocked)
        as [Heq [Hdbnext Hstep]].
      subst co1.
      assert (Hdbclose : clause_db_rep pre ** clause_db_rep post
          |-- clause_db_rep (pre ++ post)).
      { sep_apply_r_atomic (clause_db_rep_app_intro pre post).
        cancel. }
      assert (Hreuse_next : solver_simplify_reuse M
          (msolver_remove_clause Mcur false (Znth i words 0) wm' stats')).
      { unfold solver_simplify_reuse. intros Hentry.
        apply minisat_watch_completed_remove_clause__api_reentry.
        exact (Hreuse Hentry). }
      assert (Hcap_next : ms_cap
          (msolver_remove_clause Mcur false (Znth i words 0) wm' stats') = ms_cap M).
      { change (ms_cap Mcur = ms_cap M). assumption. }
      assert (Hroot_next : ms_root_level
          (msolver_remove_clause Mcur false (Znth i words 0) wm' stats') = ms_root_level M).
      { change (ms_root_level Mcur = ms_root_level M). assumption. }
      Exists words (msolver_remove_clause Mcur false (Znth i words 0) wm' stats').
      (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
      sep_apply Hdbclose.
      rewrite Hdbnext.
      rewrite (msat_simplify13_db_rest_after_remove s_pre 0 false Mcur
        (Znth i words 0) wm' stats' reasons levels_ptr_solver_simplify_spec
        smp_wl asg (or_introl (conj eq_refl eq_refl))).
      cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
      unfold solver_selected_learnt_db. cbn.
      (Intros; cancel).
    + unfold solver_selected_prob_db in Hprob. simpl in Hprob.
      destruct pre; discriminate Hprob.
  - Intros co1 pre post.
    destruct H as [Hlearnt_db [Hlits Hlearnt]].
    destruct Htype as [-> | ->].
    + unfold solver_selected_learnt_db in Hlearnt_db.
      simpl in Hlearnt_db. destruct pre; discriminate Hlearnt_db.
    + destruct (msat_simplify13_delete_arm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (or_intror (conj eq_refl eq_refl)) H_msolver_inv Hlearnt_db H_db_lookup
        H_clause_simplify_result H_Zlength H_mt_qhead
        H_ms_capacity_root_propagation_pending H_msolver_seed_shadow
        H_solver_simplify_db_compaction_inv H_i Hremove Hstats Hunlocked)
        as [Heq [Hdbnext Hstep]].
      subst co1.
      assert (Hdbclose : clause_db_rep pre ** clause_db_rep post
          |-- clause_db_rep (pre ++ post)).
      { sep_apply_r_atomic (clause_db_rep_app_intro pre post).
        cancel. }
      assert (Hreuse_next : solver_simplify_reuse M
          (msolver_remove_clause Mcur true (Znth i words 0) wm' stats')).
      { unfold solver_simplify_reuse. intros Hentry.
        apply minisat_watch_completed_remove_clause__api_reentry.
        exact (Hreuse Hentry). }
      assert (Hcap_next : ms_cap
          (msolver_remove_clause Mcur true (Znth i words 0) wm' stats') = ms_cap M).
      { change (ms_cap Mcur = ms_cap M). assumption. }
      assert (Hroot_next : ms_root_level
          (msolver_remove_clause Mcur true (Znth i words 0) wm' stats') = ms_root_level M).
      { change (ms_root_level Mcur = ms_root_level M). assumption. }
      Exists words (msolver_remove_clause Mcur true (Znth i words 0) wm' stats').
      (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
      sep_apply Hdbclose.
      rewrite Hdbnext.
      rewrite (msat_simplify13_db_rest_after_remove s_pre 1 true Mcur
        (Znth i words 0) wm' stats' reasons levels_ptr_solver_simplify_spec
        smp_wl asg (or_intror (conj eq_refl eq_refl))).
      cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
      unfold solver_selected_prob_db. cbn.
      msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_simplify_partial_solve_wit_35_pure : solver_simplify_partial_solve_wit_35_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [_ [Hj [Hji [Hi _]]]]. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_13 : solver_simplify_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_simplify_outer_loop.
  Intros Mdone.
  Exists Mdone.
  unfold msat_fp32_same.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_solve_entail_wit_3_2 : solver_solve_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hprefix0 : assumption_prefix raw_entry 0 = @nil literal).
  { unfold assumption_prefix.
    rewrite Zsublist_nil by lia.
    reflexivity. }
  Left.
  Exists raw_entry 0 Mready.
  rewrite Hprefix0.
  pose proof (Zlength_nonneg raw_entry).
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (first [assumption | lia | tauto])] ..]).
Qed.


Lemma proof_of_solver_solve_entail_wit_4_1 : solver_solve_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  msat_solve_lbool_cell_arm Mcur retval_2.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_24_pure : solver_solve_partial_solve_wit_24_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lit_sign_c_range (Znth k raw 0)).
  assert (Hsign : lit_sign_c (Znth k raw 0) = 0 \/ lit_sign_c (Znth k raw 0) = 1) by lia.
  destruct Hsign as [Hs | Hs]; rewrite Hs in *;
  (Intros; split_pures; dump_pre_spatial; solve [auto | (nia)]).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_8 : solver_solve_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  bind_fact ( assumption_fresh_ready n raw k Mcur ) as H_assumption_fresh_ready.
  bind_fact ( ms_capacity_root_propagation_pending Mcur = 0 ) as H_ms_capacity_root_propagation_pending.
  replace (k - 0) with k by lia.
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hweak.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof H_assumption_fresh_ready as Hready.
  unfold assumption_fresh_ready in Hready.
  destruct Hready as [Hsize [Hdrain [Hfresh [Hlevelroom Henq]]]].
  pose proof Henq as Henq'. unfold enqueue_input in Henq'.
  destruct Henq' as [Hlit [Htwice [Haslen [Hlvlen [Hrslen
    [Htrlen [Hqrange [Hroom Hcells]]]]]]]].
  assert (Hroomcap : ms_qtail Mcur < ms_cap Mcur).
  { specialize (Hroom Hfresh). unfold solver_shape in Hshape. lia. }
  pose proof (assume_post_refold_assigns_levels__solve
    solve_wl s values levels_ptr (Znth k raw 0)
    n (ms_cap Mcur) (ms_qtail Mcur)
    (mt_assigns (ms_core Mcur)) (mt_levels (ms_core Mcur))
    (ms_reason_words Mcur) (mt_trail (ms_core Mcur))
    (mt_lim (ms_core Mcur)) Mcur) as Hrefold.
  specialize (Hrefold
    (msa_size Hweak) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    Hshape Hroomcap H_ms_capacity_root_propagation_pending Hdrain Hfresh).
  sep_apply Hrefold.
  lazymatch goal with
  | Hentry : solver_query_reuse ?entry Mcur |- _ =>
      assert (Hreuse_assume : solver_query_reuse entry
          (msolver_assume Mcur (Znth k raw 0)))
        by (intro Hpublic;
            exact (minisat_base_watch_completed_assume__api_reentry
              n Mcur (Znth k raw 0)
              (msa_db_wf Hweak) (msa_trail_wf Hweak) Hlit Hfresh
              (Hentry Hpublic)))
  end.
  Exists (msolver_assume Mcur (Znth k raw 0)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. rewrite <- PreH1. reflexivity.
    + dump_pre_spatial. exact Hreuse_assume.
    + dump_pre_spatial. eapply assumption_fresh_transition_intro__solve; eauto.
Qed.


Lemma proof_of_solver_solve_which_implies_wit_14 : solver_solve_which_implies_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( i = begin + k * sizeof ( INT ) ) as H_i.
  bind_fact ( endvar = begin + Zlength raw * sizeof ( INT ) ) as H_endvar.
  assert (Hk : k = Zlength raw).
  { rewrite sizeof_int in H_i, H_endvar. lia. }
  subst k.
  sep_apply (store_ptr_undef_store_ptr &("i") i).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_assume_which_implies_wit_1 : assume_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold enqueue_state_at.
  Intros rsn trl.
  Exists trl rsn.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_7_split_goal_1 : solver_addclause_which_implies_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_addclause_shape_spatial_close.
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_7 : solver_addclause_which_implies_wit_7.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_addclause_which_implies_wit_7_split_goal_1 Mnew kept tail k PreH1 PreH2 PreH3).
Qed.


Lemma proof_of_solver_addclause_which_implies_wit_10 : solver_addclause_which_implies_wit_10.
Proof.
(* Hand the solver to clause_new with the level pointer still explicit, then
   split the buffer at the kept/tail boundary for its [begin, j) argument. *)
(LLM_pre_process ltac:(lia || int_auto)); ac_shape; ac_sign.
sep_apply solver_assigns_focus_close_levels_wl.
sep_apply (IntArray.seg_split_to_seg begin 0 (Zlength kept)
             (Zlength ac_input_addclause_spec) (kept ++ tail)).
(* seg_split_to_seg emits the bounds as [mid - lo] / [hi - lo]; normalise the
   [- 0] away FIRST or neither sublist identity finds its redex *)
rewrite !Z.sub_0_r.
rewrite sublist_app_exact1.
match goal with H : Zlength (kept ++ tail) = Zlength ac_input_addclause_spec |- _ =>
  rewrite <- H end.
rewrite sublist_app_exact2.
all: msat_manual_entailer_with ltac:(ac_close).
Qed.


Lemma proof_of_solver_canceluntil_entail_wit_1 : solver_canceluntil_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_cancel_open_at in *.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  assert (Hlevel : 0 <= level_pre < Zlength (mt_lim (ms_core M0))) by lia.
  pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level_pre
    H_mtrail_wf Hlevel) as Hbound.
  pose proof H_solver_shape as Hshape.
  unfold solver_shape in Hshape.
  assert (Hslice : sublist (ms_qtail M0 - 1 + 1) (ms_qtail M0)
    (mt_trail (ms_core M0)) = (@nil Z)).
  { replace (ms_qtail M0 - 1 + 1) with (ms_qtail M0) by lia.
    unfold sublist; apply skipn_all2; rewrite length_firstn; lia. }
  assert (Hinv : cancel_clear_loop_inv M0 level_pre (ms_qtail M0 - 1)
    (mt_assigns (ms_core M0)) (ms_reason_words M0)).
  { unfold cancel_clear_loop_inv.
    repeat split; try lia; rewrite Hslice; reflexivity. }
  Exists (mt_assigns (ms_core M0)) (ms_reason_words M0).
  split_pure_spatial.
  - cancel (solver_cancel_frame s_pre M0 wl).
    cancel.
    sep_apply (Veci.rep_intro &(s_pre # "solver_t" ->ₛ "trail_lim") p (mt_lim (ms_core M0)) cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption.
    replace (level_pre - 0) with level_pre by lia; reflexivity.
Qed.


Lemma proof_of_solver_new_which_implies_wit_1 : solver_new_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_storage_undef in *.
  msat_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_nvars_which_implies_wit_1 : solver_nvars_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_search_entail_wit_3_3_split_goal_1 : solver_search_entail_wit_3_3_split_goal_1.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_search_close_conflict_count_nonneg.
Qed.


Lemma proof_of_solver_search_entail_wit_3_3 : solver_search_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_solver_search_entail_wit_3_3_split_goal_1 M0 A_inst A_arr F n conflict_count_value Mcur learnt_words retval propagation_result result_focus result_clause Mconf p focus Cconf retval_2 Manalyze Manalyzed words backjump retval_3 Mback Mrecord cla_inc1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85 PreH86 PreH87 PreH88).
Qed.



Lemma proof_of_solver_search_entail_wit_5_2 : solver_search_entail_wit_5_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists Mclean.
unfold solver_search_reducedb_frame_at, solver_search_bundle_at, solver_search_payload, solver_rep_levels_wl_at.
unfold solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_scalars_rep, solver_scalars_without_qtail_rep, clause_new_scalars_frame,
  solver_vecs_rep, solver_vecs_without_learnts_rep.
Intros act asg opos rsn trl tgs.
Exists act asg opos rsn trl tgs.
msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_48_pure : solver_search_partial_solve_wit_48_pure.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact (solver_search_backjump_ready n F A_arr A_inst Mcur Mback words) as Hback.
pose proof Hback as Hframe. unfold solver_search_backjump_ready in Hframe.
destruct Hframe as [_ [_ [_ [_ [_ [_ [Hmodel [_ _]]]]]]]].
assert (Hmodel_nil : ms_model Mback = nil) by (rewrite Hmodel; assumption).
msat_manual_entailer_with ltac:(assumption || lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_85_pure : solver_search_partial_solve_wit_85_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (msi_shape PreH4) as Hshape.
  unfold solver_shape in Hshape.
  destruct Hshape as (_ & _ & _ & _ & _ & _ & _ & Hact & _).
  split_pures; dump_pre_spatial.
  - exact PreH6.
  - apply msat_fp64_eq_finite_refl.
    apply MSatFloatFacts.Z_to_fp64_i32_finite; lia.
  - exact PreH1.
  - exact PreH2.
  - exact Hact.
Qed.


Lemma proof_of_solver_search_which_implies_wit_5 : solver_search_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_search_root_frame_at, solver_search_init_frame_at,
    solver_search_bundle_at, solver_search_payload.
  Intros.
  sep_apply (join_scalars_root s M0).
  sep_apply (join_vecs_trail_lim s M0).
  sep_apply (peel_fp_decays s M0).
  sep_apply (peel_vecs_model s M0).
  unfold stats_rep, stats_without_starts_rep.
  Intros.
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hstarts_addr :
      &(s # "solver_t" ->ₛ "stats" .ₛ "starts") =
      &(stats_ptr # "stats_t" ->ₛ "starts"))
    by (unfold stats_ptr; csimpl; reflexivity).
  rewrite Hstarts_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_which_implies_wit_11 : solver_search_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_set_conflicts in *.
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationStable A_inst) Mconf focus ) as H_propagation_cancel_ready.
  bind_fact ( propagation_conflict_cert n F Mconf Cconf ) as H_propagation_conflict_cert.
  bind_fact ( conflict_ptr_denotes Mconf p Cconf ) as H_conflict_ptr_denotes.
  bind_fact ( msolver_seed_shadow Mconf ) as H_msolver_seed_shadow.
  bind_fact ( ms_model Mconf = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mconf) ) as H_msat_fp32_positive_finite.
  bind_fact ( msat_fp32_same (ms_cla_decay Mconf) (ms_cla_decay Mcur) ) as H_msat_fp32_same.
  pose proof H_propagation_cancel_ready as Hcancel0.
  destruct H_propagation_cancel_ready as
    [Hsw [Hlevel [Hfocus_wf [Hprocessed [Hfocus_level [Hfrontier
      [Hheap [Hcovers Hreasonless]]]]]]]].
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mconf)
    by exact (proj2 Hsw).
  set (Manalyze :=
    msolver_with_cla_inc_stats Mconf (ms_cla_inc Mconf)
      (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  assert (Hequiv : analysis_core_equiv Mconf Manalyze).
  { unfold Manalyze, msolver_with_cla_inc_stats, analysis_core_equiv.
    cbn. repeat split; reflexivity. }
  assert (Hshape_analyze : solver_shape Manalyze).
  { pose proof (msw_shape Hweak) as Hshape0.
    unfold Manalyze, msolver_with_cla_inc_stats, solver_shape.
    unfold solver_shape in Hshape0. cbn.
    rewrite Zlength_replace_Znth. tauto. }
  assert (Hweak_analyze : msolver_inv_weak n F A_arr A_inst Manalyze).
  { pose proof Hweak as Hweak0. destruct Hweak0.
    constructor; cbn in *; assumption. }
  assert (Hsw_analyze : solver_propagation_weak n F A_arr
      (PropagationStable A_inst) Manalyze).
  { unfold solver_propagation_weak in Hsw |- *. cbn in Hsw |- *.
    split; [exact (proj1 Hsw) | exact Hweak_analyze]. }
  assert (Hcancel_analyze : propagation_cancel_ready n F A_arr
      (PropagationStable A_inst) Manalyze focus).
  { unfold propagation_cancel_ready.
    split; [exact Hsw_analyze |].
    unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    split; [exact Hlevel |]. split; [exact Hfocus_wf |].
    split; [exact Hprocessed |]. split; [exact Hfocus_level |].
    split; [exact Hfrontier |]. split; [exact Hheap |].
    split; [exact Hcovers | exact Hreasonless]. }
  assert (Hanalysis : analysis_cancel_ready n F A_arr
      (PropagationStable A_inst) Manalyze focus).
  { unfold analysis_cancel_ready.
    exists Mconf.
    split; [exact Hcancel0 |]. split; [exact Hequiv |].
    unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    split; [exact Hheap |]. split; [exact Hcovers |].
    split; [exact Hreasonless |]. split; [exact Hfocus_level |].
    exact (msw_cla_inc_nonnegative Hweak). }
  assert (Hcert : propagation_conflict_cert n F Manalyze Cconf).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    unfold propagation_conflict_cert in H_propagation_conflict_cert |- *.
    exact H_propagation_conflict_cert. }
  assert (Hptr : conflict_ptr_denotes Manalyze p Cconf).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    unfold conflict_ptr_denotes in H_conflict_ptr_denotes |- *.
    exact H_conflict_ptr_denotes. }
  assert (Hseed : msolver_seed_shadow Manalyze).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_msolver_seed_shadow. }
  assert (Hmodel : ms_model Manalyze = @nil Z).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_ms_model. }
  assert (Hfinite : msat_fp32_positive_finite (ms_cla_decay Manalyze)).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_msat_fp32_positive_finite. }
  assert (Hsame : msat_fp32_same
      (ms_cla_decay Manalyze) (ms_cla_decay Mcur)).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_msat_fp32_same. }
  assert (Hroot_lt :
      ms_root_level Manalyze < Zlength (mt_lim (ms_core Manalyze))).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    pose proof (msw_root_range Hweak); lia. }
  lazymatch goal with
  | Hwatch : minisat_base_watch_completed ?entry ->
      minisat_watch_conflict_ready n Mconf |- _ =>
      assert (Hreuse_analyze : solver_search_reuse entry Manalyze)
  end.
  { intro Hbase.
    lazymatch goal with
    | Hwatch : minisat_base_watch_completed ?entry ->
        minisat_watch_conflict_ready n Mconf |- _ =>
        destruct (Hwatch Hbase) as [watch_focus [Hwatch_level Hexcept]]
    end.
    pose proof (level_of_msolver_view_levels__analyze n Mconf
      (lit_var_c watch_focus) (Zlength (mt_lim (ms_core Mconf)))
      (msw_trail_wf Hweak) Hwatch_level) as Hwatch_cell.
    change (minisat_base_watch_completed Mconf).
    apply (minisat_base_exception_above_zero__api_reentry Mconf watch_focus).
    - pose proof (msw_root_range Hweak). unfold Manalyze in Hroot_lt.
      cbn in Hroot_lt. lia.
    - exact Hexcept. }
  destruct (msw_tags_clear Hweak) as [Hzeros Htagged0].
  assert (Htags_len : Zlength (ms_tags Mconf) = n).
  { pose proof (msw_shape Hweak) as Hshape.
    pose proof (msw_size Hweak) as Hsize.
    unfold solver_shape in Hshape; lia. }
  assert (Hlen_nat : length (ms_tags Mconf) = Z.to_nat n).
  { apply Nat2Z.inj.
    rewrite <- Zlength_correct.
    rewrite Htags_len.
    rewrite Z2Nat.id by exact (msw_n_range Hweak).
    reflexivity. }
  assert (Htags : ms_tags Manalyze = repeat_Z 0 n).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    unfold repeat_Z.
    rewrite <- Hlen_nat.
    apply msat_forall_zero_repeat. exact Hzeros. }
  assert (Htagged : ms_tagged Manalyze = @nil Z).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact Htagged0. }
  assert (Hlit_bound : 2 * n <= INT_MAX).
  { pose proof (msolver_inv_literal_bound n F A_arr A_inst Mconf Hweak).
    rewrite <- (msw_size Hweak) in H. exact H. }
  assert (Hstats_base_len : Zlength (ms_stats Mconf) = 11).
  { pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape; tauto. }
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
  rewrite Zsublist_nil by lia.
  unfold solver_search_conflict_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_analyze_pre, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  Intros act asg opos rsn trl tgs.
  Exists Manalyze.
  unfold Manalyze.
  rewrite scalars_rep_cla_inc_stats_eq, vecs_rep_cla_inc_stats_eq, fp_rep_cla_inc_stats_eq.
  unfold msolver_with_cla_inc_stats.
  cbn.
  Exists act asg opos rsn trl tgs.
  rewrite Hconflicts_addr.
  fold stats_ptr.
  cancel.
  sep_apply Hstats_refold.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_search_which_implies_wit_36 : solver_search_which_implies_wit_36.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( model_copy_progress n Mselected model_words i ) as H_model_copy_progress.
  sep_apply_l_atomic
    (CharArray.seg_split_to_missing_i values 0 i n
      (mt_assigns (ms_core Mselected)) 0).
  - dump_pre_spatial. unfold model_copy_progress in H_model_copy_progress. lia.
  - replace (i - 0) with i by lia. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_11_pure : solver_setnvars_partial_solve_wit_11_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_partial_solve_wit_14_pure : solver_setnvars_partial_solve_wit_14_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 snv_shape; msat_manual_entailer_with ltac:(int_auto || lia || tauto || (unfold solver_shape; intuition lia)).
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_1 : solver_setnvars_which_implies_wit_1.
Proof.
  (* The block's RHS is the [setnvars_arrays_at] restatement, which is
     exactly [setnvars_open_arrays]; opening with that lemma keeps the bundle
     folded on both sides, and the EX list is spelled wl..tgs. *)
  (LLM_pre_process ltac:(lia || int_auto));
  sep_apply setnvars_open_arrays;
  Intros wl0 act0 asg0 opos0 rsn0 lvl0 trl0 tgs0;
  Exists wl0 act0 asg0 opos0 rsn0 lvl0 trl0 tgs0;
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_setnvars_which_implies_wit_3 : solver_setnvars_which_implies_wit_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 unfold solver_wlists_tail, solver_array_tail. Intros physical.
  sep_apply (proj1 (VecpArray.undef_seg_unfold wlc (2*var) physical ltac:(lia))).
  Exists physical.
  unfold VecpArray.vec_undef_store.
  rewrite Vecp.slot_eq.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_simplify_return_wit_3_split_goal_spatial : solver_simplify_return_wit_3_split_goal_spatial.
Abort.


Lemma proof_of_solver_simplify_return_wit_3 : solver_simplify_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!.
  msat_simplify_propagation_frame M_solver_simplify_spec Mprop s_pre
    assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec.
Qed.


Lemma proof_of_solver_simplify_entail_wit_2_1_split_goal_1 : solver_simplify_entail_wit_2_1_split_goal_1.
Abort.


Lemma proof_of_solver_simplify_entail_wit_2_1 : solver_simplify_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!.
  rewrite PreH12; rewrite sel_vec_learnt; cancel.
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_7 : solver_simplify_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply solver_simplify_control_join_rep_assigns__simplify.
  cancel.
Qed.


Lemma proof_of_solver_simplify_which_implies_wit_15 : solver_simplify_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_clauses_literals, stats_learnts_literals in *.
  rename M_solver_simplify_spec into M.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mdone ) as H_msolver_inv.
  bind_fact (solver_simplify_reuse M Mdone) as Hreuse.
  set (props := MiniSatTarget.uint64_sum_to_int
    (Znth 6 (ms_stats Mdone) 0) (Znth 8 (ms_stats Mdone) 0)).
  set (Mfinish := msolver_simpdb_update Mdone
    (mt_qhead (ms_core Mdone)) props).
  assert (Hreuse_finish : solver_simplify_reuse M Mfinish).
  { unfold solver_simplify_reuse. intros Hentry.
    apply minisat_watch_completed_same_fields__api_reentry with (M := Mdone);
      [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
    exact (Hreuse Hentry). }
  assert (Hcap_finish : ms_cap Mfinish = ms_cap M).
  { change (ms_cap Mdone = ms_cap M). assumption. }
  assert (Hroot_finish : ms_root_level Mfinish = ms_root_level M).
  { change (ms_root_level Mdone = ms_root_level M). assumption. }
  Exists Mfinish.
  assert (Hfinish_inv :
    msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec smp_A_arr_solver_simplify_spec Mfinish).
  { unfold Mfinish.
    apply solver_assuming_simpdb_update__api_reentry.
    exact H_msolver_inv. }
  unfold solver_simplify_finish_transition.
  subst props.
  cancel.
  unfold solver_rep_levels_wl_at, solver_cancel_owned.
  unfold solver_simplify_finish_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  unfold solver_simplify_control_scalars_frame, solver_scalars_rep.
  unfold stats_without_simplify_totals_rep, stats_rep.
  replace (solver_fp_rep s Mfinish) with (solver_fp_rep s Mdone)
    by (unfold Mfinish; reflexivity).
  replace (solver_vecs_rep s Mfinish) with (solver_vecs_rep s Mdone)
    by (unfold Mfinish; reflexivity).
  replace (solver_trail_array_rep Mfinish trl)
    with (solver_trail_array_rep Mdone trl)
    by (unfold Mfinish; reflexivity).
  replace (solver_levels_slice_at s Mfinish levels_ptr_solver_simplify_spec)
    with (solver_levels_slice_at s Mdone levels_ptr_solver_simplify_spec)
    by (unfold Mfinish; reflexivity).
  subst Mfinish.
  set (P := MiniSatTarget.uint64_sum_to_int
    (Znth 6 (ms_stats Mdone) 0) (Znth 8 (ms_stats Mdone) 0)) in *.
  set (U := msolver_simpdb_update Mdone
    (mt_qhead (ms_core Mdone)) P) in *.
  pose proof (msa_shape (msas_weak Hfinish_inv)) as Hshape_finish.
  assert (HU_size : ms_size U = ms_size Mdone) by (unfold U; reflexivity).
  assert (HU_cap : ms_cap U = ms_cap Mdone) by (unfold U; reflexivity).
  assert (HU_qtail : ms_qtail U = ms_qtail Mdone) by (unfold U; reflexivity).
  assert (HU_pending_qhead : ms_capacity_pending_qhead U =
      ms_capacity_pending_qhead Mdone) by (unfold U; reflexivity).
  assert (HU_pending : ms_capacity_root_propagation_pending U =
      ms_capacity_root_propagation_pending Mdone)
    by (unfold U; reflexivity).
  assert (HU_core : ms_core U = ms_core Mdone) by (unfold U; reflexivity).
  assert (HU_root : ms_root_level U = ms_root_level Mdone)
    by (unfold U; reflexivity).
  assert (HU_simpdb_assigns : ms_simpdb_assigns U =
      mt_qhead (ms_core Mdone)) by (unfold U; reflexivity).
  assert (HU_simpdb_props : ms_simpdb_props U = P)
    by (unfold U; reflexivity).
  assert (HU_verbosity : ms_verbosity U = ms_verbosity Mdone)
    by (unfold U; reflexivity).
  assert (HU_binary : ms_binary U = ms_binary Mdone)
    by (unfold U; reflexivity).
  assert (HU_activity : ms_activity U = ms_activity Mdone)
    by (unfold U; reflexivity).
  assert (HU_orderpos : ms_orderpos U = ms_orderpos Mdone)
    by (unfold U; reflexivity).
  assert (HU_reasons : ms_reason_words U = ms_reason_words Mdone)
    by (unfold U; reflexivity).
  assert (HU_tags : ms_tags U = ms_tags Mdone)
    by (unfold U; reflexivity).
  assert (HU_wm : ms_wm U = ms_wm Mdone) by (unfold U; reflexivity).
  assert (HU_prob : ms_prob U = ms_prob Mdone) by (unfold U; reflexivity).
  assert (HU_learnt : ms_learnt U = ms_learnt Mdone)
    by (unfold U; reflexivity).
  assert (HU_binary_lits : ms_binary_lits U = ms_binary_lits Mdone)
    by (unfold U; reflexivity).
  assert (HU_stats : ms_stats U = ms_stats Mdone)
    by (unfold U; reflexivity).
  rewrite ?HU_size, ?HU_cap, ?HU_qtail, ?HU_pending_qhead, ?HU_pending,
    ?HU_core, ?HU_root, ?HU_simpdb_assigns, ?HU_simpdb_props, ?HU_verbosity,
    ?HU_binary, ?HU_activity, ?HU_orderpos, ?HU_reasons, ?HU_tags, ?HU_wm,
    ?HU_prob, ?HU_learnt, ?HU_binary_lits, ?HU_stats.
  split_pure_spatial.
  - Intros. msat_cancel_sound.
    csimpl. msat_manual_entailer_with ltac:(lia).
  - msat_manual_entailer_with ltac:(unfold solver_shape in Hshape_finish; tauto).
Qed.


Lemma proof_of_solver_solve_entail_wit_5_3_split_goal_1 : solver_solve_entail_wit_5_3_split_goal_1.
Abort.


Lemma proof_of_solver_solve_entail_wit_5_3 : solver_solve_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  entailer!.
  rewrite <- PreH20; cancel.
  assert (Hstatus :
    signed_last_nbits
      (- Znth (retval_2 - 0) (mt_assigns (ms_core Mcur)) 0) 8 =
    (1 - 2 * lit_sign_c (Znth k raw 0)) *
      Znth (lit_var_c (Znth k raw 0))
        (mt_assigns (ms_core Mcur)) 0)
    by (msat_solve_selector_join k raw Mcur n_solver_solve_spec retval_2).
  rewrite Hstatus; cancel.
Qed.


Lemma proof_of_solver_solve_partial_solve_wit_23_pure : solver_solve_partial_solve_wit_23_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lit_sign_c_range (Znth k raw 0)).
  assert (Hsign : lit_sign_c (Znth k raw 0) = 0 \/ lit_sign_c (Znth k raw 0) = 1) by lia.
  destruct Hsign as [Hs | Hs]; rewrite Hs in *;
  (Intros; split_pures; dump_pre_spatial; solve [auto | (nia)]).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_5 : solver_solve_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( msolver_inv_assuming_strong n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  bind_fact ( A_arr_solver_solve_spec = assumption_prefix raw (Zlength raw) ) as H_A_arr.
  bind_fact ( Forall (lit_wf_c n_solver_solve_spec) raw ) as H_Forall.
  bind_fact ( Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0 = 1 - 2 * lit_sign_c (Znth k raw 0) ) as
      H_Znth.
  set (current := Znth k raw 0).
  assert (Hlit : lit_wf_c n_solver_solve_spec current).
  { unfold current. apply (Forall_Znth_elim Z (lit_wf_c n_solver_solve_spec) raw 0 k H_Forall).
    lia. }
  assert (Hlit0 : 0 <= current) by (unfold lit_wf_c in Hlit; lia).
  assert (Hvr : 0 <= lit_var_c current < n_solver_solve_spec).
  { apply lit_var_c_in_range. exact Hlit. }
  assert (Hprefix : assumption_prefix raw (k + 1) =
      assumption_prefix raw k ++ (lit_denote current :: nil)).
  { unfold assumption_prefix, current.
    rewrite (sublist_split 0 (k + 1) k raw) by lia.
    rewrite (sublist_single 0 k raw) by lia.
    rewrite lits_denote_app. reflexivity. }
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hold.
  pose proof (msa_trail_wf Hold) as Htrailwf.
  assert (Hcell : Znth (lit_var_c current)
      (mt_assigns (ms_core Mcur)) 0 = lit_sig current).
  { unfold current in *.
    rewrite H_Znth.
    unfold lit_sig, lit_sign_c.
    destruct (Z.odd (Znth k raw 0)); reflexivity. }
  assert (Htrue : assump_true_at_root (ms_core Mcur)
      (Zlength (mt_lim (ms_core Mcur))) (lit_denote current)).
  { unfold assump_true_at_root. split.
    - unfold eval_partial_literal.
      rewrite mt_pv_nonneg by (rewrite lit_var_c_denote; lia).
      apply (proj1 (lit_true_iff (mt_assigns (ms_core Mcur)) current Hlit0)).
      exact Hcell.
    - assert (Hassigned : Znth (lit_var_c current)
          (mt_assigns (ms_core Mcur)) 0 <> 0).
      { rewrite Hcell. apply lit_sig_nonzero. }
      pose proof (proj1 (mtw_assigned_iff Htrailwf
        (lit_var_c current) Hvr) Hassigned) as Hin.
      destruct (In_Znth_index
        (map lit_var_c (mt_trail (ms_core Mcur)))
        (lit_var_c current) Hin) as [j [Hj Hmap]].
      rewrite Zlength_map_Z in Hj.
      assert (Htrailvar : trail_var (ms_core Mcur) j = lit_var_c current).
      { unfold trail_var.
        rewrite <- (Znth_map Z Z lit_var_c
          (mt_trail (ms_core Mcur)) j 0 0 Hj).
        exact Hmap. }
      pose proof (mtw_levels_agree Htrailwf j Hj) as Hagree.
      rewrite lit_var_c_denote.
      rewrite <- Htrailvar.
      rewrite Hagree.
      apply prop_level_processed_level_le. }
  assert (Hnew : msolver_inv_assuming n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec
      (assumption_prefix raw (k + 1)) Mcur).
  { constructor.
    - exact (msa_size Hold).
    - exact (msa_n_range Hold).
    - exact (msa_shape Hold).
    - exact (msa_F_wf Hold).
    - exact (msa_A_wf Hold).
    - exact Htrailwf.
    - exact (msa_level_bound Hold).
    - destruct (msa_decisions Hold) as [A_inst [Hdec Hincl]].
      exists A_inst. split; [exact Hdec|].
      intros x Hx. rewrite Hprefix. apply in_or_app. left.
      apply Hincl. exact Hx.
    - rewrite Hprefix. intros x Hx. apply in_app_or in Hx.
      destruct Hx as [Hx | Hx].
      + apply (msa_proc_incl Hold). exact Hx.
      + simpl in Hx. destruct Hx as [<- | Hcontra]; [|contradiction].
        rewrite H_A_arr. unfold assumption_prefix.
        rewrite (sublist_self raw (Zlength raw) eq_refl).
        apply lits_denote_in. apply Znth_In. lia.
    - rewrite Hprefix. apply Forall_app. split.
      + exact (msa_proc_sat Hold).
      + constructor; [exact Htrue | constructor].
    - exact (msa_stable Hold).
    - exact (msa_reasons_ent Hold).
    - exact (msa_reasons_inj Hold).
    - exact (msa_trail_impl Hold).
    - exact (msa_db_wf Hold).
    - exact (msa_db_matches Hold).
    - exact (msa_db_implied Hold).
    - exact (msa_db_complete Hold).
    - exact (msa_learnt_db Hold).
    - exact (msa_prob_db Hold).
    - exact (msa_binary_out Hold).
    - exact (msa_reasons_mem Hold).
    - exact (msa_reason_head Hold).
    - exact (msa_reason_bin Hold).
    - exact (msa_wmap_exact Hold).
    - exact (msa_tags_clear Hold).
    - exact (msa_heap_wf Hold).
    - exact (msa_cla_inc_nonnegative Hold).
    - exact (msa_seed Hold). }
  assert (Hstrong : msolver_inv_assuming_strong n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec
      (assumption_prefix raw (k + 1)) Mcur).
  { constructor.
    - exact Hnew.
    - exact (msas_prop_level H_msolver_inv_assuming_strong).
    - exact (msas_watch_frontier H_msolver_inv_assuming_strong).
    - exact (msas_heap_covers H_msolver_inv_assuming_strong).
    - exact (msas_reasonless_current H_msolver_inv_assuming_strong). }
  unfold assumption_true_advance.
  subst assumption_status.
  sep_apply store_char_undef_store_char.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_13 : solver_solve_which_implies_wit_13.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Hkind : failure_kind = 0 \/ failure_kind = 1) by lia.
destruct Hkind as [Hkind | Hkind].
{ destruct (PreH8 Hkind) as [[Hstrong Hdrain] Hreuse]. rename Mfailure into Mcur.
rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M.
  bind_fact (msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur) as Hstrong.
  bind_fact (solver_query_reuse M Mcur) as Hreuse.
  bind_fact (ms_capacity_root_propagation_pending Mcur = 0) as Hpending.
  bind_fact (msolver_seed_shadow Mcur) as Hseed.
  bind_fact (ms_size Mcur = n) as Hsize.
  bind_fact (mt_qhead (ms_core Mcur) = ms_qtail Mcur) as Hdrain.
  unfold solver_cancel_post.
  Split.
  - Intros.
    assert (Hlen : Zlength (mt_lim (ms_core Mcur)) <= 0) by assumption.
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mcur /\ solver_query_reentry n F Mcur /\ msolver_seed_shadow Mcur).
    { intro Hentry.
      destruct (solver_assuming_empty_base_recovery__api_reentry
        n F A_arr (assumption_prefix raw k) Mcur Hstrong Hpending
        (Hreuse Hentry) Hseed Hlen) as [Hbase [_ Hseed_current]].
      split; [exact Hbase|]. split; [|exact Hseed_current].
      exact (solver_base_recovery_drained_reentry__api_reentry
        n F Mcur Hbase Hdrain). }
    Exists Mcur. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep s Mcur levels_ptr solve_wl).
      cancel.
    + (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - Intros orderpos order.
    destruct H as (Hlevel & Hheap & Hincl & Hreinserted).
    set (Mpost := msolver_cancel_project Mcur 0 orderpos order
      (ms_root_level Mcur)).
    assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mcur))) by lia.
    assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
    { rewrite <- Hsize. exact Hheap. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mpost /\ solver_query_reentry n F Mpost /\ msolver_seed_shadow Mpost).
    { intro Hentry.
      destruct (solver_assuming_cancel_zero_base_recovery__api_reentry
        n F A_arr (assumption_prefix raw k) Mcur orderpos order
        Hstrong Hpending (Hreuse Hentry) Hseed Hpositive Hheap_n
        Hincl Hreinserted) as [Hbase [_ Hseed_post]].
      split; [exact Hbase|]. split; [|exact Hseed_post].
      exact (solver_cancel_project_reentry__api_reentry
        n F Mcur orderpos order (ms_root_level Mcur) Hbase). }
    Exists Mpost. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + unfold Mpost.
      sep_apply (solver_cancel_project_join_rep s Mcur levels_ptr 0
        orderpos order (ms_root_level Mcur) solve_wl).
      cancel.
    + unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
      cbn. msat_manual_entailer_with ltac:(lia).
}
{ destruct (PreH9 Hkind) as [[Hready Hreuse] Hfalse]. rename Mfailure into Mconf. rename failure_focus into focus.
rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M.
  bind_fact (propagation_cancel_ready n F A_arr
    (PropagationAssuming (assumption_prefix raw (k + 1))) Mconf focus) as Hready.
  bind_fact (solver_query_reuse_guard M -> minisat_watch_conflict_ready n Mconf) as Hreuse.
  bind_fact (minisat_resident_false_clause Mconf) as Hfalse.
  bind_fact (msolver_seed_shadow Mconf) as Hseed.
  bind_fact (ms_size Mconf = n) as Hsize.
  unfold solver_cancel_post.
  Split.
  - Intros.
    assert (Hdepth : Zlength (mt_lim (ms_core Mconf)) = 0).
    { pose proof (Zlength_nonneg (mt_lim (ms_core Mconf))). lia. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mconf /\ solver_query_reentry n F Mconf /\ msolver_seed_shadow Mconf).
    { intro Hentry.
      pose proof (solver_propagation_conflict_base_recovery__api_reentry
        n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1)))
        Mconf focus Hready (Hreuse Hentry) Hfalse Hdepth) as Hbase.
      split; [exact Hbase|]. split; [|exact Hseed].
      exact (solver_base_recovery_false_reentry__api_reentry
        n F Mconf Hbase Hfalse). }
    Exists Mconf. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep s Mconf levels_ptr solve_wl).
      cancel.
    + (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - Intros orderpos order.
    destruct H as (Hlevel & Hheap & Hincl & Hreinserted).
    set (Mpost := msolver_cancel_project Mconf 0 orderpos order
      (ms_root_level Mconf)).
    assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mconf))) by lia.
    assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
    { rewrite <- Hsize. exact Hheap. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mpost /\ solver_query_reentry n F Mpost /\ msolver_seed_shadow Mpost).
    { intro Hentry.
      destruct (solver_conflict_cancel_zero_base_recovery__api_reentry
        n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1)))
        Mconf focus orderpos order Hready (Hreuse Hentry)
        Hseed Hpositive Hheap_n Hincl Hreinserted)
        as [Hbase [_ Hseed_post]].
      split; [exact Hbase|]. split; [|exact Hseed_post].
      exact (solver_cancel_project_reentry__api_reentry
        n F Mconf orderpos order (ms_root_level Mconf) Hbase). }
    Exists Mpost. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + unfold Mpost.
      sep_apply (solver_cancel_project_join_rep s Mconf levels_ptr 0
        orderpos order (ms_root_level Mconf) solve_wl).
      cancel.
    + unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
      cbn. msat_manual_entailer_with ltac:(lia).
}
Qed.
