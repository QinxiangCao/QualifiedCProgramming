From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.Reals.Reals.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.


Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.

Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_analysis_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.
Lemma proof_of_solver_analyze_entail_wit_17 : solver_analyze_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( retval = lit_var_c (Znth (ind - 1 + 1 - 0) (mt_trail (ms_core Mresolved)) 0) ) as H_retval.
  bind_fact ( Znth (retval_2 - 0) (ms_tags Mresolved) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_2 = lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mresolved)) 0) ) as H_retval_2.
  bind_fact ( analysis_core_equiv M0 Mresolved ) as H_analysis_core_equiv.
  bind_fact ( msolver_seed_shadow Mresolved ) as H_msolver_seed_shadow.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  replace (ind - 1 + 1 - 0) with ind in * by lia.
  replace (retval_2 - 0) with retval_2 in * by lia.
  replace (retval - 0) with retval in * by lia.
  replace (ind - 0) with ind in * by lia.
  fold (trail_var (ms_core Mresolved) ind) in H_retval, H_retval_2.
  rewrite H_retval_2 in H_Znth.
  rewrite H_retval in *.
  pose proof H_analyze_backward_scan_inv as Hscan.
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Htail
      [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mresolved anz_focus Hready) as [Hsize Hreason_core].
  assert (Hstats_pure :
    solver_analyze_frame s_pre Mresolved anz_wl |--
      “ Zlength (ms_stats Mresolved) = 11 ”).
  { unfold solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame.
    Intros asg. (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]). }
  prop_apply_p Hstats_pure.
  Intros_p Hstats.
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr_back 0 anz_n
    (ms_activity Mresolved)).
  Intros_p Hactivity_raw.
  assert (Hactivity : Zlength (ms_activity Mresolved) = anz_n) by lia.
  assert (Hshape : solver_shape Mresolved).
  { eapply analysis_cancel_ready_shape__analyze; eauto. }
  match goal with
  | |- ?P |-- _ =>
      assert (Hspatial : P |--
        solver_rep_analyze_at s_pre Mresolved reasons levels_ptr trail tags anz_wl ** (Veci.rep learnt_pre words_resolved ** ((&( "l_Undef" ) # Char |-> 0) ** ((&( "l_True" ) # Char |-> 1) ** ((&( "lit_Undef" ) # Int |-> (-2)) ** ((&( "true" ) # Int |-> 1) ** ((&( "false" ) # Int |-> 0))))))))
  end.
  { rewrite Hsize.
    unfold solver_analyze_inert_at.
    Intros.
    sep_apply (analyze_frame_join s_pre Mresolved anz_wl).
    Intros asg.
    unfold solver_rep_analyze_at, solver_rep_at.
    Exists activity_ptr_back asg orderpos_ptr_back.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
      solver_trail_array_rep.
    (Intros; split_pure_spatial; [msat_cancel_sound; cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]). }
  destruct (Z.eq_dec cnt 1) as [Hcntone|Hcntnotone].
  - pose proof (analyze_backward_scan_exit__analyze
      anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind
      Sresolved Rresolved learnt_resolved H_analyze_backward_scan_inv H_Znth Hcntone) as Hexit.
    rewrite Hsize in *.
    Right.
    assert (Htwice : 2 * ms_size Mresolved <= INT_MAX)
      by (unfold solver_shape in Hshape; tauto).
    split_pure_spatial.
    + exact Hspatial.
    + split_pures; dump_pre_spatial; solve [ assumption | lia ].
  - assert (Hcntgt : 1 < cnt) by lia.
    destruct (analyze_backward_scan_selected__analyze
      anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind
      Sresolved Rresolved learnt_resolved H_analyze_backward_scan_inv H_Znth Hcntgt)
      as [Cnext [Hnonzero [Htarget Hselected]]].
    rewrite Hsize in *.
    Left. Exists Cnext.
    assert (Htwice : 2 * ms_size Mresolved <= INT_MAX)
      by (unfold solver_shape in Hshape; tauto).
    split_pure_spatial.
    + Intros.
      exact Hspatial.
    + split_pures; dump_pre_spatial; solve [ auto | lia ].
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_7_pure : solver_analyze_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  sep_apply (valid_store_ptr (&( "c" )) c).
  (* valid_store_ptr yields [valid_ptr_value c], i.e. [0 <= c /\ c <= addr_max_unsigned], and micromega cannot see
     inside that definition -- without this unfold lia cannot close [0 <= c]. *)
  unfold valid_ptr_value in *.
  Intros_p Hc.
  dump_pre_spatial.
  lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_21_pure : solver_analyze_partial_solve_wit_21_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_29_pure : solver_analyze_partial_solve_wit_29_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( reason_target_wf anz_n Mcur_2 x c Ccur_2 ) as H_reason_target_wf.
  split_pures.
  all: dump_pre_spatial;
       unfold reason_target_wf, lit_wf_c in H_reason_target_wf;
       unfold msat_true in *;
       destruct H_reason_target_wf as
         [_ [_ [_ [_ [[_ [_ Hwf]] | [co [Hfalse _]]]]]]];
       try lia;
       congruence.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_42_learnt_pure : solver_analyze_partial_solve_wit_42_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_43_learnt_pure : solver_analyze_partial_solve_wit_43_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_54_learnt_pure : solver_analyze_partial_solve_wit_54_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 0.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_70_learnt_pure : solver_analyze_partial_solve_wit_70_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 0.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_79_learnt_pure : solver_analyze_partial_solve_wit_79_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hr : 0 <= j - 0 < Zlength clause_words2) by lia.
  pose proof (sat_shared_lib.Forall_Znth_elim Z (solver_qcp_model.lit_wf_c anz_n)
    clause_words2 0 (j - 0) PreH7 Hr) as Hlit.
  unfold solver_qcp_model.lit_wf_c in Hlit.
  subst j.
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_88_learnt_pure : solver_analyze_partial_solve_wit_88_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_learnt_offset_congruence.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_182_pure : solver_analyze_partial_solve_wit_182_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Forall (lit_wf_c anz_n) words_compact ) as H_Forall.
  bind_fact ( solver_shape Mclear ) as H_solver_shape.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as H_analysis_cancel_ready.
  assert (Hindex : 0 <= 1 < Zlength words_compact) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 1 H_Forall Hindex) as Hlit.
  unfold lit_wf_c in Hlit.
  destruct Hlit as [Hlow Hhigh].
  pose proof (analysis_cancel_ready_reason_core anz_n anz_F anz_A_arr K Mclear anz_focus H_analysis_cancel_ready)
    as Hreason_core.
  destruct Hreason_core as [Hn_size _].
  unfold solver_shape in H_solver_shape.
  destruct H_solver_shape as [_ [_ [Htwo [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]]].
  apply _derivable1_andp_intros; apply dump_spatial_left; rewrite Z.sub_0_r; lia.
Qed.


Lemma proof_of_solver_analyze_safety_wit_45_learnt : solver_analyze_safety_wit_45_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial.
   msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_22 : solver_analyze_which_implies_wit_22.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply solver_rep_analyze_at_shape__analyze.
  unfold solver_rep_analyze_at, solver_rep_at.
  Intros act asg opos.
  split_pure_spatial.
  - rewrite PreH2.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
      solver_levels_slice_at, solver_reason_levels_frame_at,
      solver_removable_frame_at, solver_scalars_rep, solver_vecs_rep,
      clause_new_scalars_frame.
    Exists act asg opos.
    msat_manual_entailer_with lia.
  - split_pures; dump_pre_spatial; auto.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_24 : solver_analyze_which_implies_wit_24.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mmin anz_focus PreH2) as [Hn _].
  unfold solver_rep_analyze_at, solver_rep_at.
  Intros act asg opos.
  rewrite Hn.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_reason_levels_frame_at,
    solver_removable_frame_at, solver_scalars_rep, solver_vecs_rep,
    clause_new_scalars_frame.
  Exists act asg opos.
  msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_1 : solver_lit_removable_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( 0 <= minl_pre ) as H_minl_pre.
  bind_fact ( minl_pre <= 4294967295 ) as H_minl_pre_2.
  bind_fact ( assigned_below_current (msolver_view lrm_n M0) (lit_var_c l_pre) ) as H_assigned_below_current.
  bind_fact ( reason_target_wf lrm_n M0 (lit_var_c l_pre) (Znth (lit_var_c l_pre) (ms_reason_words M0) 0) Croot ) as
      H_reason_target_wf.
  bind_fact ( analysis_tags_exact lrm_n (ms_tags M0) (ms_tagged M0) ) as H_analysis_tags_exact.
  bind_fact ( In (lit_var_c l_pre) (map lit_var_c (mt_trail (ms_core M0))) ) as H_In.
  match goal with
  | MS : msolver |- _ =>
      pose proof
        (removable_dfs_loop_init__record
          lrm_n MS l_pre minl_pre Croot H_analysis_tags_exact H_assigned_below_current H_reason_target_wf
          (conj H_minl_pre H_minl_pre_2)) as Hinv
  end.
  subst retval_4.
  unfold removable_reason_array_hole, StorePtrAsElement.storeA.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_seg reasons_ptr 0 (lit_var_c l_pre) lrm_n
      (Znth (lit_var_c l_pre) (ms_reason_words M0) 0) (ms_reason_words M0)).
  { dump_pre_spatial. lia. }
  replace (lit_var_c l_pre - 0) with (lit_var_c l_pre) by lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (Veci.rep_ptr_rep &( s_pre # "solver_t" ->ₛ "tagged") p
    (ms_tagged M0)).
  Exists (@nil Z) (sublist 0 0 (ms_stack M0) +:: retval_5) (ms_tags M0) (ms_tagged M0).
  try subst retval_5; try subst retval_6.
  simpl in *.
  split_pure_spatial.
  - msat_manual_entailer_with ltac:(lia).
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    + intros x [<- | []]. exact H_In.
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_12_3 : solver_lit_removable_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( retval_2 = lit_var_c (Znth (i - 0) clause_words 0) ) as H_retval_2.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan_2 stack_scan_2 tags_scan_2
      tagged_scan_2 Cnext v c i ) as H_removable_reason_scan_inv.
  bind_fact ( Cnext = lits_denote clause_words ) as H_Cnext.
  replace (i - 0) with i in * by lia.
  replace (retval_2 - 0) with retval_2 in * by lia.
  assert (Hxdef : retval_2 = literal_var (Znth i Cnext (Pos 0))).
  { rewrite H_Cnext. unfold lits_denote.
    rewrite (Znth_map Z literal lit_denote clause_words i 0 (Pos 0)) by lia.
    rewrite lit_var_c_denote. exact H_retval_2. }
  assert (Hneq : literal_var (Znth i Cnext (Pos 0)) <> v).
  { eapply removable_reason_scan_side_neq__lit_removable;
      [exact H_analysis_cancel_ready | exact H_removable_reason_scan_inv |].
    rewrite H_Cnext, lits_denote_length. lia. }
  assert (Hbelow : assigned_below_current (msolver_view lrm_n M0) retval_2).
  { rewrite Hxdef.
    eapply removable_reason_scan_side_assigned_below__lit_removable;
      [exact H_analysis_cancel_ready | exact H_removable_reason_scan_inv | | exact Hneq].
    rewrite H_Cnext, lits_denote_length. lia. }
  destruct (analysis_cancel_ready_semantic_core__lit_removable
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Htrail Hsemantic].
  assert (Hlevel : level_of (msolver_view lrm_n M0) retval_2 = Some 0).
  { eapply assigned_below_level_word_zero__lit_removable;
      eauto. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_scan_2 stack_scan_2 tags_scan_2 tagged_scan_2
    Cnext v c (i + 1)).
  { eapply removable_reason_scan_advance_level0__lit_removable.
    - exact H_removable_reason_scan_inv.
    - rewrite H_Cnext, lits_denote_length. lia.
    - rewrite <- Hxdef. exact Hlevel. }
  Exists done_scan_2 stack_scan_2
    tags_scan_2 tagged_scan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_13_1 : solver_lit_removable_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth retval_7 tags_now_2 0 = 0 ) as H_Znth.
  bind_fact ( reason_target_wf lrm_n M0 retval_7 (Znth retval_7 (ms_reason_words M0) 0) Cpush ) as H_reason_target_wf.
  bind_fact ( retval_7 = lit_var_c retval_6 ) as H_retval_7.
  bind_fact ( retval_6 = tag_lit (Znth (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) ) as
      H_retval_6.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) = msat_true ) as
      H_is_tag.
  bind_fact ( stack_after = sublist 0 (Zlength stack_now_2 - 1) stack_now_2 ) as H_stack_after.
  bind_fact ( stack_now_2 = stack_after +:: Znth (Zlength stack_now_2 - 1) stack_now_2 0 ) as H_stack_now_2.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (Znth (Znth (Zlength
      stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( incl stack_now_2 (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( In (lit_var_c l_pre) (ms_tagged M0) ) as H_In.
  bind_fact ( removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now_2 tagged_now_2 stack_now_2
      done_2 ) as H_removable_dfs_loop_inv.
  replace (retval_4 - 1) with (Zlength stack_now_2 - 1) in * by lia.
  replace (retval_7 - 0) with retval_7 in * by lia.
  set (v_now := Znth (Zlength stack_now_2 - 1) stack_now_2 0) in *.
  set (stack_prefix := sublist 0 (Zlength stack_now_2 - 1) stack_now_2) in *.
  rewrite H_stack_after in H_stack_now_2.
  assert (Hshape_stack : stack_now_2 = stack_prefix ++ v_now :: nil)
    by exact H_stack_now_2.
  assert (Hstack : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_now_2 tagged_now_2 (v_now :: stack_prefix) done_2).
  { eapply removable_dfs_loop_inv_stack_perm__lit_removable
      with (stack := stack_now_2).
    - rewrite Hshape_stack.
      pose proof (Permutation_middle stack_prefix nil v_now) as Hperm.
      rewrite app_nil_r in Hperm. exact (Permutation_sym Hperm).
    - exact H_removable_dfs_loop_inv. }
  assert (Hfocus : reason_target_wf lrm_n M0 v_now
    (Znth v_now (ms_reason_words M0) 0) Cnext) by exact H_removable_reason_focus.
  pose proof
    (reason_target_wf_tag_shape__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus v_now
      (Znth v_now (ms_reason_words M0) 0) Cnext
      H_analysis_cancel_ready Hfocus H_is_tag) as Hshape_reason.
  assert (Hclause_wf : Forall (literal_wf lrm_n) Cnext).
  { rewrite Hshape_reason. constructor.
    - apply lit_denote_wf. apply trail_lit_of_wf. lia.
    - constructor.
      + unfold literal_wf, var_in_range.
        rewrite literal_var_neg, lit_var_c_denote. lia.
      + constructor. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_2 stack_prefix tags_now_2 tagged_now_2
    Cnext v_now (Znth v_now (ms_reason_words M0) 0) 1).
  { unfold removable_reason_scan_inv.
    split; [exact Hstack|].
    split; [exact H_removable_reason_focus|].
    split; [rewrite Hshape_reason;
      rewrite !Zlength_cons; rewrite Zlength_nil; lia|].
    split; [exact Hclause_wf|].
    intros k Hk. lia. }
  assert (Hnew_dfs : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) (replace_Znth retval_7 1 tags_now_2)
    (tagged_now_2 ++ retval_7 :: nil)
    (stack_prefix ++ retval_7 :: nil) (v_now :: done_2)).
  { eapply removable_dfs_tagged_push__lit_removable
      with (F := lrm_F) (A_arr := lrm_A_arr) (K := lrm_K) (focus := lrm_focus)
        (C := Cnext) (p := Znth v_now (ms_reason_words M0) 0)
        (q := Znth retval_7 (ms_reason_words M0) 0) (Cx := Cpush).
    - exact H_analysis_cancel_ready.
    - exact Hscan.
    - exact H_In.
    - exact H_is_tag.
    - rewrite H_retval_7, H_retval_6. reflexivity.
    - lia.
    - exact H_Znth.
    - exact H_reason_target_wf. }
  assert (Hnew_incl : incl (stack_prefix ++ retval_7 :: nil)
    (map lit_var_c (mt_trail (ms_core M0)))).
  { intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | [<- | []]].
    - apply H_incl. rewrite Hshape_stack. apply in_or_app. left. exact Hy.
    - apply assigned_below_in_trail__lit_removable with (n := lrm_n).
      unfold removable_dfs_loop_inv in Hnew_dfs.
      destruct Hnew_dfs as [fresh [_ [_ [_ [_ [Hpart [Hassigned _]]]]]]].
      apply Hassigned.
      eapply Permutation_in; [exact Hpart|].
      apply in_or_app. right. apply in_or_app. right.
      simpl. auto. }
  assert (Htags : analysis_tags_exact lrm_n
    (replace_Znth retval_7 1 tags_now_2)
    (tagged_now_2 ++ retval_7 :: nil)).
  { unfold removable_dfs_loop_inv in Hnew_dfs.
    destruct Hnew_dfs as [fresh [_ [Hexact _]]].
    exact Hexact. }
  Exists (v_now :: done_2)
    (stack_prefix ++ retval_7 :: nil)
    (replace_Znth retval_7 1 tags_now_2)
    (tagged_now_2 ++ retval_7 :: nil).
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth retval_7 1 tags_now_2)).
  sep_apply_l_atomic (PtrArray.full_to_seg reasons_ptr lrm_n (ms_reason_words M0)).
  sep_apply_l_atomic (IntArray.full_to_seg levels_ptr lrm_n (mt_levels (ms_core M0))).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_31_pure : solver_lit_removable_partial_solve_wit_31_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_lit_removable_retval_var_bounds retval retval_7 stack_now M0 lrm_n Hv Hw Hlo Hhi.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_41_pure : solver_lit_removable_partial_solve_wit_41_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_7_1 : solver_analyze_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  bind_fact ( Zlength tags_now = anz_n ) as H_tags_len;
  bind_fact ( order_heap_wf anz_n heap_now orderpos_now ) as H_order_wf;
  bind_fact ( Permutation (ms_order Mcur) heap_now ) as H_order_perm;
  bind_fact ( Zlength activity_now = anz_n ) as H_act_len;
  bind_fact ( Zlength orderpos_now = anz_n ) as H_pos_len;
  bind_fact ( Znth (lit_var_c (tag_lit c)) (ms_tags Mcur) 0 = 0 )
    as H_tag_zero;
  msat_analyze_e7_semantic_facts anz_n anz_F anz_A_arr K Mcur
    anz_focus c x Ccur phase_2 words_2 cnt ind p S0 R2 learnt0;
  bind_fact ( analysis_core_equiv M0 Mcur ) as H_core_equiv;
  bind_fact ( msolver_seed_shadow Mcur ) as H_seed.
  pose proof H_loop_inv as Hloop.
  rewrite H_phase in Hloop.
  destruct (msat_analyze_e7_ready_semantics
    anz_n anz_F anz_A_arr K Mcur anz_focus H_cancel_ready)
    as (Htrailwf & Hstable & Htrailimpl & Hrootunit).
  destruct (msat_analyze_e7_select_bridge
    anz_n anz_F anz_A_arr K Mcur anz_focus c ind cnt p x Ccur
    words_2 S0 R2 learnt0 Hloop H_reason_target H_is_tag H_x_in_S0 H_cnt_len
    H_analyze_inv H_tagged_perm H_shape Htrailwf Hstable Hrootunit) as
    (HCshapeX & Horder0 & Hrank_sel & HvalidA & HentA & HCndA & HinvNew &
     HpendS & HresolvedRanks & Htags & Hind & Hwords & Hroot &
     Hindvarrange & HrangeXn & Hqneq).
  destruct (msat_analyze_e7_resolve_sets
    anz_n Mcur c x Ccur S0 R2 learnt0 HCshapeX (proj1 HrangeXn)
    H_x_level H_tag_level H_x_in_S0) as (HresolveL & HresolveAdd & _).
  destruct (msat_analyze_e7_pending_split
    anz_n anz_F Mcur x cnt S0 R2 learnt0 H_analyze_inv H_x_in_S0 H_cnt_len)
    as (Hlenremove & Hperm_move).
  set (qv := lit_var_c (tag_lit c)).
  assert (Hqrange : 0 <= qv < anz_n).
  { unfold qv. split; [exact H_tag_lo | exact H_tag_hi]. }
  set (Mtag := analyze_tag_step_msolver Mcur
    (replace_Znth qv 1 (ms_tags Mcur))
    (ms_tagged Mcur ++ (qv :: nil))
    activity_now orderpos_now heap_now var_inc_now).
  destruct (msat_analyze_e7_tag_state
    anz_n anz_F anz_A_arr K _ Mcur Mtag anz_focus qv x
    activity_now orderpos_now heap_now S0 R2 learnt0 var_inc_now
    eq_refl H_cancel_ready Htags Hqrange H_tag_zero H_tagged_perm Hperm_move
    H_order_wf H_order_perm H_shape H_size H_act_len H_pos_len H_core_equiv
    H_seed) as
    (Hqnotseen & HtagsNew & HpermNew & HreadyTag & HshapeTag & HsizeTag &
     HcoreMTag & HcoreCurTag & HseedTag & HcoreTag & HviewTag &
     HrootTag & HqtailTag).
  assert (HresolveS :
    resolve_S (msolver_view anz_n Mcur) x Ccur S0 R2 learnt0 =
    zremove x S0 ++ (qv :: nil)).
  { exact (HresolveAdd Hqnotseen). }
  rewrite HresolveS, HresolveL in HinvNew.
  assert (Hlennew :
    cnt + 1 = Zlength (zremove x S0 ++ (qv :: nil))).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  pose proof (msat_analyze_e7_side_rank
    anz_n Mcur c x ind Ccur HCshapeX HvalidA Hrank_sel
    (proj1 Hind) Hqneq) as Hqrank.
  assert (HpendingRanks :
    forall y, In y (zremove x S0 ++ (qv :: nil)) -> exists r,
      assignment_rank (msolver_view anz_n Mcur) y = Some r /\
      Z.of_nat r <= ind).
  {
    intros y Hy. rewrite in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    - apply In_zremove_iff in Hy. destruct Hy as (HyS & Hyx).
      exact (HpendS y HyS Hyx).
    - cbn in Hy. destruct Hy as [Hy | []]. subst y. exact Hqrank.
  }
  assert (HexPending : exists y, In y (zremove x S0 ++ (qv :: nil))).
  { exists qv. apply in_or_app. right. left. reflexivity. }
  assert (Htagged :
    analyze_tagged_step anz_n anz_F anz_A_arr K Mcur Mtag anz_focus
      c (tag_lit c) Ccur S0 R2 learnt0 x
      (zremove x S0 ++ (qv :: nil)) (x :: R2) learnt0 words_2 (cnt + 1)).
  {
    unfold analyze_tagged_step.
    rewrite HrootTag, HcoreTag.
    refine (conj HreadyTag (conj HcoreCurTag (conj Hroot (conj H_reason_target
      (conj H_is_tag (conj eq_refl (conj H_x_in_S0 (conj Horder0
      (conj H_analyze_inv (conj HvalidA (conj HentA (conj HCndA
      (conj H_tag_level (_)))))))))))))).
    refine (conj (eq_sym HresolveS) (conj eq_refl (conj (eq_sym HresolveL)
      (conj Hlennew (conj Hwords (conj H_learnt_eq (conj HtagsNew
      (HpermNew)))))))).
  }
  assert (Hback :
    analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mtag anz_focus
      words_2 (cnt + 1) ind (zremove x S0 ++ (qv :: nil))
      (x :: R2) learnt0).
  {
    unfold analyze_backward_scan_inv.
    rewrite HviewTag, HqtailTag, HrootTag, HcoreTag.
    refine (conj HreadyTag (conj HinvNew (conj Hlennew (conj _ (conj Hind
      (conj Hwords (conj Hroot (conj H_learnt_eq (conj HtagsNew (conj HpermNew
      (conj HpendingRanks (conj HresolvedRanks (_))))))))))))); [lia |].
    destruct HexPending as (y & Hy).
    destruct (HpendingRanks y Hy) as (r & Hr & Hri).
    exists y, r. repeat split; assumption.
  }
  pose proof (msat_analyze_e7_scan_index_nonzero
    anz_n Mcur Mtag ind (zremove x S0 ++ (qv :: nil)) (x :: R2) learnt0
    HcoreTag HtagsNew HpermNew HexPending HpendingRanks (proj1 Hind))
    as Hzero.
  assert (Htagged_target :
    analyze_tagged_step anz_n anz_F anz_A_arr K Mcur Mtag anz_focus
      (Znth x (ms_reason_words Mcur) 0)
      (tag_lit (Znth x (ms_reason_words Mcur) 0)) Ccur
      S0 R2 (lits_denote (tl words_2)) x
      (zremove x S0 ++ qv :: nil) (x :: R2) learnt0
      words_2 (cnt + 1)).
  { rewrite <- H_reason_word, H_learnt_eq. exact Htagged. }
  rename Hback into Hback_target.
  assert (Hbounds_target :
    0 <= lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mtag)) 0) < anz_n).
  { rewrite Z.sub_0_r, HcoreTag. exact Hindvarrange. }
  destruct Hbounds_target as (Hlower_target & Hupper_target).
  assert (Hzero_target :
    Znth
      (lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mtag)) 0) - 0)
      (ms_tags Mtag) 0 = 0 -> 0 < ind).
  { rewrite !Z.sub_0_r. exact Hzero. }
  Exists (zremove x S0 ++ qv :: nil) (x :: R2) learnt0
    words_2 (replace_Znth qv 1 (ms_tags Mcur))
    (ms_tagged Mcur ++ qv :: nil)
    activity_now orderpos_now heap_now var_inc_now Mtag.
  fold Mtag.
  bind_fact (retval_8 = lit_var_c (tag_lit c)) as Hpush.
  bind_fact (tags_now = replace_Znth (lit_var_c (tag_lit c)) 1 (ms_tags Mcur)) as Htagsnow.
  rewrite Hpush, Htagsnow. fold qv.
  sep_apply (CharArray.full_to_seg tags_loop anz_n (replace_Znth qv 1 (ms_tags Mcur))).
  assert (Hframe : solver_analyze_frame s_pre Mtag anz_wl = solver_analyze_frame s_pre Mcur anz_wl)
    by reflexivity.
  assert (Hinert : solver_analyze_inert_at s_pre Mtag anz_n activity_ptr_loop orderpos_ptr_loop
    reasons_loop levels_ptr trail_loop tags_loop =
    solver_analyze_inert_at s_pre Mcur anz_n activity_ptr_loop orderpos_ptr_loop
    reasons_loop levels_ptr trail_loop tags_loop) by reflexivity.
  rewrite Hframe, Hinert.
  unfold Mtag, analyze_tag_step_msolver, msolver_analysis_update.
  cbn [ms_qtail ms_cap ms_activity ms_orderpos ms_reason_words ms_core ms_tags ms_order ms_stack ms_tagged ms_var_inc ms_cla_inc ms_learnt ms_prob ms_binary ms_binary_lits ms_stats].
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_7_learnt : solver_analyze_entail_wit_12_7_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  assert (H_l_prime_2 :
      words_scan_2 +:: Znth (j - 0) clause_words2 0 =
      words_scan_2 +:: Znth (j - 0) clause_words2 0) by reflexivity.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_9 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 > 0 ) as H_Znth_2.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  rewrite <- H_Mscan_2 in H_retval_11.
  Right.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hreason & HSold & ERscan & HLold).
  msat_analyze_tag_step_open v Mnext j clause_words2 activity1
    orderpos1 heap1 var_inc1 Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Hempty : sublist 1 1 Ccur = nil) by (apply ms_sublist_one_one_nil).
  assert (ESbase : Sscan_2 = zremove x_2 S0_2).
  { rewrite HSold. subst j. rewrite Hempty.
    unfold resolve_S, resolve_new_S. cbn [filter map app].
    rewrite app_nil_r. reflexivity. }
  assert (ELbase : learnt_scan_2 = learnt0_2).
  { rewrite HLold. subst j. rewrite Hempty.
    unfold resolve_learnt, resolve_new_lits. cbn [filter map app].
    rewrite app_nil_r. reflexivity. }
  assert (Hnotcur : ~ In v (analyze_tags Sscan_2 Rscan_2 learnt_scan_2))
    by (apply (ms_analyze_var_untagged anz_n (ms_tags Mscan_2)
          (ms_tagged Mscan_2));
        [exact Htagsold | exact Hpermold | unfold v; lia | unfold v in *; lia]).
  assert (Hnotinitial : ~ In v (analyze_tags S0_2 R0_2 learnt0_2))
    by (apply (ms_analyze_notin_initial_resolved v x_2 S0_2 R0_2 Sscan_2
          Rscan_2 learnt0_2 learnt_scan_2);
        [exact Hnotcur | exact ESbase | exact ERscan | exact ELbase]).
  assert (Hnotmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = false).
  { apply zmem_false_iff. exact Hnotinitial. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  assert (Hvneqx : v <> x_2).
  { intro Evx. apply Hnotinitial.
    unfold analyze_tags. apply in_or_app. left. rewrite Evx. exact Hinx. }
  destruct Hreason as
    [bx [dx [rx [Hassx [Hlevx [Hrankx [Hsatx Hside]]]]]]].
  assert (Hvarqneq : literal_var (lit_denote q) <> x_2)
    by (rewrite lit_var_c_denote; unfold q, v in *;
        replace (j - 0) with j in Hvneqx by lia; exact Hvneqx).
  destruct (Hside (lit_denote q) HqC Hvarqneq) as
    [_ [dq [rq [Hlevq [Hrankq [Hdqle Hrqlt]]]]]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l; exact Hpermold).
  msat_analyze_scan_level_transport v Mscan_2 rq Hlevq Hrankq Eqv Eview
    Htrailwf.
  msat_analyze_selected_level_bounds v Mscan_2 rq dq
    H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth Edq Hagree.
  msat_analyze_offlevel_flags anz_n Mact q dq Hlevq0 Hdqne Eqv Eview.
  msat_analyze_scan_words_grow anz_n q Mscan_2 words_scan_2 Sscan_2 Rscan_2
    R0_2 learnt_scan_2 Hpermold ERscan.
  msat_analyze_resolve_step_word q anz_n Mact Ccur j clause_words2 x_2 S0_2
    R0_2 learnt0_2 Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow
    Eqv Hnotmem.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      Sscan_2 Rscan_2 (learnt_scan_2 ++ (lit_denote q :: nil))
      (words_scan_2 ++ (q :: nil)) cnt)
    by (msat_analyze_scan_inv_word Mnext phase H_Ccur Hwordlennew
          Hwordsnext HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
    (learnt_scan_2 ++ (lit_denote q :: nil))
    (words_scan_2 ++ (q :: nil)) Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame Mnext Mscan_2 v activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    rewrite <- H_Mscan_2.
    replace (j - 0) with j by lia.
    fold q.
    fold v in H_retval_7, H_retval_6.
    rewrite H_retval_7, H_retval_6.
    sep_apply CharArray.full_to_seg.
    cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_12_learnt : solver_analyze_entail_wit_12_12_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  Left.
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mscan_2)
      (ms_tagged Mscan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hperm : Permutation (ms_tagged Mscan_2)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (HS : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HR : Rscan_2 = nil) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HL : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  subst j. unfold sublist, analyze_start_S in HS.
  unfold sublist, analyze_start_learnt in HL. cbn in HS, HL.
  subst Sscan_2 Rscan_2 learnt_scan_2.
  unfold analyze_tags in Hperm. cbn in Hperm.
  assert (Htaggednil : ms_tagged Mscan_2 = nil).
  { apply Permutation_nil. apply Permutation_sym. exact Hperm. }
  set (v := lit_var_c (Znth (0 - 0) clause_words2 0)).
  assert (Hv : 0 <= v < anz_n) by (unfold v; lia).
  assert (Hseen : In v (ms_tagged Mscan_2)).
  { eapply analysis_tags_exact_nonzero_in__lit_removable;
      [exact Htags | exact Hv |].
    intro Hzero. apply H_Znth.
    rewrite H_retval_4, !Z.sub_0_r. exact Hzero. }
  rewrite Htaggednil in Hseen. contradiction.
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_14_learnt : solver_analyze_entail_wit_12_14_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  unfold solver_analyze_open_at in *. msat_analyze_scan_stop orderpos_ptr_scan_2 activity_ptr_scan_2 S0_2 R0_2
    learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 Mscan_2 phase j Ccur clause_words2 anz_n K Mact.
Qed.


Lemma proof_of_solver_analyze_entail_wit_13_1_learnt : solver_analyze_entail_wit_13_1_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R2
      learnt0 x Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  subst phase Mact. cbn in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as
    [Hready [Hequiv_scan [Hind_scan [Hroot
    [HCwf [HCnodup [Hjscan [Hcnt [Hwords [Hden
    [Htags [Hperm Hinitial]]]]]]]]]]]].
  destruct Hinitial as
    [HS0 [HR0 [Hlearnt0 [Hx0 [Hqtail_initial
    [Hconflict [HS [HR Hlearnt]]]]]]]].
  destruct Hconflict as
    [Hent [Hfalse [Hconf_wf [Hconf_nd [q [HqC Hqlevel]]]]]].
  assert (HCzero : Zlength Ccur = 0).
  { rewrite H_Ccur, lits_denote_length.
    pose proof (Zlength_nonneg clause_words2). lia. }
  exfalso.
  destruct Ccur as [|a rest].
  - contradiction.
  - rewrite Zlength_cons in HCzero.
    pose proof (Zlength_nonneg rest). lia.
Qed.


Lemma proof_of_solver_analyze_entail_wit_14_4_learnt : solver_analyze_entail_wit_14_4_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame words_done Sdone Rdone learnt_done Mdone.
Qed.


Lemma proof_of_solver_analyze_entail_wit_16 : solver_analyze_entail_wit_16.
Proof.
  LLM_pre_process ltac:(lia).
  unfold solver_analyze_open_at in *.
  bind_fact ( Znth (retval - 0) (ms_tags Mresolved) 0 = 0 ) as H_Znth.
  bind_fact ( retval = lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mresolved)) 0) ) as H_retval.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  replace (retval - 0) with retval in H_Znth by lia.
  replace (ind - 0) with ind in H_retval by lia.
  assert (Hzero :
    Znth (trail_var (ms_core Mresolved) ind) (ms_tags Mresolved) 0 = 0).
  { unfold trail_var. rewrite <- H_retval. exact H_Znth. }
  destruct (analyze_backward_scan_decr__analyze
    anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind
    Sresolved Rresolved learnt_resolved H_analyze_backward_scan_inv Hzero)
    as [Hinv' [Hind' [[Hvar1 Hvar2] Hguard']]].
  replace (ind - 1 - 0) with (ind - 1) by lia.
  replace (lit_var_c (Znth (ind - 1) (mt_trail (ms_core Mresolved)) 0) - 0)
    with (lit_var_c (Znth (ind - 1) (mt_trail (ms_core Mresolved)) 0)) by lia.
  fold (trail_var (ms_core Mresolved) (ind - 1)).
  split_pure_spatial.
  - cancel (solver_analyze_frame s_pre Mresolved anz_wl).
    cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.


Lemma proof_of_solver_analyze_entail_wit_25 : solver_analyze_entail_wit_25.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( solver_shape Mresolution ) as H_solver_shape.
  bind_fact ( Forall (lit_wf_c anz_n) words_uip ) as H_Forall.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mresolution anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mresolution) (ms_tagged Mresolution) ) as H_analysis_tags_exact.
  bind_fact ( analyze_clause_cert anz_n anz_F Mresolution words_uip ) as H_analyze_clause_cert.
  bind_fact ( minimize_tag_scope anz_n Mresolution words_uip nil ) as H_minimize_tag_scope.
  pose proof (analyze_clause_cert_vars_in_trail__analyze
    anz_n anz_F Mresolution words_uip H_analyze_clause_cert) as Htrail.
  pose proof (analyze_minimize_init__analyze
    anz_n Mresolution words_uip ltac:(lia) H_Forall H_analysis_tags_exact H_minimize_tag_scope) as Hinit.
  pose proof (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mresolution anz_focus H_analysis_cancel_ready) as [Hsize Hreason_core].
  Exists (sublist 0 1 words_uip) (@nil Z) words_uip (@nil Z) Mresolution.
  (Intros; split_pure_spatial; [ | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  rewrite Hsize.
  sep_apply_r_atomic (solver_reason_levels_join__analyze
    s_pre Mresolution reasons levels_ptr trail tags anz_wl H_solver_shape).
  cancel. cancel.
Qed.



Lemma proof_of_solver_analyze_partial_solve_wit_33_pure : solver_analyze_partial_solve_wit_33_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  prop_apply_p
    (ms_analyze_db_triple_positive
       (ms_prob Mcur) (ms_learnt Mcur) (ms_binary Mcur) (ms_binary_lits Mcur)).
  Intros_p Hpos.
  destruct Hpos as [Hprob_pos [Hlearnt_pos Hbinary_pos]].
  split_pures.
  - dump_pre_spatial. exact H_analyze_resolution_loop_inv.
  - dump_pre_spatial. exact H_is_tag.
  - dump_pre_spatial.
    unfold msat_false in H_is_tag.
    destruct (analyze_resolution_real_ptr_source__analyze
      anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p H_analyze_resolution_loop_inv H_is_tag)
      as [Hbinary | [co Hin]].
    + rewrite Hbinary. exact Hbinary_pos.
    + unfold msolver_db in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * rewrite Forall_forall in Hprob_pos.
        exact (Hprob_pos (c, co) Hin).
      * rewrite Forall_forall in Hlearnt_pos.
        exact (Hlearnt_pos (c, co) Hin).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_34_pure : solver_analyze_partial_solve_wit_34_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_44_learnt_pure : solver_analyze_partial_solve_wit_44_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_91_learnt_pure : solver_analyze_partial_solve_wit_91_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_clause_word_int_range_via_wf j clause_words2 Hlit.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_139_pure : solver_analyze_partial_solve_wit_139_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  bind_fact ( 0 <= ind ) as H_ind_nonneg.
  bind_fact ( ind < ms_qtail Mresolved ) as H_ind.
  destruct H_analyze_backward_scan_inv as [Hready _].
  pose proof (analysis_cancel_ready_qtail_eq__analyze
    anz_n anz_F anz_A_arr K Mresolved anz_focus Hready) as Hqtail.
  assert (Hi : 0 <= ind - 1 + 1 < Zlength (mt_trail (ms_core Mresolved))) by lia.
  msat_analyze_trail_lit Hready (ind - 1 + 1) Hi as Hlit.
  pose proof (lit_var_c_in_range anz_n _ Hlit) as Hrange.
  split_pures; dump_pre_spatial;
    replace (ind - 1 + 1 - 0) with (ind - 1 + 1) by lia;
    lia.
Qed.


Lemma proof_of_solver_analyze_safety_wit_36_learnt : solver_analyze_safety_wit_36_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_analyze_scan_count_bound.
Qed.


