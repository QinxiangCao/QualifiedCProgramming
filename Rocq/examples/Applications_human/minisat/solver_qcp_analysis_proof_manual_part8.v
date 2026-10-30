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
Lemma proof_of_solver_analyze_which_implies_wit_7 : solver_analyze_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia).
    bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  pose proof H_analyze_resolution_loop_inv as Hinv.
  destruct Hinv as [_ [_ [_ [_ [Htags Hphase]]]]].
  destruct Htags as [Htagslen [Hnodup [Hrange [Hcells Hiff]]]].
  assert (Hv : 0 <= lit_var_c q < anz_n) by lia.
  assert (Hnotin : ~ In (lit_var_c q) (ms_tagged Mcur)).
  { intro Hin.
    pose proof (proj2 (Hiff (lit_var_c q) Hv) Hin) as Htag.
    lia. }
  assert (Hnodup' : NoDup (lit_var_c q :: ms_tagged Mcur)).
  { constructor; assumption. }
  pose proof (msat_cons_list_var_bounded anz_n (lit_var_c q) (ms_tagged Mcur)
    Hv Hrange) as Hrange'.
  pose proof (NoDup_Z_bounded_length
    (lit_var_c q :: ms_tagged Mcur) anz_n ltac:(lia) Hnodup' Hrange') as Hlen.
  assert (Hlt : Zlength (ms_tagged Mcur) < anz_n).
  { rewrite Zlength_correct. cbn in Hlen. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_10 : solver_analyze_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (Mtag = analyze_tag_step_msolver Mcur tags_j tagged_j
    activity_j orderpos_j heap_j var_inc_j) as Htag.
  bind_fact (solver_shape Mtag) as Hshape.
  bind_fact (anz_n = ms_size Mtag) as Hsize.
  assert (Hqtail : ms_qtail Mtag = ms_qtail Mcur) by (rewrite Htag; reflexivity).
  replace (ms_prob Mcur) with (ms_prob Mtag) by (rewrite Htag; reflexivity).
  replace (ms_learnt Mcur) with (ms_learnt Mtag) by (rewrite Htag; reflexivity).
  replace (ms_binary Mcur) with (ms_binary Mtag) by (rewrite Htag; reflexivity).
  replace (ms_binary_lits Mcur) with (ms_binary_lits Mtag) by (rewrite Htag; reflexivity).
  unfold msat_false.
  sep_apply (solver_analyze_open_at_rep s Mtag anz_n activity_ptr_loop
    orderpos_ptr_loop reasons levels trail tags anz_wl Hshape (eq_sym Hsize)).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_12 : solver_analyze_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_focus_clause_db c Mcur ( Intros_p Hb; bind_fact ( is_learnt_now = msat_true ) as Hlt;
    destruct Hb as [Hc [Htag [Hlits Hinitialized]]]; unfold msat_true, msat_false in Hlt, Htag; congruence ).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_32_split_goal_1 : solver_analyze_which_implies_wit_32_split_goal_1.
Abort.


Lemma proof_of_solver_analyze_which_implies_wit_32_split_goal_2 : solver_analyze_which_implies_wit_32_split_goal_2.
Abort.


Lemma proof_of_solver_analyze_which_implies_wit_32 : solver_analyze_which_implies_wit_32.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Forall_Znth_elim Z (lit_wf_c anz_n)
    words_compact 0 1 PreH1 ltac:(lia)) as Hlit.
  replace (1 - 0) with 1 by lia.
  pose proof (lit_var_c_in_range anz_n _ Hlit) as Hrange.
  entailer!.
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_8 : solver_lit_removable_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) = msat_false ) as
      H_is_tag.
  bind_fact ( Cnext = lits_denote clause_words ) as H_Cnext.
  bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  bind_fact ( stack_after = sublist 0 (Zlength stack_now - 1) stack_now ) as H_stack_after.
  bind_fact ( stack_now = stack_after +:: Znth (Zlength stack_now - 1) stack_now 0 ) as H_stack_now.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( incl stack_now (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now tagged_now stack_now done ) as
      H_removable_dfs_loop_inv.
  replace (retval_5 - 1) with (Zlength stack_now - 1) in * by lia.
  set (v_now := Znth (Zlength stack_now - 1) stack_now 0) in *.
  set (stack_prefix := sublist 0 (Zlength stack_now - 1) stack_now) in *.
  rewrite H_stack_after in H_stack_now.
  assert (Hshape : stack_now = stack_prefix ++ v_now :: nil) by exact H_stack_now.
  assert (Hstack : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_now tagged_now (v_now :: stack_prefix) done).
  { eapply removable_dfs_loop_inv_stack_perm__lit_removable
      with (stack := stack_now).
    - rewrite Hshape.
      pose proof (Permutation_middle stack_prefix nil v_now) as Hperm.
      rewrite app_nil_r in Hperm. exact (Permutation_sym Hperm).
    - exact H_removable_dfs_loop_inv. }
  assert (HCnonempty : 1 <= Zlength Cnext).
  { pose proof H_removable_reason_focus as Htarget.
    unfold removable_reason_focus, reason_target_wf in Htarget.
    destruct Htarget as [Hvrange [Hp [Hpnonzero [Hreason Hkind]]]].
    destruct Hkind as [[Htag [Hpositive Hwf]] |
      [co [Htag [Hbinary [Hin HC]]]]].
    - assert (Hclause_shape : Cnext =
        lit_denote (trail_lit_of (ms_core M0) v_now) ::
        literal_neg
          (lit_denote (tag_lit (Znth v_now (ms_reason_words M0) 0))) :: nil).
      { eapply reason_target_wf_tag_shape__lit_removable.
        + exact H_analysis_cancel_ready.
        + exact H_removable_reason_focus.
        + exact Htag. }
      rewrite Hclause_shape, Zlength_cons, Zlength_cons, Zlength_nil. lia.
    - rewrite HC.
      destruct
        (analysis_cancel_ready_semantic_core__lit_removable
          lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready)
        as [_ [_ [_ [Hdb _]]]].
      destruct (db_wf_obj lrm_n (msolver_db M0)
        (Znth v_now (ms_reason_words M0) 0) co Hdb Hin)
        as [Hlen _].
      unfold denote_obj. rewrite lits_denote_length. lia. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done stack_prefix tags_now tagged_now Cnext v_now
    (Znth v_now (ms_reason_words M0) 0) 1).
  { unfold removable_reason_scan_inv.
    split; [exact Hstack|].
    split; [exact H_removable_reason_focus|].
    split.
    - rewrite H_Cnext, lits_denote_length in HCnonempty.
      rewrite H_Cnext, lits_denote_length.
      split; [lia | exact HCnonempty].
    - split.
      + rewrite H_Cnext. apply lits_denote_wf. exact H_Forall.
      + intros k Hk. lia. }
  pose proof HCnonempty as Hwords_nonempty.
  rewrite H_Cnext, lits_denote_length in Hwords_nonempty.
  assert (Hincl : incl (v_now :: stack_prefix)
    (map lit_var_c (mt_trail (ms_core M0)))).
  { intros x [<- | Hx].
    - apply H_incl. rewrite Hshape. apply in_or_app. right.
      simpl. auto.
    - apply H_incl. rewrite Hshape. apply in_or_app. left. exact Hx. }
  assert (Hmod : Znth v_now (ms_reason_words M0) 0 mod 2 = 0).
  { assert (Heven : Z.even (Znth v_now (ms_reason_words M0) 0) = true).
    { unfold msat_false, is_tag in H_is_tag.
      rewrite <- Z.negb_even in H_is_tag.
      destruct (Z.even (Znth v_now (ms_reason_words M0) 0)) eqn:Heven.
      - reflexivity.
      - simpl in H_is_tag. discriminate. }
    exact (clause_ptr_mod2 _ Heven). }
  assert (Hrem : Z.rem (Znth v_now (ms_reason_words M0) 0) 2 = 0).
  { apply Z.rem_divide; [lia |].
    apply Z.mod_divide; [lia | exact Hmod]. }
  sep_apply Veci.rep_ptr_rep.
  Exists done stack_prefix tags_now tagged_now.
  split_pure_spatial.
  - cancel (PtrArray.seg reasons_ptr 0 lrm_n (ms_reason_words M0)).
    cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_lit_removable_partial_solve_wit_29_pure : solver_lit_removable_partial_solve_wit_29_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures;
  (dump_pre_spatial; subst retval retval_7; lia).
Qed.


Lemma proof_of_solver_lit_removable_safety_wit_36 : solver_lit_removable_safety_wit_36.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  unfold clause_hdr_word in PreH12.
  apply _derivable1_andp_intros.
  all: dump_pre_spatial.
  all: destruct is_learnt_now; lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_11 : solver_lit_removable_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact lrm_n tags_now tagged_now ) as H_analysis_tags_exact.
  bind_fact ( Znth v tags_now 0 = 0 ) as H_Znth.
  bind_fact ( Znth v (ms_reason_words M0) 0 <> 0 ) as H_Znth_2.
  pose proof
    (analysis_tags_exact_untagged_strict__lit_removable
      lrm_n tags_now tagged_now v H_analysis_tags_exact ltac:(lia) H_Znth) as Hstrict.
  destruct (analysis_cancel_ready_reason_target__lit_removable
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus v H_analysis_cancel_ready ltac:(lia) H_Znth_2)
    as [Cpush Htarget].
  Exists Cpush. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_22 : solver_analyze_entail_wit_22.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (analyze_resolution_exit_uip__analyze _ _ _ _ _ _ _ _ PreH8) as Huip.
  cbv zeta in Huip.
  destruct Huip as [Hready [Hlen [Hwf [Hnd [Hcert [Htags [Hincl Hscope]]]]]]].
  assert (HlenR : Zlength (replace_Znth 0 (lit_neg_c p) words_before) = Zlength words_before)
    by (rewrite Zlength_replace_Znth; reflexivity).
  sep_apply (Veci.rep_ptr_intro learnt_pre learnt_ptr_uip
    (replace_Znth 0 (lit_neg_c p) words_before) cap);
    [| solve [exact PreH1 | lia] ..].
  Exists (replace_Znth 0 (lit_neg_c p) words_before).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_analyze_entail_wit_24 : solver_analyze_entail_wit_24.
Proof.
  LLM_pre_process ltac:(lia).
  set (bit := unsigned_last_nbits
    (Z.shiftl 1 (Z.land (Znth (retval - 0)
      (mt_levels (ms_core Mresolution)) 0) 31)) 32).
  assert (Hbit : 0 <= bit < 2 ^ 32).
  { subst bit. apply unsigned_Lastnbits_range. lia. }
  assert (Hmin : 0 <= minl < 2 ^ 32).
  { split; [exact PreH15|].
    change (minl < 4294967296).
    lia. }
  assert (Hlor : 0 <= Z.lor minl bit <= UINT_MAX).
  { pose proof (unsigned_last_nbits_lor_distr_missing
      minl bit 32 ltac:(lia) Hmin Hbit) as E.
    pose proof (unsigned_Lastnbits_range (Z.lor minl bit) 32 ltac:(lia)) as Hr.
    rewrite E in Hr.
    change (0 <= Z.lor minl bit < 4294967296) in Hr.
    lia. }
  sep_apply (Veci.rep_ptr_intro learnt_pre lits words_uip cap
    (Zlength words_uip) (Zlength words_uip) (Zlength words_uip)
    eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) PreH2).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_analyze_entail_wit_26_1 : solver_analyze_entail_wit_26_1.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( solver_shape Mmin_2 ) as H_solver_shape.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin_2 anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( 1 <= j ) as H_j.
  bind_fact ( j <= i ) as H_j_2.
  bind_fact ( incl (map lit_var_c words_min_2) (map lit_var_c (mt_trail (ms_core Mmin_2))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min_2) (ms_tagged Mmin_2) ) as H_incl_2.
  replace (i - 0) with i in * by lia.
  assert (Hcur_in : In (Znth i words_min_2 0) words_min_2).
  { apply Znth_In. lia. }
  pose proof (replace_Znth_incl_self__analyze
    words_min_2 j (Znth i words_min_2 0) ltac:(lia) Hcur_in) as Hself.
  pose proof (incl_map_of_incl__analyze
    lit_var_c _ _ Hself) as Hmap.
  assert (Htagged : incl
    (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
    (ms_tagged Mmin_2)).
  { intros x Hx. apply H_incl_2, Hmap, Hx. }
  assert (Htrail : incl
    (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
    (map lit_var_c (mt_trail (ms_core Mmin_2)))).
  { intros x Hx. apply H_incl, Hmap, Hx. }
  pose proof (analyze_minimize_keep__analyze
    anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j
    H_analyze_minimize_loop_inv ltac:(lia) H_j H_j_2) as Hkeep.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mmin_2 anz_focus H_analysis_cancel_ready) as [Hsize _].
  assert (Hreplen :
    Zlength (replace_Znth j (Znth i words_min_2 0) words_min_2) =
    Zlength words_min_2) by apply Zlength_replace_Znth.
  unfold analyze_minimize_loop_inv in Hkeep.
  sep_apply (IntArray.full_to_seg lits (Zlength words_min_2)
    (replace_Znth j (Znth i words_min_2 0) words_min_2)).
  sep_apply (Veci.rep_ptr_intro learnt_pre lits
    (replace_Znth j (Znth i words_min_2 0) words_min_2) cap
    (Zlength words_min_2) (Zlength words_min_2) (Zlength words_min_2)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  Exists (kept_2 ++ Znth i words_min_2 0 :: nil)
    removed_2
    (replace_Znth j (Znth i words_min_2 0) words_min_2)
    T_2 Mmin_2.
  (Intros; split_pure_spatial; [| split_pures; dump_pre_spatial; solve [auto | lia | (int_auto)] ..]).
  rewrite Hsize.
  unfold solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_rep_analyze_at, solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_scalars_rep, solver_vecs_rep,
    clause_new_scalars_frame.
  Intros act asg opos.
  Exists act asg opos.
  msat_entailer_with ltac:(first [assumption | lia]).
Qed.



Lemma proof_of_solver_analyze_entail_wit_26_2 : solver_analyze_entail_wit_26_2.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mmin_2) (ms_tagged Mmin_2) ) as H_analysis_tags_exact.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( 1 <= j ) as H_j.
  bind_fact ( j <= i ) as H_j_2.
  bind_fact ( Forall (lit_wf_c anz_n) words_min_2 ) as H_Forall.
  bind_fact ( incl (map lit_var_c words_min_2) (map lit_var_c (mt_trail (ms_core Mmin_2))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min_2) (ms_tagged Mmin_2) ) as H_incl_2.
  unfold solver_lit_removable_post.
  Intros Mpost.
  Intros.
  destruct H as
    (Hready' & Hseed' & Hequiv' & Hret).
  destruct Hret as [(Hret & Etags & Etagged) | (Hret & Hstack & Hfresh)].
  - replace (i - 0) with i in * by lia.
    pose proof (analyze_minimize_keep__analyze
      anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j
      H_analyze_minimize_loop_inv ltac:(lia) H_j H_j_2) as Hkeep.
    pose proof (analyze_minimize_loop_inv_transport__analyze
      anz_n Mmin_2 Mpost words_uip
      (kept_2 ++ Znth i words_min_2 0 :: nil) removed_2
      (replace_Znth j (Znth i words_min_2 0) words_min_2) T_2
      (i + 1) (j + 1) Hequiv' Etags Etagged Hkeep) as Hkeep'.
    assert (Hcur : In (Znth i words_min_2 0) words_min_2).
    { apply Znth_In. lia. }
    pose proof (replace_Znth_incl_self__analyze
      words_min_2 j (Znth i words_min_2 0) ltac:(lia) Hcur) as Hincl.
    pose proof (incl_map_of_incl__analyze lit_var_c _ _ Hincl)
      as Hmap.
    assert (Hinc_tag : incl
      (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
      (ms_tagged Mpost)).
    { rewrite Etagged. intros x Hx. apply H_incl_2, Hmap, Hx. }
    assert (Ecore : ms_core Mpost = ms_core Mmin_2).
    { unfold analysis_core_equiv in Hequiv'. tauto. }
    assert (Hinc_trail : incl
      (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
      (map lit_var_c (mt_trail (ms_core Mpost)))).
    { rewrite Ecore. intros x Hx. apply H_incl, Hmap, Hx. }
    assert (Hwfwords : Forall (lit_wf_c anz_n)
      (replace_Znth j (Znth i words_min_2 0) words_min_2)).
    { apply Forall_replace_Znth; [exact H_Forall|].
      eapply Forall_Znth_elim; [exact H_Forall|lia]. }
    assert (Hbound : i + 1 <=
      Zlength (replace_Znth j (Znth i words_min_2 0) words_min_2)).
    { rewrite Zlength_replace_Znth. lia. }
    assert (Hcert : analyze_clause_cert anz_n anz_F Mpost words_uip).
    { eapply analyze_clause_cert_transport__analyze; eauto. }
    assert (Htagsexact :
      analysis_tags_exact anz_n (ms_tags Mpost) (ms_tagged Mpost)).
    { rewrite Etags, Etagged. exact H_analysis_tags_exact. }
    assert (Hcore : analysis_core_equiv M0 Mpost).
    { eapply analysis_core_equiv_trans__analyze; eauto. }
    sep_apply (solver_rep_analyze_at_shape__analyze
      s_pre Mpost reasons levels_ptr trail tags anz_wl).
    Intros.
    sep_apply (IntArray.full_to_seg lits (Zlength words_min_2)
      (replace_Znth j (Znth i words_min_2 0) words_min_2)).
    assert (Hlen : Zlength words_min_2 =
      Zlength (replace_Znth j (Znth i words_min_2 0) words_min_2)).
    { rewrite Zlength_replace_Znth. reflexivity. }
    sep_apply (Veci.rep_ptr_intro learnt_pre lits
      (replace_Znth j (Znth i words_min_2 0) words_min_2) cap
      (Zlength words_min_2) (Zlength words_min_2) (Zlength words_min_2)
      Hlen Hlen Hlen ltac:(lia) ltac:(lia) PreH4).
    Exists (kept_2 ++ Znth i words_min_2 0 :: nil)
      removed_2 (replace_Znth j (Znth i words_min_2 0) words_min_2)
      T_2 Mpost.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - lia.
Qed.



Lemma proof_of_solver_analyze_entail_wit_26_3 : solver_analyze_entail_wit_26_3.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin_2 anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( incl (map lit_var_c words_min_2) (map lit_var_c (mt_trail (ms_core Mmin_2))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min_2) (ms_tagged Mmin_2) ) as H_incl_2.
  bind_fact ( vec_buf_ok cap lits ) as H_buf.
  unfold solver_lit_removable_post.
  Intros Mpost.
  Intros.
  destruct H as
    (Hready' & Hseed' & Hequiv' & Hret).
  destruct Hret as [(Hret & Etags & Etagged) | (Hret & Hstack & Hfresh)].
  - lia.
  - destruct Hfresh as [fresh [Etagged [Htags' [Hwit Hbelow]]]].
    replace (i - 0) with i in * by lia.
    pose proof (analyze_minimize_remove__analyze
      anz_n anz_F anz_A_arr K anz_focus Mmin_2 Mpost words_uip kept_2 removed_2
      words_min_2 T_2 i j fresh H_analyze_minimize_loop_inv ltac:(lia) H_analysis_cancel_ready Hequiv'
      Etagged Htags' Hwit Hbelow) as Hremove.
    assert (Ecore : ms_core Mpost = ms_core Mmin_2).
    { unfold analysis_core_equiv in Hequiv'. tauto. }
    assert (Hinc_trail : incl (map lit_var_c words_min_2)
      (map lit_var_c (mt_trail (ms_core Mpost)))).
    { rewrite Ecore. exact H_incl. }
    assert (Hinc_tag : incl (map lit_var_c words_min_2)
      (ms_tagged Mpost)).
    { rewrite Etagged. intros x Hx. apply in_or_app. left.
      exact (H_incl_2 x Hx). }
    assert (Hcert : analyze_clause_cert anz_n anz_F Mpost words_uip).
    { eapply analyze_clause_cert_transport__analyze; eauto. }
    assert (Hcore : analysis_core_equiv M0 Mpost).
    { eapply analysis_core_equiv_trans__analyze; eauto. }
    sep_apply (solver_rep_analyze_at_shape__analyze
      s_pre Mpost reasons levels_ptr trail tags anz_wl).
    Intros.
    sep_apply (Veci.rep_ptr_intro learnt_pre lits words_min_2 cap
      (Zlength words_min_2) (Zlength words_min_2) (Zlength words_min_2)
      eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) H_buf).
    Exists kept_2
      (removed_2 ++ Znth i words_min_2 0 :: nil) words_min_2
      (T_2 ++ lit_var_c (Znth i words_min_2 0) :: fresh) Mpost.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_solver_analyze_entail_wit_29 : solver_analyze_entail_wit_29.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mstats_upd anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert anz_n anz_F Mstats_upd words_uip ) as H_analyze_clause_cert.
  bind_fact ( analyze_minimize_loop_inv anz_n Mstats_upd words_uip kept_done removed_done words_done T_done i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( Zlength (sublist 0 j words_done) = j ) as H_Zlength.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin words_uip kept removed words_min T i j ) as
      H_analyze_minimize_loop_inv_2.
  assert (Horiglen : Zlength words_min = Zlength words_uip).
  { unfold analyze_minimize_loop_inv in H_analyze_minimize_loop_inv_2. tauto. }
  assert (Hdone : Zlength words_uip <= i) by lia.
  pose proof (analyze_minimize_finish__analyze
    anz_n anz_F anz_A_arr K Mstats_upd anz_focus words_uip kept_done removed_done
    words_done T_done i j H_analysis_cancel_ready H_analyze_clause_cert H_analyze_minimize_loop_inv Hdone) as Hfinish.
  destruct Hfinish as [Hpositive [Hbounded [Hwf [Hnodup Hcert]]]].
  Exists (sublist 0 j words_done) Mstats_upd.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_solver_analyze_entail_wit_34_1 : solver_analyze_entail_wit_34_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (retval_3 - 0) (mt_levels (ms_core Mclear)) 0 > max ) as H_Znth.
  bind_fact ( retval_3 = lit_var_c (Znth (i - 0) words_compact 0) ) as H_retval_3.
  bind_fact ( retval = lit_var_c (Znth (i - 0) words_compact 0) ) as H_retval.
  bind_fact ( analyze_max_loop_inv anz_n Mclear words_compact i max_i max ) as H_analyze_max_loop_inv.
  unfold analyze_max_loop_inv in *.
  destruct H_analyze_max_loop_inv as [Hi [Hmi [Hwf [Hmaxeq Hmaxbound]]]].
  replace (i - 0) with i in H_retval_3, H_retval by lia.
  rewrite H_retval_3 in H_Znth.
  replace (lit_var_c (Znth i words_compact 0) - 0)
    with (lit_var_c (Znth i words_compact 0)) in H_Znth by lia.
  sep_apply (Veci.rep_ptr_intro learnt_pre lits words_compact cap
    (Zlength words_compact) (Zlength words_compact) (Zlength words_compact)
    eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    rewrite H_retval.
    replace (lit_var_c (Znth i words_compact 0) - 0)
      with (lit_var_c (Znth i words_compact 0)) by lia.
    split; [lia |].
    split; [lia |].
    split; [exact Hwf |].
    split; [reflexivity |].
    intros k Hk.
    destruct (Z.lt_ge_cases k i) as [Hlt | Hge].
    + pose proof (Hmaxbound k ltac:(lia)). lia.
    + assert (k = i) by lia. subst k. lia.
Qed.



Lemma proof_of_solver_analyze_entail_wit_34_2 : solver_analyze_entail_wit_34_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth (retval_2 - 0) (mt_levels (ms_core Mclear)) 0 <= max ) as H_Znth.
  bind_fact ( retval_2 = lit_var_c (Znth (i - 0) words_compact 0) ) as H_retval_2.
  bind_fact ( analyze_max_loop_inv anz_n Mclear words_compact i max_i max ) as H_analyze_max_loop_inv.
  unfold analyze_max_loop_inv in *.
  destruct H_analyze_max_loop_inv as [Hi [Hmi [Hwf [Hmaxeq Hmaxbound]]]].
  replace (i - 0) with i in H_retval_2 by lia.
  rewrite H_retval_2 in H_Znth.
  replace (lit_var_c (Znth i words_compact 0) - 0)
    with (lit_var_c (Znth i words_compact 0)) in H_Znth by lia.
  sep_apply (Veci.rep_ptr_intro learnt_pre lits words_compact cap);
    [ | first [reflexivity | lia | exact PreH3] .. ].
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    split; [lia |].
    split; [lia |].
    split; [exact Hwf |].
    split; [exact Hmaxeq |].
    intros k Hk.
    destruct (Z.lt_ge_cases k i) as [Hlt | Hge].
    + apply Hmaxbound. lia.
    + assert (k = i) by lia. subst k. exact H_Znth.
Qed.



Lemma proof_of_solver_analyze_entail_wit_35 : solver_analyze_entail_wit_35.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (1 - 0) with 1 by lia.
  replace (max_i - 0) with max_i by lia.
  set (sw := replace_Znth max_i (Znth 1 words_compact 0)
    (replace_Znth 1 (Znth max_i words_compact 0) words_compact)).
  assert (Hlen : Zlength sw = Zlength words_compact).
  { subst sw. rewrite !Zlength_replace_Znth. reflexivity. }
  sep_apply (IntArray.full_to_seg lits (Zlength words_compact) sw).
  sep_apply (Veci.rep_ptr_intro learnt_pre lits sw cap
    (Zlength words_compact) (Zlength words_compact) (Zlength words_compact)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  Exists sw.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | lia] ..]).
Qed.



Lemma proof_of_solver_analyze_entail_wit_36_1 : solver_analyze_entail_wit_36_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_max_loop_inv anz_n Mclear words_compact i max_i max ) as H_analyze_max_loop_inv.
  bind_fact ( Forall (lit_wf_c anz_n) words_compact ) as H_Forall.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert anz_n anz_F Mclear words_compact ) as H_analyze_clause_cert.
  assert (Hi : i = Zlength words_compact) by lia.
  assert (Hj : 1 <= max_i < Zlength words_compact) by lia.
  subst words_sw.
  set (sw := replace_Znth max_i (Znth 1 words_compact 0)
    (replace_Znth 1 (Znth max_i words_compact 0) words_compact)).
  assert (Hperm : Permutation sw words_compact).
  { subst sw. apply swap_Znth_one_perm. exact Hj. }
  assert (Hlen : Zlength sw = Zlength words_compact).
  { apply Zlength_perm_eq. exact Hperm. }
  assert (Hwf : Forall (lit_wf_c anz_n) sw).
  { eapply Permutation_Forall; [|exact H_Forall].
    apply Permutation_sym. exact Hperm. }
  assert (Hhead : Znth 0 sw 0 = Znth 0 words_compact 0).
  { subst sw. apply swap_Znth_one_head__analyze. exact Hj. }
  assert (Hcert : analyze_clause_cert anz_n anz_F Mclear sw).
  { eapply analyze_clause_cert_perm_head__analyze;
      eauto; unfold analyze_max_loop_inv in H_analyze_max_loop_inv; lia. }
  assert (Hnodup : NoDup (map lit_var_c sw)).
  { pose proof Hcert as Hcert_copy.
    unfold analyze_clause_cert, uip_exit_cert in Hcert_copy.
    destruct Hcert_copy as [[_ [Hnd _]] _].
    rewrite map_literal_var_lits_denote in Hnd. exact Hnd. }
  assert (Hwftrail : mtrail_wf anz_n (ms_core Mclear)).
  { eapply analysis_cancel_ready_trail_wf__analyze; eauto. }
  assert (Hlenle : Zlength sw <= anz_n).
  { pose proof (msat_map_lit_var_c_in_range anz_n sw Hwf) as Hall.
    pose proof (NoDup_Z_bounded_length _ anz_n (mtw_n_nonneg Hwftrail)
      Hnodup Hall) as Hle.
    rewrite length_map in Hle. rewrite Zlength_correct. exact Hle. }
  assert (Hback : analyze_backjump_cert anz_n Mclear sw
    (Z.max (ms_root_level Mclear) max)).
  { subst sw. exact (analyze_backjump_swap_complete__analyze
      anz_n anz_F anz_A_arr K Mclear anz_focus words_compact i max_i max
      Hi H_analysis_cancel_ready H_analyze_max_loop_inv H_analyze_clause_cert). }
  sep_apply (Veci.rep_ptr_rep learnt_pre lits sw).
  Exists (Z.max (ms_root_level Mclear) max) sw Mclear.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_analyze_entail_wit_36_2 : solver_analyze_entail_wit_36_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_clause_cert anz_n anz_F Mclear words_compact ) as H_analyze_clause_cert.
  assert (Hlen : Zlength words_compact = 1) by lia.
  pose proof (analyze_backjump_singleton__analyze
    anz_n anz_F Mclear words_compact Hlen H_analyze_clause_cert) as [Hnodup Hback].
  sep_apply (Veci.rep_ptr_rep learnt_pre lits words_compact).
  Exists (ms_root_level Mclear) words_compact Mclear.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_analyze_partial_solve_wit_196_pure : solver_analyze_partial_solve_wit_196_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as Hready.
  bind_fact ( ms_tags Mclear = repeat_Z 0 anz_n ) as Htags.
  pose proof (analysis_cancel_ready_size__lit_removable _ _ _ _ _ _ Hready) as Hsize.
  unfold solver_reason_levels_frame_at, solver_removable_frame_at, stats_rep.
  Intros act asg opos.
  prop_apply_p (DoubleArray.seg_Zlength act 0 (ms_size Mclear) (ms_activity Mclear)).
  Intros_p Hact.
  apply derivable1s_coq_prop_r.
  eapply analysis_cancel_ready_shape__lit_removable; [exact Hready | | lia | | assumption].
  - destruct Hready as (Mb & _ & _ & Hheap & _).
    unfold heap_wf, msolver_heap in Hheap; cbn in Hheap. rewrite <- Hsize. tauto.
  - rewrite Htags. unfold repeat_Z. rewrite Zlength_correct, List.repeat_length.
    pose proof (Zlength_nonneg (ms_activity Mclear)). lia.
Qed.


