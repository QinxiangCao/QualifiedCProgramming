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
Lemma proof_of_solver_analyze_partial_solve_wit_45_learnt_pure : solver_analyze_partial_solve_wit_45_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_72_learnt_pure : solver_analyze_partial_solve_wit_72_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 1.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_90_learnt_pure : solver_analyze_partial_solve_wit_90_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_clause_word_int_range_via_wf j clause_words2 Hlit.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_100_learnt_pure : solver_analyze_partial_solve_wit_100_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_108_learnt_pure : solver_analyze_partial_solve_wit_108_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_110_learnt_pure : solver_analyze_partial_solve_wit_110_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  subst Mact.
  subst j.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mscan Mscan anz_focus phase Ccur 0 ind S0 R2 learnt0 x
    Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  prop_apply_p (DoubleArray.seg_Zlength activity_ptr_scan 0 anz_n
    (ms_activity Mscan)).
  Intros.
  assert (Hheap : order_heap_wf anz_n (ms_order Mscan) (ms_orderpos Mscan)).
  { unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
    destruct H_analyze_clause_scan_inv as [Hready _].
    unfold analysis_cancel_ready in Hready.
    destruct Hready as [Mready [_ [_ [Hheap _]]]].
    exact Hheap. }
  split_pures; dump_pre_spatial; auto; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_148_pure : solver_analyze_partial_solve_wit_148_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mresolution anz_focus ) as H_analysis_cancel_ready.
 split_pures;
  dump_pre_spatial;
  try lia;
  (try (destruct H_analysis_cancel_ready as [Mbase [Hcancel [Hequiv _]]];
       destruct Hcancel as [Hweak _]; destruct Hweak as [_ Hinv];
       unfold analysis_core_equiv in Hequiv;
       destruct Hequiv as [HsizeEq _];
       destruct K as [A_inst | A_proc]; cbn in Hinv;
       [ pose proof (msw_size Hinv) as Hsize
       | pose proof (msa_size Hinv) as Hsize ]; lia)).
Qed.


Lemma proof_of_solver_analyze_safety_wit_39_learnt : solver_analyze_safety_wit_39_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial. msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_15 : solver_analyze_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  bind_fact ( q = Znth (j - 0) clause_words2 0 ) as H_q.
  rewrite Z.sub_0_r in H_q.
  pose proof (Forall_Znth_elim Z (lit_wf_c anz_n) clause_words2 0 j
    H_Forall ltac:(lia)) as Hwf.
  rewrite <- H_q in Hwf.
  pose proof (lit_var_c_in_range anz_n q Hwf) as Hrange.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; rewrite ?Z.sub_0_r; solve [auto | lia].
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_16 : solver_analyze_which_implies_wit_16.
Proof.
  LLM_pre_process ltac:(lia).
    bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R2 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= lit_var_c q ) as H_lit_var_c.
  bind_fact ( lit_var_c q < anz_n ) as H_lit_var_c_2.
  pose proof H_analyze_clause_scan_inv as Hinv.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as [Hready Hrest].
  destruct Hrest as (Hcore & Hind & Hroot & Hwf & Hj & Hjbound & Hcnt & Hwords_bound &
      Hlearnt & Htags & Hperm & Hphase).
  unfold analysis_tags_exact in Htags.
  destruct Htags as [Htags_len [Hnodup [Hrange [Hbits Hexact]]]].
  assert (Hnotin : ~ In (lit_var_c q) (ms_tagged Mscan)).
  { intro Hin.
    pose proof (proj2 (Hexact (lit_var_c q) (conj H_lit_var_c H_lit_var_c_2)) Hin) as Hone.
    lia. }
  assert (Hcons_nodup : NoDup (lit_var_c q :: ms_tagged Mscan)).
  { constructor; assumption. }
  pose proof (msat_cons_list_var_bounded anz_n (lit_var_c q) (ms_tagged Mscan)
    (conj H_lit_var_c H_lit_var_c_2) Hrange) as Hbounded.
  assert (Htagged : Zlength (ms_tagged Mscan) < anz_n).
  { pose proof (NoDup_Z_bounded_length
      (lit_var_c q :: ms_tagged Mscan) anz_n ltac:(lia) Hcons_nodup Hbounded)
      as Hlen.
    rewrite Zlength_correct. simpl in Hlen. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_11 : solver_lit_removable_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hstep : removable_rollback_inv lrm_n top (j + 1) (ms_tagged M0)
    (ms_tags M0) tags_scan tagged_scan
    (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2)).
  { eapply removable_rollback_step__lit_removable; eauto. }
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "tagged") tagged tagged_scan cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_full tags_ptr
      (Znth j tagged_scan 0) lrm_n 0 tags_rollback_2).
  { dump_pre_spatial. lia. }
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2)).
  destruct (Z_lt_ge_dec (j + 1) (Zlength tagged_scan)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth (j + 1) tagged_scan 0 < lrm_n).
    { assert (Hexact : analysis_tags_exact lrm_n tags_scan tagged_scan).
      { unfold removable_rollback_inv in Hstep. tauto. }
      unfold analysis_tags_exact in Hexact.
      destruct Hexact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2).
    msat_manual_entailer_with ltac:(lia).
  - assert (Hjle : j + 1 <= Zlength tagged_scan).
    { unfold removable_rollback_inv in Hstep. tauto. }
    assert (Hjeq : j + 1 = Zlength tagged_scan) by lia.
    Right. Exists (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2).
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_13_3 : solver_lit_removable_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth retval_7 (mt_levels (ms_core M0)) 0 = 0 ) as H_Znth.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (Znth (Znth (Zlength
    stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) = msat_true ) as
    H_is_tag.
  bind_fact ( removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now_2 tagged_now_2 stack_now_2 done_2
    ) as H_removable_dfs_loop_inv.
  bind_fact ( stack_after = sublist 0 (Zlength stack_now_2 - 1) stack_now_2 ) as H_stack_after.
  bind_fact ( stack_now_2 = stack_after +:: Znth (Zlength stack_now_2 - 1) stack_now_2 0 ) as H_stack_now_2.
  bind_fact ( retval_4 = Zlength stack_now_2 ) as H_retval_4.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( incl stack_now_2 (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  all: (set (v := Znth (Zlength stack_now_2 - 1) stack_now_2 0) in *);
    (assert (Hperm : Permutation stack_now_2 (v :: stack_after)) by (
    rewrite H_stack_now_2;
    apply list_snoc_permutation));
    (assert (Hloop_top :
    removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0)
      tags_now_2 tagged_now_2 (v :: stack_after) done_2) by
    (eapply removable_dfs_loop_inv_stack_perm__lit_removable;
    [exact Hperm | exact H_removable_dfs_loop_inv])).
  all: (try subst retval_6);
    (try subst retval_7);
    (try unfold msat_true in H_is_tag).
  all: (assert (Hr : reason_of (msolver_view lrm_n M0) v = Some Cnext) by
    (eapply removable_reason_focus_view__lit_removable;
    [exact H_analysis_cancel_ready | exact H_removable_reason_focus]));
    (assert (Hside : forall q, In q Cnext -> literal_var q <> v ->
    level_of (msolver_view lrm_n M0) (literal_var q) = Some 0 \/
    In (literal_var q) (ms_tagged M0) \/
    In (literal_var q) (v :: done_2) \/ In (literal_var q) stack_after) by
    (intros q Hq Hneq; left;
    eapply tagged_reason_side_level_word_zero__lit_removable;
    [exact H_analysis_cancel_ready | exact H_removable_reason_focus | exact H_is_tag | reflexivity |
     exact H_Znth | exact Hq | exact Hneq])).
  all: (assert (Hloop_done :
    removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0)
      tags_now_2 tagged_now_2 stack_after (v :: done_2)) by
    (eapply removable_dfs_loop_inv_finish_head__lit_removable;
    [exact Hloop_top | exact Hr | exact Hside]));
    (assert (Hstack_incl :
    incl stack_after (map lit_var_c (mt_trail (ms_core M0)))) by
    (intros x Hx; apply H_incl; rewrite H_stack_now_2;
     apply in_or_app; left; exact Hx)).
  - pose proof (Zlength_nonneg stack_after) as Hstack_after_nonneg.
    rewrite H_retval_4, <- H_stack_after.
    Exists (v :: done_2) stack_after tags_now_2 tagged_now_2.
    sep_apply (Veci.rep_ptr_rep &(s_pre # "solver_t" ->ₛ "stack") p stack_after).
    msat_restore_array_read PtrArray.missing_i_merge_to_seg
      reasons_ptr (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n (ms_reason_words M0).
    msat_restore_array_read IntArray.missing_i_merge_to_seg
      levels_ptr (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n (mt_levels (ms_core M0)).
    msat_restore_array_read CharArray.missing_i_merge_to_seg
      tags_ptr (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n tags_now_2.
    all: msat_manual_entailer_with lia.
Qed.



Lemma proof_of_solver_lit_removable_partial_solve_wit_32_pure : solver_lit_removable_partial_solve_wit_32_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval = lit_var_c retval_7 ) as H_retval.
  bind_fact ( retval_7 = tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) ) as
      H_retval_7.
  bind_fact ( 0 <= lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) ) as
      H_lit_var_c.
  bind_fact ( lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) < lrm_n )
      as H_lit_var_c_2.
  assert (Hretval_nonneg : 0 <= retval).
  { rewrite H_retval, H_retval_7. exact H_lit_var_c. }
  assert (Hretval_bound : retval < lrm_n).
  { rewrite H_retval, H_retval_7. exact H_lit_var_c_2. }
  msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_55_pure : solver_lit_removable_partial_solve_wit_55_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures; dump_pre_spatial;
    replace (retval - 0) with retval in * by lia;
    assumption.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_6_split_goal_spatial : solver_lit_removable_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold removable_reason_array_hole, StorePtrAsElement.storeA.
  prop_apply_p
    (ptrarray_missing_i_index_range__lit_removable
      reasons_ptr v 0 lrm_n (ms_reason_words M0)).
  Intros_p Hrange. destruct Hrange as [Hv0 Hvn].
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_seg reasons_ptr 0 v lrm_n
      (Znth v (ms_reason_words M0) 0) (ms_reason_words M0)).
  - dump_pre_spatial. lia.
  - replace (v - 0) with v by lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_6 : solver_lit_removable_which_implies_wit_6.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_lit_removable_which_implies_wit_6_split_goal_spatial M0 lrm_n reasons_ptr v PreH1).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_10_split_goal_1 : solver_lit_removable_which_implies_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (v - 0) with v by lia; msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_10 : solver_lit_removable_which_implies_wit_10.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_lit_removable_which_implies_wit_10_split_goal_1 M0 lrm_n v PreH1 PreH2).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_14 : solver_lit_removable_which_implies_wit_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_focus lrm_n M0 v c Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  pose proof H_removable_reason_focus as Hfocus.
  unfold removable_reason_focus, reason_target_wf in H_removable_reason_focus.
  destruct H_removable_reason_focus as [Hv [Hp [Hnonzero [Hreason [Htagged | Hreal]]]]].
  - destruct Htagged as [Htag _]. unfold msat_false in H_is_tag. congruence.
  - destruct Hreal as [co [Htag [Hnotbinary [Hin HC]]]].
    destruct
      (analysis_cancel_ready_db_binary__lit_removable
        lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Hdb Hbinary_out].
    pose proof (db_wf_obj lrm_n (msolver_db M0) c co Hdb Hin) as Hobj.
    destruct Hobj as [Hobj_len [Hwords Hnodup]].
    pose proof
      (clause_hdr_word_div2 (co_learnt co) (Zlength (co_lits co))
        (Zlength_nonneg (co_lits co))) as Hhdr.
    pose proof
      (clause_hdr_word_nonneg (co_learnt co) (Zlength (co_lits co))
        (Zlength_nonneg (co_lits co))) as Hhdr_nonneg.
    assert (Hhdrq :
      clause_hdr_word (co_learnt co) (Zlength (co_lits co)) ÷ 2 =
      Zlength (co_lits co)).
    { rewrite Z.quot_div_nonneg by lia. exact Hhdr. }
    unfold denote_obj in HC.
    sep_apply
      (clause_db_pair_focus_from_member__lit_removable
        (ms_prob M0) (ms_learnt M0) c co Hin).
    unfold MiniSatClause.rep at 1.
    Exists (co_learnt co) (co_lits co).
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_3_learnt : solver_analyze_entail_wit_12_3_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mact)) ) as H_retval_11.
  bind_fact ( retval_9 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( forall u_2 : Z, 0 <= u_2 < anz_n -> Znth u_2 orderpos1 (-1) = -1 -> Znth u_2 (ms_orderpos Mscan_2) (-1)
      = -1 ) as H_u_2.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv_2.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hreason & HSold & ERscan & HLold).
  msat_analyze_tag_step_open v Mnext j clause_words2 activity1
    orderpos1 heap1 var_inc1 Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hpermold).
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
  assert (Eqcv : lit_var_c q = v).
  { rewrite <- lit_var_c_denote. exact Eqv. }
  rewrite Eqv in Hlevq, Hrankq.
  assert (Hdqcur : dq = Zlength (mt_lim (ms_core Mscan_2))).
  { rewrite <- H_Mscan_2 in Hlevq, Hrankq.
    unfold msolver_view, view_of in Hlevq, Hrankq.
    cbn [level_of assignment_rank] in Hlevq, Hrankq.
    rewrite Hrankq in Hlevq. cbn in Hlevq. injection Hlevq as Edq.
    pose proof (trail_pos_bound (ms_core Mscan_2) v rq Hrankq) as Hrqb.
    pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
    rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrankq) in Hagree.
    fold v in H_retval_10. rewrite H_retval_10, H_retval_11 in H_Znth.
    rewrite Edq in Hagree.
    replace (v - 0) with v in H_Znth by lia.
    rewrite H_Mscan_2.
    lia. }
  assert (Hat : at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true).
  { apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite Eqv, Hlevq.
    rewrite msolver_view_current_level, <- H_Mscan_2, Hdqcur. reflexivity. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { unfold below_current_b. rewrite Eqv, Hlevq.
    rewrite msolver_view_current_level, <- H_Mscan_2, Hdqcur.
    rewrite Z.ltb_irrefl, Bool.andb_false_r. reflexivity. }
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HSnext : Sscan_2 ++ (v :: nil) =
      resolve_S (msolver_view anz_n Mact) x_2 (sublist 1 (j + 1) Ccur)
        S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map]. rewrite Hat.
    replace (map literal_var (lit_denote q :: nil)) with (v :: nil)
      by (cbn [map]; rewrite Eqv; reflexivity).
    cbn [filter]. rewrite Hnotmem. cbn [negb].
    rewrite HSold. rewrite !app_assoc. reflexivity. }
  assert (HLnext : learnt_scan_2 =
      resolve_learnt (msolver_view anz_n Mact) (sublist 1 (j + 1) Ccur)
        S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter]. rewrite Hbelow. cbn [filter andb].
    rewrite app_nil_r. exact HLold. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext
      anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  msat_analyze_tag_step_carry Mnext Mact M0 H_analysis_core_equiv
    H_analysis_core_equiv_2 H_msolver_seed_shadow.
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ (v :: nil)) Rscan_2
    learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - msat_analyze_tag_step_frame Mnext Mscan_2 v activity1 orderpos1
      heap1 var_inc1 c is_learnt2 clause_words2.
    msat_cancel_sound.
    fold v in H_retval_7, H_retval_6.
    rewrite H_retval_7, H_retval_6.
    sep_apply CharArray.full_to_seg.
    rewrite H_Mscan_2.
    msat_cancel_sound; cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_13_learnt : solver_analyze_entail_wit_12_13_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  unfold solver_analyze_open_at in *. msat_analyze_scan_stop orderpos_ptr_scan_2 activity_ptr_scan_2 S0_2 R0_2
    learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 Mscan_2 phase j Ccur clause_words2 anz_n K Mact.
Qed.


Lemma proof_of_solver_analyze_entail_wit_13_4_learnt : solver_analyze_entail_wit_13_4_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_core_equiv Mact Mscan_4 ) as H_analysis_core_equiv.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_4 anz_focus phase Ccur j ind S0_4 R0_4 learnt0_4 x_4
      Sscan_4 Rscan_4 learnt_scan_4 words_scan_4 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  Exists activity_ptr_scan orderpos_ptr_scan
    words_scan_4 Sscan_4 Rscan_4 learnt_scan_4 Mscan_4.
  split_pure_spatial.
  - cancel (clause_hdr_addr c # Int |-> clause_hdr_word is_learnt2 (Zlength clause_words2)).
    cancel.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    (* The two goals number the
       anonymous hypotheses differently, which is exactly why the rest of this
       proof reads the destructuring pattern below and never an `H<k>`. *)
    all: (unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv);
      (subst phase);
      (cbn in H_analyze_clause_scan_inv);
      (destruct H_analyze_clause_scan_inv as
           (Hready & Hcore & (Hindlo & Hindhi) & Hrootlim & Hlitwf & Hnodup &
            (Hjlo & Hjhi) & Hcnt & (Hwordslo & Hwordshi) & Hwordsden & Htagsexact
            & Htagsperm & Hcntpos & Hjone & HxinS0 & Hxrank & Hrankothers & Hinv0
            & Hreason & Hreasonvalid & Hentails & HSscan & HRscan & Hlearntscan)).
    all: (destruct (msat_analysis_ready_scan_facts anz_n anz_F anz_A_arr K
           Mscan_4 anz_focus Hready)
           as (Hwf & Hstable & Htrailimpl & Hqtail & Hlevel0));
      (assert (Hindex : 0 <= ind < Zlength (mt_trail (ms_core Mscan_4))) by lia);
      (pose proof (msat_trail_lit_var_range anz_n Mscan_4 ind Hwf Hindex)
           as Hvarrange);
      (try (match goal with |- context [?idx - 0] =>
                replace (idx - 0) with idx by lia end));
      (try lia).
    1: {
    destruct (msat_analysis_equiv_transport anz_n Mact Mscan_4
      H_analysis_core_equiv) as (Ecore & Ereason & Hview).
    assert (Hxrange : 0 <= x_4 < anz_n).
    { apply (msat_trail_pos_var_range anz_n Mscan_4 x_4 (ind + 1) Hwf ltac:(lia)).
      rewrite Ecore. exact Hxrank. }
    assert (Hheadvar : literal_var (Znth 0 Ccur (Pos 0)) = x_4).
    { apply (msat_analysis_reason_head_var anz_n anz_F anz_A_arr K Mscan_4
        anz_focus x_4 Ccur Hready Hxrange).
      rewrite Ereason. exact Hreason. }
    assert (Hnewinv : analyze_inv anz_F (msolver_view anz_n Mscan_4)
      (resolve_S (msolver_view anz_n Mscan_4) x_4 Ccur S0_4 R0_4 learnt0_4)
      (x_4 :: R0_4)
      (resolve_learnt (msolver_view anz_n Mscan_4) Ccur S0_4 R0_4 learnt0_4)).
    { eapply analyze_resolve_step.
      - exact (proj2 Hstable).
      - exact Hlevel0.
      - rewrite <- Hview. exact Hinv0.
      - exact HxinS0.
      - rewrite <- Hview.
        cbn [msolver_view view_of reason_of]. rewrite Hxrank. exact Hreason.
      - rewrite <- Hview. exact Hreasonvalid.
      - exact Hentails.
      - exact Hnodup.
      - intros s Hs Hsx. rewrite <- Hview. apply Hrankothers; assumption. }
    assert (Hjfull : j = Zlength Ccur) by
      (rewrite H_Ccur, lits_denote_length; lia).
    destruct (msat_clause_head_tail Ccur j ltac:(lia) Hjfull)
      as (HCcons & Hscanpart).
    destruct (msat_resolve_head_drop (msolver_view anz_n Mscan_4) x_4 Ccur
      S0_4 R0_4 learnt0_4 HCcons Hheadvar HxinS0) as (HresolveS & HresolveL).
    rewrite Hscanpart, Hview in HSscan, Hlearntscan.
    rewrite <- HresolveS in HSscan. rewrite <- HresolveL in Hlearntscan.
    assert (Hinvscan : analyze_inv anz_F (msolver_view anz_n Mscan_4)
      Sscan_4 Rscan_4 learnt_scan_4).
    { rewrite HSscan, HRscan, Hlearntscan. exact Hnewinv. }
    assert (Hrankx : assignment_rank (msolver_view anz_n Mscan_4) x_4 =
        Some (Z.to_nat (ind + 1))) by (rewrite <- Hview; exact Hxrank).
    destruct (msat_analyze_scan_rank_split anz_F (msolver_view anz_n Mscan_4)
      S0_4 R0_4 learnt0_4 Sscan_4 Rscan_4 learnt_scan_4 x_4 ind ltac:(lia) Hinvscan
      ltac:(rewrite <- Hview; exact Hinv0) HRscan HxinS0 Hrankx)
      as (Hpending & Hresolved).
    assert (HexS : exists y, In y Sscan_4) by
      (destruct Sscan_4 as [|y ys]; [cbn in Hcnt; lia|exists y; left; reflexivity]).
    destruct HexS as [y Hy]. destruct (Hpending y Hy) as [r [Hyr Hri]].
    unfold analyze_backward_scan_inv.
    split; [exact Hready|]. split; [exact Hinvscan|]. split; [exact Hcnt|].
    split; [exact Hcntpos|]. split; [exact (conj Hindlo Hindhi)|].
    split; [exact (conj Hwordslo Hwordshi)|]. split; [exact Hrootlim|]. split; [exact Hwordsden|].
    split; [exact Htagsexact|]. split; [exact Htagsperm|]. split; [exact Hpending|].
    split; [exact Hresolved|]. exists y, r. split; [ | split ]; assumption. }
    intros Htag0.
    destruct (Z.eq_dec ind 0) as [Hzeroind|Hzeroind]; [subst ind|lia].
    destruct (msat_analysis_equiv_transport anz_n Mact Mscan_4 H_analysis_core_equiv)
      as (_ & _ & Hview0).
    assert (Hjfull0 : j = Zlength Ccur) by
      (rewrite H_Ccur, lits_denote_length; lia).
    destruct (msat_clause_head_tail Ccur j ltac:(lia) Hjfull0)
      as (HCcons0 & Hscanpart0).
    rewrite Hview0, Hscanpart0 in HSscan.
    assert (Htagx0 : zmem x_4 (analyze_tags S0_4 R0_4 learnt0_4) = true).
    { apply zmem_true_iff. unfold analyze_tags.
      apply in_or_app. left. exact HxinS0. }
    assert (HexS0 : exists y, In y Sscan_4) by
      (destruct Sscan_4 as [|y ys]; [cbn in Hcnt; lia|exists y; left; reflexivity]).
    destruct HexS0 as [y Hy].
    assert (Hrankyx : rank_lt (msolver_view anz_n Mscan_4) y x_4).
    { rewrite HSscan in Hy. unfold resolve_S in Hy.
      apply in_app_or in Hy. destruct Hy as [Hy|Hy].
      - apply In_zremove_iff in Hy. destruct Hy as [HyS Hyx].
        rewrite <- Hview0. apply Hrankothers; assumption.
      - unfold resolve_new_S in Hy. apply filter_In in Hy.
        destruct Hy as [Hymap Hyfresh]. apply negb_true_iff in Hyfresh.
        rewrite in_map_iff in Hymap.
        destruct Hymap as [m [Hmy Hmfilter]].
        apply filter_In in Hmfilter. destruct Hmfilter as [Hm _].
        assert (Hmyx : y <> x_4).
        { intro Heq. rewrite Heq, Htagx0 in Hyfresh. discriminate. }
        assert (Hmx : literal_var m <> x_4) by congruence.
        assert (HmC : In m Ccur).
        { rewrite HCcons0. right. exact Hm. }
        pose proof Hreasonvalid as Hrv.
        destruct Hrv as [b [d [rx [Hass [Hlev [Hrank [Hin Hothers]]]]]]].
        destruct (Hothers m HmC Hmx) as
          [_ [dy [ry [Hmlev [Hmrank [Hdy Hry]]]]]].
        rewrite <- Hview0. unfold rank_lt.
        exists ry, rx. split; [ rewrite <- Hmy; exact Hmrank | split; assumption ]. }
    assert (Hrankx0 : assignment_rank (msolver_view anz_n Mscan_4) x_4 = Some (1%nat)).
    { rewrite <- Hview0. cbn in Hxrank. exact Hxrank. }
    destruct Hrankyx as [ry [rx [Hranky [Hrankx Hlt]]]].
    rewrite Hrankx0 in Hrankx. injection Hrankx as <-.
    assert (ry = 0)%nat by lia. subst ry.
    cbn [msolver_view view_of assignment_rank] in Hranky.
    pose proof (trail_pos_var _ _ _ Hranky) as Hyvar.
    change (lit_var_c (Znth 0 (mt_trail (ms_core Mscan_4)) 0) = y) in Hyvar.
    assert (Hyv0 : y = lit_var_c
      (Znth 0 (mt_trail (ms_core Mscan_4)) 0)) by congruence.
    assert (HyAnalyze : In y (analyze_tags Sscan_4 Rscan_4 learnt_scan_4)).
    { unfold analyze_tags. apply in_or_app. left. exact Hy. }
    assert (HyTagged : In y (ms_tagged Mscan_4)).
    { eapply Permutation_in; [apply Permutation_sym; exact Htagsperm|exact HyAnalyze]. }
    destruct Htagsexact as [_ [_ [_ [_ Htagiff]]]].
    assert (Hyrange : 0 <= y < anz_n).
    { rewrite Hyv0. exact Hvarrange. }
    pose proof (proj2 (Htagiff y Hyrange) HyTagged) as Htagone.
    replace (0 - 0) with 0 in Htag0 by lia.
    rewrite Hyv0 in Htagone. congruence.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_5_pure : solver_analyze_partial_solve_wit_5_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (analysis_cancel_ready_reason_core _ _ _ _ _ _ (proj1 PreH4)) as Hsize. msat_manual_entailer_with ltac:(intuition lia).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_9_pure : solver_analyze_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  bind_fact ( reason_target_wf anz_n Mcur_2 x c Ccur_2 ) as H_reason_target_wf.
  bind_fact ( is_tag c = msat_true ) as H_is_tag.
  unfold reason_target_wf in H_reason_target_wf.
  destruct H_reason_target_wf as [_ [_ [_ [_ Hshape]]]].
  destruct Hshape as [[_ [Hcpos Hlit]] | [co [Hnot_tag _]]].
  - unfold lit_wf_c in Hlit.
    (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]); lia.
  - rewrite H_is_tag in Hnot_tag; discriminate.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_27_pure : solver_analyze_partial_solve_wit_27_pure.
Proof.
  LLM_pre_process ltac:(lia). split_pures; msat_analyze_cancel_heap_tail.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_60_learnt_pure : solver_analyze_partial_solve_wit_60_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 1.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_61_learnt_pure : solver_analyze_partial_solve_wit_61_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 1.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_101_learnt_pure : solver_analyze_partial_solve_wit_101_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_clause_word_int_range_via_wf j clause_words2 Hlit.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_116_learnt_pure : solver_analyze_partial_solve_wit_116_learnt_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  subst j.
  pose proof (Forall_Znth_elim _ _ _ 0 (1 - 0) PreH24 ltac:(lia)) as Hlit.
  unfold lit_wf_c in Hlit.
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_136_pure : solver_analyze_partial_solve_wit_136_pure.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | Hscan : analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus
      words_resolved cnt ind Sresolved Rresolved learnt_resolved |- _ =>
      unfold analyze_backward_scan_inv in Hscan;
      destruct Hscan as [Hready _]
  end.
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mbase [Hprop [Hequiv _]]].
  unfold propagation_cancel_ready in Hprop.
  destruct Hprop as [Hweak _].
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as [_ Hweak].
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as [_ [_ [Eqtail [Ecore _]]]].
  assert (Hfacts :
    mtrail_wf anz_n (ms_core Mresolved) /\
    Zlength (mt_trail (ms_core Mresolved)) = ms_qtail Mresolved /\
    2 * anz_n <= INT_MAX).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - pose proof (msw_trail_wf Hweak) as Htrail.
      pose proof (msw_shape Hweak) as Hshape.
      pose proof (msw_size Hweak) as Hsize.
      unfold solver_shape in Hshape.
      destruct Hshape as
        [_ [_ [Htwo [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]]]]].
      split.
      + rewrite Ecore. exact Htrail.
      + split.
        * rewrite Ecore, Eqtail. exact Hlen.
        * rewrite Hsize. exact Htwo.
    - pose proof (msa_trail_wf Hweak) as Htrail.
      pose proof (msa_shape Hweak) as Hshape.
      pose proof (msa_size Hweak) as Hsize.
      unfold solver_shape in Hshape.
      destruct Hshape as
        [_ [_ [Htwo [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]]]]].
      split.
      + rewrite Ecore. exact Htrail.
      + split.
        * rewrite Ecore, Eqtail. exact Hlen.
        * rewrite Hsize. exact Htwo. }
  destruct Hfacts as [Htrail [Hlen Htwo]].
  assert (Hi : 0 <= ind < Zlength (mt_trail (ms_core Mresolved))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 ind (mtw_trail_lits Htrail) Hi)
    as Hlit.
  unfold lit_wf_c in Hlit.
  split_pures; dump_pre_spatial;
    replace (ind - 0) with ind by lia; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_158_pure : solver_analyze_partial_solve_wit_158_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  msat_analyze_close_learnt_vec_lit_range Hf.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_174_pure : solver_analyze_partial_solve_wit_174_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures.
  all: (try (dump_pre_spatial; lia));
    (try (dump_pre_spatial;
      lazymatch goal with
      | H : ?fact |- ?fact => exact H
      end));
    (try (dump_pre_spatial;
      lazymatch goal with
      | H : Znth ?index ?words ?default < ?bound |-
        Znth (?index - 0) ?words ?default < ?bound =>
          replace (index - 0) with index by lia; exact H
      end)).
  all: try (dump_pre_spatial;
      lazymatch goal with
      | H : 0 <= Znth ?index ?words ?default |-
        0 <= Znth (?index - 0) ?words ?default =>
          replace (index - 0) with index by lia; exact H
      end).
Qed.



Lemma proof_of_solver_analyze_which_implies_wit_21 : solver_analyze_which_implies_wit_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hr : 0 <= 0 < Zlength words_before) by lia.
  pose proof (IntArray.missing_i_merge_to_seg learnt_ptr_uip 0 0
    (Zlength words_before) (lit_neg_c p) words_before Hr) as Hmerge.
  generalize Hmerge.
  clear Hmerge.
  replace (learnt_ptr_uip + 0 * sizeof(INT)) with learnt_ptr_uip by lia.
  intros Hmerge.
  sep_apply Hmerge.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_28 : solver_analyze_which_implies_wit_28.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (analysis_cancel_ready
    anz_n anz_F anz_A_arr K Mstats anz_focus) as Hready.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mstats anz_focus Hready) as [Hsize _].
  subst anz_n.
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_tags_tagged_frame_at,
    solver_removable_frame_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_vecs_rep, solver_ptrs_rep, solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply peel_scalars_size.
  sep_apply (Veci.rep_rep_ptr
    (&(s # "solver_t" ->ₛ "tagged")) (ms_tagged Mstats)).
  Intros tagged_ptr.
  Exists tagged_ptr act asg opos.
  pose proof (Zlength_nonneg (ms_tagged Mstats)).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_5_split_goal_spatial : solver_lit_removable_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_5_split_goal_1 : solver_lit_removable_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (v - 0) with v by lia.
  reflexivity.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_5 : solver_lit_removable_which_implies_wit_5.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_lit_removable_which_implies_wit_5_split_goal_spatial M0 lrm_n reasons_ptr v PreH1 PreH2).
- Goal_apply (proof_of_solver_lit_removable_which_implies_wit_5_split_goal_1 M0 lrm_n reasons_ptr v PreH1 PreH2).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_19 : solver_lit_removable_which_implies_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lits_refold.
  bind_fact ( c_refold % 2 = 0 ) as H_c_refold.
  unfold MiniSatClause.rep.
  pose proof (Zlength_nonneg clause_words).
  assert (Hmod : c_refold mod 2 = 0).
  { apply Z.mod_divide; [lia |].
    apply Z.rem_divide; [lia | exact H_c_refold]. }
  msat_manual_entailer_with ltac:(lia).
Qed.


