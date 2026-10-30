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
Lemma proof_of_solver_analyze_entail_wit_7_2 : solver_analyze_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  bind_fact ( Znth retval_5 (ms_tags Mcur) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_5 = lit_var_c (tag_lit c) ) as H_retval_5.
  msat_analyze_e7_semantic_facts anz_n anz_F anz_A_arr K Mcur
    anz_focus c x Ccur phase_2 words_2 cnt ind p S0 R2 learnt0.
  bind_fact ( 0 < cnt ) as H_cnt_2.
  pose proof H_loop_inv as Hloop.
  rewrite H_phase in Hloop.
  destruct (msat_analyze_e7_ready_semantics
    anz_n anz_F anz_A_arr K Mcur anz_focus H_cancel_ready)
    as (Htrailwf & Hstable & Htrailimpl & Hrootunit).
  destruct (msat_analyze_e7_select_bridge
    anz_n anz_F anz_A_arr K Mcur anz_focus c ind cnt p x Ccur
    words_2 S0 R2 learnt0 Hloop H_reason_target H_is_tag H_x_in_S0 H_cnt_len
    H_analyze_inv H_tagged_perm H_shape Htrailwf Hstable
    Hrootunit) as
    (HCshapeX & Horder0 & Hrank_sel & HvalidA & HentA & HCndA & HinvNew &
     HpendS & HresolvedRanks & Htags & Hind & Hwords & Hroot &
     Hindvarrange & HrangeXn & Hqneq).
  destruct (msat_analyze_e7_resolve_sets
    anz_n Mcur c x Ccur S0 R2 learnt0 HCshapeX (proj1 HrangeXn)
    H_x_level H_tag_level H_x_in_S0) as (HresolveL & _ & HresolveKeep).
  destruct (msat_analyze_e7_pending_split
    anz_n anz_F Mcur x cnt S0 R2 learnt0 H_analyze_inv H_x_in_S0 H_cnt_len)
    as (Hlenremove & Hperm_move).
  pose proof (msat_analyze_e7_tag_already_seen
    anz_n Mcur c retval_5 S0 R2 learnt0 Htags H_tagged_perm
    H_retval_5 H_tag_lo H_tag_hi H_Znth) as Hqseen.
  assert (HresolveS :
    resolve_S (msolver_view anz_n Mcur) x Ccur S0 R2 learnt0 =
    zremove x S0).
  { exact (HresolveKeep Hqseen). }
  rewrite HresolveS, HresolveL in HinvNew.
  assert (HpermNew :
    Permutation (ms_tagged Mcur)
      (analyze_tags (zremove x S0) (x :: R2) learnt0)).
  { eapply Permutation_trans; [exact H_tagged_perm | exact Hperm_move]. }
  assert (HcoreSelf : analysis_core_equiv Mcur Mcur).
  { unfold analysis_core_equiv. repeat split; reflexivity. }
  assert (Htagged_target :
    analyze_tagged_step (ms_size Mcur) anz_F anz_A_arr K Mcur Mcur
      anz_focus (Znth x (ms_reason_words Mcur) 0)
      (tag_lit (Znth x (ms_reason_words Mcur) 0)) Ccur
      S0 R2 (lits_denote (tl words_2)) x
      (zremove x S0) (x :: R2) learnt0 words_2 cnt).
  {
    rewrite H_size, <- H_reason_word, H_learnt_eq.
    unfold analyze_tagged_step.
    refine (conj H_cancel_ready (conj HcoreSelf (conj Hroot (conj
      H_reason_target (conj H_is_tag (conj eq_refl (conj H_x_in_S0 (conj Horder0
      (conj H_analyze_inv (conj HvalidA (conj HentA (conj HCndA (conj
      H_tag_level (_)))))))))))))).
    refine (conj (eq_sym HresolveS) (conj eq_refl (conj (eq_sym HresolveL)
      (conj Hlenremove (conj Hwords (conj H_learnt_eq (conj Htags
      (HpermNew)))))))).
  }
  assert (HexPending : exists y, In y (zremove x S0)).
  {
    destruct (zremove x S0) as [|y ys] eqn:Hz.
    - cbn in Hlenremove. lia.
    - exists y. left. reflexivity.
  }
  assert (HpendingRanks :
    forall y, In y (zremove x S0) -> exists r,
      assignment_rank (msolver_view anz_n Mcur) y = Some r /\
      Z.of_nat r <= ind).
  {
    intros y Hy.
    apply In_zremove_iff in Hy. destruct Hy as (HyS & Hyx).
    exact (HpendS y HyS Hyx).
  }
  assert (Hback_target :
    analyze_backward_scan_inv (ms_size Mcur) anz_F anz_A_arr K Mcur
      anz_focus words_2 cnt ind (zremove x S0) (x :: R2) learnt0).
  {
    rewrite H_size.
    unfold analyze_backward_scan_inv.
    refine (conj H_cancel_ready (conj HinvNew (conj Hlenremove (conj
      H_cnt_2 (conj Hind (conj Hwords (conj Hroot (conj H_learnt_eq (conj
      Htags (conj HpermNew (conj HpendingRanks (conj HresolvedRanks
      (_))))))))))))).
    destruct HexPending as (y & Hy).
    destruct (HpendingRanks y Hy) as (r & Hr & Hri).
    exists y, r. repeat split; assumption.
  }
  pose proof (msat_analyze_e7_scan_index_nonzero
    anz_n Mcur Mcur ind (zremove x S0) (x :: R2) learnt0
    eq_refl Htags HpermNew HexPending HpendingRanks (proj1 Hind)) as Hzero.
  rewrite H_reason_word in H_is_tag, H_reason_target, Hloop.
  rewrite <- H_size in H_reason_target, Hloop.
  assert (Hlower_target :
    0 <= lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mcur)) 0)).
  { replace (ind - 0) with ind by lia. exact (proj1 Hindvarrange). }
  assert (Hupper_target :
    lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mcur)) 0) <
      ms_size Mcur).
  {
    replace (ind - 0) with ind by lia.
    rewrite H_size. exact (proj2 Hindvarrange).
  }
  assert (Hzero_target :
    Znth (lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mcur)) 0) - 0)
      (ms_tags Mcur) 0 = 0 -> 0 < ind).
  {
    replace (ind - 0) with ind by lia.
    replace (lit_var_c (Znth ind (mt_trail (ms_core Mcur)) 0) - 0)
      with (lit_var_c (Znth ind (mt_trail (ms_core Mcur)) 0)) by lia.
    exact Hzero.
  }
  Exists (zremove x S0) (x :: R2) learnt0 words_2
    (ms_tags Mcur) (ms_tagged Mcur)
    (ms_activity Mcur) (ms_orderpos Mcur) (ms_order Mcur) (ms_var_inc Mcur)
    Mcur.
  rewrite analyze_tag_step_msolver_id.
  rewrite H_size in Htagged_target, Hback_target, Hupper_target.
  sep_apply (CharArray.full_to_seg tags_loop anz_n (ms_tags Mcur)).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + reflexivity.
    + exact H_shape.
    + lia.
    + assumption.
    + exact HcoreSelf.
    + assumption.
    + rewrite H_learnt_eq in Htagged_target.
      rewrite H_reason_word.
      exact Htagged_target.
    + exact Hback_target.
    + exact Hlower_target.
    + exact Hupper_target.
    + exact Hzero_target.
    + lia.
    + lia.
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_9_learnt : solver_analyze_entail_wit_12_9_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_4 - 0) (ms_tags Mscan_2) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_4 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_4.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( 0 <= lit_var_c (Znth (j - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (j - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (_ & Htags & Hperm & _ & _ & _).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & _ & HSold & ERscan & HLold).
  assert (HndC : NoDup (map literal_var Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hv : 0 <= v < anz_n).
  { unfold v, q. replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hseen : In v (ms_tagged Mscan_2)).
  { eapply analysis_tags_exact_nonzero_in__lit_removable;
      [exact Htags | exact Hv |].
    intro Hzero. apply H_Znth.
    rewrite H_retval_4, !Z.sub_0_r. exact Hzero. }
  pose proof (Permutation_in v Hperm Hseen) as HinCur.
  assert (HcurSplit :
      In v (analyze_tags S0_2 R0_2 learnt0_2) \/
      In v (map literal_var (sublist 1 j Ccur))).
  { unfold analyze_tags in HinCur |- *.
    rewrite !in_app_iff in HinCur |- *.
    destruct HinCur as [HinS|[HinR|HinL]].
    - rewrite HSold in HinS. unfold resolve_S, resolve_new_S in HinS.
      apply in_app_iff in HinS. destruct HinS as [HinOld|HinNew].
      + left. left. apply In_zremove_iff in HinOld. tauto.
      + right. apply filter_In in HinNew. destruct HinNew as [HinNew _].
        apply in_map_iff in HinNew.
        destruct HinNew as [l [<- Hl]].
        apply filter_In in Hl. destruct Hl as [Hl _].
        apply in_map. exact Hl.
    - rewrite ERscan in HinR. cbn in HinR.
      destruct HinR as [<-|HinR].
      + left. left. exact Hinx.
      + left. right. left. exact HinR.
    - rewrite HLold in HinL. unfold resolve_learnt in HinL.
      rewrite map_app in HinL.
      apply in_app_iff in HinL. destruct HinL as [HinOld|HinNew].
      + left. right. right. exact HinOld.
      + right. apply in_map_iff in HinNew.
        destruct HinNew as [l [<- Hl]].
        apply filter_In in Hl. destruct Hl as [Hl _].
        apply in_map. exact Hl. }
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HndFirst :
      NoDup (map literal_var (firstn (Z.to_nat (j + 1)) Ccur))).
  { pose proof HndC as Hnd.
    rewrite <- (firstn_skipn (Z.to_nat (j + 1)) Ccur) in Hnd.
    rewrite map_app in Hnd.
    eapply NoDup_app_remove_r. exact Hnd. }
  assert (HndSub :
      NoDup (map literal_var (sublist 1 (j + 1) Ccur))).
  { unfold sublist. cbn.
    rewrite <- (firstn_skipn 1 (firstn (Z.to_nat (j + 1)) Ccur))
      in HndFirst.
    rewrite map_app in HndFirst.
    eapply NoDup_app_remove_l. exact HndFirst. }
  destruct HcurSplit as [HinInitial|HinPrefix].
  2: { rewrite Hprefix, map_app in HndSub. cbn in HndSub.
       rewrite Eqv in HndSub.
       pose proof (NoDup_app_disjoint _ _ v HndSub HinPrefix) as Hdis.
       exfalso. apply Hdis. simpl. tauto. }
  assert (Hmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = true).
  { apply zmem_true_iff. exact HinInitial. }
  assert (HSnext : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map].
    destruct (at_current_level_b (msolver_view anz_n Mact) (lit_denote q))
      eqn:Hat; cbn [filter map].
    - rewrite Eqv, Hmem. cbn [negb filter map].
      rewrite HSold. rewrite !app_nil_r. reflexivity.
    - rewrite HSold. rewrite !app_nil_r. reflexivity. }
  assert (HLnext : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter].
    destruct (below_current_b (msolver_view anz_n Mact) (lit_denote q))
      eqn:Hbelow; cbn [andb filter].
    - rewrite Eqv, Hmem. cbn [negb andb filter].
      rewrite HLold. rewrite !app_nil_r. reflexivity.
    - rewrite HLold. rewrite !app_nil_r. reflexivity. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase
      Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
      learnt_scan_2 words_scan_2 cnt).
  { msat_analyze_scan_unchanged_close phase H_Ccur HSnext HLnext. }
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_87_learnt_pure : solver_analyze_partial_solve_wit_87_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_learnt_offset_congruence.
Qed.


Lemma proof_of_solver_analyze_safety_wit_43_learnt : solver_analyze_safety_wit_43_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial. msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_11 : solver_analyze_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
    H_analyze_resolution_loop_inv.
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  pose proof (analyze_resolution_real_clause_source__analyze
    anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p
    H_analyze_resolution_loop_inv H_is_tag) as Hsource.
  destruct Hsource as
    [[Hbinary [HC [Hwf Hinitialized]]] | [co [Hbinary [Hin [HC Hwf]]]]].
  - subst c Ccur.
    rewrite (binary_scratch_initialized _ _ Hinitialized).
    unfold MiniSatClause.rep at 1.
    Exists false (ms_binary_lits Mcur).
    unfold analysis_clause_remainder.
    Left. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
  - unfold msolver_db in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply in_split in Hin. destruct Hin as [pre [post Hprob]].
      rewrite Hprob.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Left. Exists co pre post. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
      * cbn [fst snd msat_false].
        unfold msat_false.
        cancel.
    + apply in_split in Hin. destruct Hin as [pre [post Hlearnt]].
      rewrite Hlearnt.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Right. Exists co pre post. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
      * cbn [fst snd msat_false].
        unfold msat_false.
        cancel.
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_6_1 : solver_lit_removable_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  bind_fact ( top = Zlength (ms_tagged M0) ) as H_top.
  bind_fact ( analysis_tags_exact lrm_n tags_now tagged_now ) as H_analysis_tags_exact.
  replace (retval_5 - 1) with (Zlength stack_now - 1) in * by lia.
  subst stack_after.
  assert (Hrollback : removable_rollback_inv lrm_n top top (ms_tagged M0)
    (ms_tags M0) tags_now tagged_now tags_now).
  { eapply removable_rollback_start__lit_removable; eauto. }
  assert (Htop0 : 0 <= top).
  { rewrite H_top. apply Zlength_nonneg. }
  assert (Hlocals :
    ((( &( "v" ) )) # Int |-> retval_8) **
    ((( &( "c" ) )) # Ptr |->
      (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) **
    ((( &( "v" ) )) # Int |-> (Znth (Zlength stack_now - 1) stack_now 0)) **
    ((( &( "reasons" ) )) # Ptr |-> reasons_ptr) **
    ((( &( "levels" ) )) # Ptr |-> levels_ptr) |--
    ((( &( "v" ) )) # Int |->_) ** ((( &( "c" ) )) # Ptr |->_) **
    ((( &( "v" ) )) # Int |->_) ** ((( &( "reasons" ) )) # Ptr |->_) **
    ((( &( "levels" ) )) # Ptr |->_)).
  { sep_apply_l_atomic (store_int_undef_store_int (&( "v")) retval_8).
    sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "c"))
      (Znth (Znth (Zlength stack_now - 1) stack_now 0)
        (ms_reason_words M0) 0)).
    sep_apply_l_atomic (store_int_undef_store_int (&( "v"))
      (Znth (Zlength stack_now - 1) stack_now 0)).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr (&( "levels")) levels_ptr).
    cancel. }
  sep_apply_l_atomic Hlocals.
  prop_apply_p
    (ptrarray_missing_i_index_range__lit_removable
      reasons_ptr retval_8 0 lrm_n (ms_reason_words M0)).
  Intros_p Hidx. destruct Hidx as [Hidx0 Hidxn].
  msat_restore_array_read PtrArray.missing_i_merge_to_seg
    reasons_ptr retval_8 lrm_n (ms_reason_words M0).
  msat_restore_array_read IntArray.missing_i_merge_to_seg
    levels_ptr retval_8 lrm_n (mt_levels (ms_core M0)).
  msat_restore_array_read CharArray.missing_i_merge_to_seg
    tags_ptr retval_8 lrm_n tags_now.
  destruct (Z_lt_ge_dec top (Zlength tagged_now)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth top tagged_now 0 < lrm_n).
    { unfold analysis_tags_exact in H_analysis_tags_exact.
      destruct H_analysis_tags_exact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists tags_now.
    sep_apply_l_atomic (Veci.rep_ptr_rep (&( s_pre # "solver_t" ->ₛ "stack")) p
      (sublist 0 (Zlength stack_now - 1) stack_now)).
    msat_manual_entailer_with ltac:(lia).
  - assert (Htople : top <= Zlength tagged_now).
    { unfold removable_rollback_inv in Hrollback. tauto. }
    assert (Htopeq : top = Zlength tagged_now) by lia.
    Right. Exists tags_now.
    sep_apply_l_atomic (Veci.rep_ptr_rep (&( s_pre # "solver_t" ->ₛ "stack")) p
      (sublist 0 (Zlength stack_now - 1) stack_now)).
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_12_2 : solver_lit_removable_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( Znth (retval_2 - 0) tags_scan_2 0 <> 0 ) as H_Znth.
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
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_scan_2 stack_scan_2 tags_scan_2 tagged_scan_2
    Cnext v c (i + 1)).
  { eapply removable_reason_scan_advance_seen__lit_removable.
    - exact H_removable_reason_scan_inv.
    - rewrite H_Cnext, lits_denote_length. lia.
    - exact Hneq.
    - rewrite <- Hxdef. exact H_Znth. }
  Exists done_scan_2 stack_scan_2 tags_scan_2 tagged_scan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_50_pure : solver_lit_removable_partial_solve_wit_50_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  pose proof (Forall_lit_wf_Znth lrm_n clause_words i H_Forall ltac:(lia))
    as Hlit.
  unfold lit_wf_c in Hlit.
  replace (i - 0) with i by lia.
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]); lia.
Qed.


Lemma proof_of_solver_lit_removable_return_wit_2 : solver_lit_removable_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply Veci.rep_ptr_open. Intros tagged_cap_rb.
  pose proof (Zlength_nonneg tagged_scan) as H_Zlength.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  sep_apply
    (solver_removable_frame_lengths_keep__lit_removable
      s_pre M0 trail_ptr lrm_wl);
    Intros_p Hframe_lengths;
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
  prop_apply_p (CharArray.seg_Zlength tags_ptr 0 lrm_n tags_rollback);
    Intros_p Htags_len.
  try match goal with
       | Hinv : removable_rollback_inv _ _ _ _ _ _ _ _ ,
         Hj : _ = Zlength _ |- _ =>
           pose proof Hinv as Hinv_bounds;
           unfold removable_rollback_inv in Hinv_bounds;
           destruct Hinv_bounds as
             (Htop_nonneg & Htop_j & Hj_tagged & Htop_base & _);
           pose proof (removable_rollback_restore__lit_removable
             _ _ _ _ _ _ _ _ Hinv Hj) as [Htags Hbase]
       end.
  subst tags_rollback.
  rewrite Hbase in *.
  sep_apply clause_db_pair_refold__lit_removable.
  pose proof (analysis_cancel_ready_size__lit_removable
    _ _ _ _ _ _ H_analysis_cancel_ready) as Hnsize.
  assert (Horder_shape :
    Zlength (ms_orderpos M0) = ms_size M0) by lia.
  assert (Hactivity_shape :
    Zlength (ms_activity M0) = ms_size M0) by lia.
  assert (Htags_shape : Zlength (ms_tags M0) = ms_size M0) by lia.
  assert (Hstats_shape : Zlength (ms_stats M0) = 11) by lia.
  pose proof (analysis_cancel_ready_shape__lit_removable
    _ _ _ _ _ _ H_analysis_cancel_ready Horder_shape Hactivity_shape
    Htags_shape Hstats_shape) as Hshape.
  subst lrm_n.
  sep_apply (solver_removable_scratch_refold_residual__lit_removable
    s_pre M0 reasons_ptr levels_ptr trail_ptr tags_ptr tagged
    tagged_cap_rb stack_scan lrm_wl Hshape).
  bind_fact (msolver_seed_shadow M0) as Hseed.
  msat_removable_scratch_carry
    (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0) stack_scan)
    H_analysis_cancel_ready Hseed as Hreadyout Hseedout Hequivout.
  pose proof
    (removable_failure_post_pure__lit_removable
      (ms_size M0) lrm_F lrm_A_arr lrm_K M0 lrm_focus (ms_tags M0) (ms_tagged M0)
      stack_scan Hreadyout Hseedout Hequivout
      eq_refl eq_refl) as Hpostpure.
  unfold solver_lit_removable_post.
  Exists (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0) stack_scan).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_safety_wit_29 : solver_lit_removable_safety_wit_29.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 match goal with |- context [Z.land ?z 31] => assert (Hmask : 0 <= Z.land z 31 <= 31) by (replace 31 with (Z.ones 5) by reflexivity; rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound z 32 ltac:(lia)); change (0 <= z mod 32 <= 31); lia) end. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_9_split_goal_1 : solver_lit_removable_which_implies_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (v - 0) with v by lia; msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_9 : solver_lit_removable_which_implies_wit_9.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_solver_lit_removable_which_implies_wit_9_split_goal_1 M0 lrm_n v PreH1 PreH2).
Qed.


Lemma proof_of_solver_analyze_entail_wit_13_2_learnt : solver_analyze_entail_wit_13_2_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  pose proof H_analyze_clause_scan_inv as Hscan_original.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  subst phase. cbn in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as
    [Hready [Hequiv_scan [Hind_scan [Hroot
    [HCwf [HCnodup [Hjscan [Hcnt [Hwords [Hden
    [Htags [Hperm Hinitial]]]]]]]]]]]].
  destruct Hinitial as
    [HS0 [HR0 [Hlearnt0 [Hx0 [Hqtail_initial
    [Hconflict [HS [HR Hlearnt]]]]]]]].
  destruct (msat_analysis_ready_scan_facts anz_n anz_F anz_A_arr K Mscan_2
    anz_focus Hready) as (Hwf & Hstable & Htrailimpl & Hqtrail & Hlevel0).
  destruct (msat_analysis_equiv_transport anz_n Mact Mscan_2 Hequiv_scan)
    as (_ & _ & Hview).
  destruct Hconflict as
    [Hent [Hfalse_raw [Hconf_wf [Hconf_nd [l [HlC Hllevel]]]]]].
  assert (Hfalse : clause_false
    (assignment (msolver_view anz_n Mact)) Ccur).
  { rewrite msolver_view_assignment.
    intros q HqC. pose proof (Hfalse_raw q HqC) as Hqfalse.
    rewrite Forall_forall in Hconf_wf.
    pose proof (Hconf_wf q HqC) as Hqwf.
    unfold literal_wf, var_in_range in Hqwf.
    unfold eval_partial_literal in Hqfalse |- *.
    rewrite mt_pv_nonneg by lia.
    unfold assigns_pv, assigns_val in Hqfalse. exact Hqfalse. }
  assert (Hstable_act : stable_view (msolver_view anz_n Mact)) by
    (rewrite Hview; exact Hstable).
  assert (Hlevel0_act : forall v b,
    assignment (msolver_view anz_n Mact) v = Some b ->
    level_of (msolver_view anz_n Mact) v = Some 0 ->
    entails_clause anz_F (satisfying_literal v b :: nil)).
  { rewrite Hview. exact Hlevel0. }
  destruct Hstable_act as [Hgrounded_act Hclosed_act].
  pose proof (analyze_init anz_F (msolver_view anz_n Mact) Ccur
    Hgrounded_act Hclosed_act Hlevel0_act Hent Hfalse Hconf_nd) as Hainv.
  assert (HClen : Zlength Ccur = Zlength clause_words2) by
    (rewrite H_Ccur, lits_denote_length; reflexivity).
  assert (Hjfull : j = Zlength Ccur) by lia.
  assert (Hsubfull : sublist 0 j Ccur = Ccur).
  { rewrite Hjfull. apply sublist_self. reflexivity. }
  change (firstn (Z.to_nat j) Ccur = Ccur) in Hsubfull.
  rewrite Hsubfull in HS, Hlearnt.
  unfold analyze_start_S, analyze_start_learnt in Hainv.
  rewrite <- HS, <- HR, <- Hlearnt in Hainv.
  rewrite Hview in Hainv.
  assert (Hqtailind : ms_qtail Mscan_2 = ind + 1).
  { pose proof Hequiv_scan as Hequiv_qtail.
    unfold analysis_core_equiv in Hequiv_qtail.
    destruct Hequiv_qtail as [_ [_ [Eqtail _]]]. lia. }
  assert (HinS : In (literal_var l) Sscan_2).
  { rewrite HS. unfold analyze_start_S.
    apply in_map. apply filter_In. split; [exact HlC|].
    apply at_current_level_b_true_iff.
    rewrite msolver_view_current_level. exact Hllevel. }
  assert (Hcntpos : 0 < cnt).
  { rewrite Hcnt. destruct Sscan_2 as [|s ss].
    - contradiction.
    - rewrite Zlength_cons. pose proof (Zlength_nonneg ss). lia. }
  assert (HSrank : forall v, In v Sscan_2 -> exists r,
    assignment_rank (msolver_view anz_n Mscan_2) v = Some r /\
    Z.of_nat r <= ind).
  { pose proof Hainv as Hainv_fields.
    unfold analyze_inv in Hainv_fields.
    destruct Hainv_fields as [_ [_ [_ [Hassigned _]]]].
    rewrite Forall_forall in Hassigned.
    intros v Hv. destruct (Hassigned v Hv) as [b Hass].
    destruct Hstable as [Hgrounded _].
    destruct (Hgrounded v b Hass) as [d [r [_ [Hrank _]]]].
    exists r. split; [exact Hrank|].
    cbn [msolver_view view_of assignment_rank] in Hrank.
    pose proof (trail_pos_bound _ _ _ Hrank) as Hbound.
    rewrite <- Hqtrail, Hqtailind in Hbound. lia. }
  destruct (HSrank (literal_var l) HinS) as
    [rl [Hlrank Hlrankle]].
  assert (Hbackward : analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mscan_2
    anz_focus words_scan_2 cnt ind Sscan_2 Rscan_2 learnt_scan_2).
  { unfold analyze_backward_scan_inv.
    split; [exact Hready|].
    split; [exact Hainv|].
    split; [exact Hcnt|].
    split; [exact Hcntpos|].
    split; [exact Hind_scan|].
    split; [exact Hwords|].
    split; [exact Hroot|].
    split; [exact Hden|].
    split; [exact Htags|].
    split; [exact Hperm|].
    split; [exact HSrank|].
    split.
    - intros v Hv. rewrite HR in Hv. contradiction.
    - exists (literal_var l), rl. split; [ | split ]; assumption. }
  assert (Hindex : 0 <= ind <
    Zlength (mt_trail (ms_core Mscan_2))) by
    (rewrite <- Hqtrail; exact Hind_scan).
  pose proof (msat_trail_lit_var_range anz_n Mscan_2 ind Hwf Hindex)
    as Hvarrange.
  assert (Htagzero :
    Znth (lit_var_c (Znth ind (mt_trail (ms_core Mscan_2)) 0))
      (ms_tags Mscan_2) 0 = 0 -> 0 < ind).
  { intro Hzero. destruct (Z.eq_dec ind 0) as [Hind0|]; [|lia].
    subst ind. assert (rl = 0%nat) by lia. subst rl.
    cbn [msolver_view view_of assignment_rank] in Hlrank.
    pose proof (trail_pos_var _ _ _ Hlrank) as Hlvar.
    change (lit_var_c (Znth 0 (mt_trail (ms_core Mscan_2)) 0) =
      literal_var l) in Hlvar.
    assert (HlAnalyze : In (literal_var l)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)).
    { unfold analyze_tags. apply in_or_app. left. exact HinS. }
    assert (HlTagged : In (literal_var l) (ms_tagged Mscan_2)).
    { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact HlAnalyze]. }
    pose proof Htags as Htags_copy.
    destruct Htags_copy as [_ [_ [_ [_ Htagiff]]]].
    assert (Hlrange : 0 <= literal_var l < anz_n) by
      (rewrite <- Hlvar; exact Hvarrange).
    pose proof (proj2 (Htagiff (literal_var l) Hlrange) HlTagged) as Htagone.
    rewrite <- Hlvar in Htagone. congruence. }
  assert (Hscan_box : unit -> analyze_clause_scan_inv anz_n anz_F anz_A_arr K
    Mact Mscan_2 anz_focus AnalyzeInitial Ccur j ind S0_2 R0_2 learnt0_2 x_2
    Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt).
  { intro. exact Hscan_original. }
  destruct Hvarrange as [Hvarlo Hvarhi].
  Left. Left.
  Exists activity_ptr_scan orderpos_ptr_scan
    words_scan_2 Sscan_2 Rscan_2 learnt_scan_2 Mscan_2.
  split_pure_spatial.
  - cancel (Veci.rep learnt_pre words_scan_2).
    cancel.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    + rewrite Z.sub_0_r. exact Hvarlo.
    + rewrite Z.sub_0_r. exact Hvarhi.
    + rewrite !Z.sub_0_r. exact Htagzero.
Qed.


Lemma proof_of_solver_analyze_entail_wit_14_5_learnt : solver_analyze_entail_wit_14_5_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame words_done Sdone Rdone learnt_done Mdone.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_16_pure : solver_analyze_partial_solve_wit_16_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_18_pure : solver_analyze_partial_solve_wit_18_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_106_learnt_pure : solver_analyze_partial_solve_wit_106_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_112_learnt_pure : solver_analyze_partial_solve_wit_112_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  subst Mact.
  subst j.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mscan Mscan anz_focus phase Ccur 1 ind S0 R2 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= lit_var_c (Znth (1 - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (1 - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  pose proof H_analyze_clause_scan_inv as Hscan.
  unfold analyze_clause_scan_inv in Hscan.
  destruct Hscan as [Hready Hscan_rest].
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mbase [Hcancel [Hequiv [Hheap Hready_rest]]]].
  unfold order_heap_wf, msolver_heap in Hheap.
  prop_apply_p (DoubleArray.seg_Zlength
    activity_ptr_scan 0 anz_n (ms_activity Mscan)).
  Intros_p Hactivity.
  replace (anz_n - 0) with anz_n in Hactivity by lia.
  split_pures.
  - dump_pre_spatial. exact Hheap.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. exact Hactivity.
  - dump_pre_spatial. exact H_lit_var_c_2.
  - dump_pre_spatial. exact H_lit_var_c.
  - dump_pre_spatial. exact Hheap.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_134_pure : solver_analyze_partial_solve_wit_134_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial.
  match goal with
  | Hscan : analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus
      words_resolved cnt ind Sresolved Rresolved learnt_resolved |- _ =>
      unfold analyze_backward_scan_inv in Hscan;
      destruct Hscan as [Hready _];
      pose proof
        (analysis_cancel_ready_reason_core anz_n anz_F anz_A_arr K Mresolved anz_focus Hready)
        as [Hsize _]
  end.
  symmetry. exact Hsize.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_152_pure : solver_analyze_partial_solve_wit_152_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  msat_analyze_close_learnt_vec_lit_range Hf.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_5 : solver_analyze_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (analysis_cancel_ready anz_n anz_F anz_A_arr K Mcur anz_focus) as Hready.
  bind_fact (reason_target_wf anz_n Mcur x c Ccur) as Htarget.
  bind_fact (level_of (msolver_view anz_n Mcur) x =
    Some (current_level (msolver_view anz_n Mcur))) as Hlevel.
  bind_fact (is_tag c = msat_true) as Htagged.
  bind_fact (q = tag_lit c) as Hq.
  pose proof (msat_binary_reason_current_level
    anz_n anz_F anz_A_arr K Mcur anz_focus x c Ccur Hready Htarget Hlevel Htagged)
    as [Hrange Hqlevel].
  subst q. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_9 : solver_analyze_which_implies_wit_9.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mcur anz_focus ) as H_analysis_cancel_ready.
    bind_fact ( level_of (msolver_view anz_n Mcur) (lit_var_c q) = Some (current_level (msolver_view anz_n Mcur)) ) as
      H_level_of.
  pose proof H_analysis_cancel_ready as H_analysis_cancel_ready_folded.
  pose proof H_level_of as H_level_of_folded.
  destruct H_analysis_cancel_ready as [M0 [Hready [Hequiv Hrest]]].
  destruct Hready as [[Hpending Hweak] Hready].
  assert (Hwf0 : mtrail_wf anz_n (ms_core M0)).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_trail_wf Hweak).
    - exact (msa_trail_wf Hweak). }
  destruct Hequiv as [_ [_ [_ [Hcore _]]]].
  assert (Hwf : mtrail_wf anz_n (ms_core Mcur)).
  { rewrite Hcore. exact Hwf0. }
  unfold msolver_view, view_of in H_level_of.
  cbn in H_level_of.
  destruct (trail_pos (ms_core Mcur) (lit_var_c q)) as [k|] eqn:Hpos;
    cbn in H_level_of; [|discriminate].
  inversion H_level_of as [Hlevel].
  assert (Hresult :
    Znth (lit_var_c q) (mt_levels (ms_core Mcur)) 0 =
      Zlength (mt_lim (ms_core Mcur))).
  { rewrite <- (trail_pos_var (ms_core Mcur) (lit_var_c q) k Hpos).
    rewrite (mtw_levels_agree Hwf (Z.of_nat k)).
    - exact Hlevel.
    - split; [lia|]. eapply trail_pos_bound. exact Hpos. }
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact H_level_of_folded.
    + dump_pre_spatial. exact H_analysis_cancel_ready_folded.
    + dump_pre_spatial.
      replace (lit_var_c q - 0) with (lit_var_c q) by lia.
      lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_20 : solver_analyze_which_implies_wit_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (analyze_resolution_exit
    anz_n anz_F anz_A_arr K Mresolution anz_focus p words_before) as Hexit.
  pose proof Hexit as Hexit_copy.
  unfold analyze_resolution_exit in Hexit_copy.
  destruct Hexit_copy as (_ & Hlen & _).
  entailer!.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_31 : solver_analyze_which_implies_wit_31.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (analysis_cancel_ready
    anz_n anz_F anz_A_arr K Mclear anz_focus) as Hready.
  pose proof (analysis_cancel_ready_size__lit_removable
    anz_n anz_F anz_A_arr K Mclear anz_focus Hready) as Hsize.
  subst anz_n.
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_vecs_rep, solver_ptrs_rep,
    solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply peel_scalars_size.
  Exists act asg opos.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_2_split_goal_1 : solver_lit_removable_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 1 - 0) with (retval_3 - 1) by lia.
  reflexivity.
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_2 : solver_lit_removable_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_lit_removable_entail_wit_2_split_goal_1.
Qed.



Lemma proof_of_solver_lit_removable_partial_solve_wit_3_pure : solver_lit_removable_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_lit_var_parity_bounds l_pre.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_25_pure : solver_lit_removable_partial_solve_wit_25_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( retval = Zlength stack_now ) as H_retval.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  rewrite H_retval.
  unfold removable_reason_focus, reason_target_wf in *.
  destruct H_removable_reason_focus as [_ [_ [_ [_ Hkind]]]].
  destruct Hkind as [[_ [Hpositive _]] | [co [_ [_ [Hin _]]]]].
  - (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - pose proof (analysis_cancel_ready_db_wf__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as Hdb.
    pose proof (db_wf_ptr_pos lrm_n (msolver_db M0) _ co Hdb Hin) as Hpositive.
    msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_57_pure : solver_lit_removable_partial_solve_wit_57_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  pose proof (Forall_lit_wf_Znth lrm_n clause_words i H_Forall ltac:(lia))
    as Hlit.
  unfold lit_wf_c in Hlit.
  replace (i - 0) with i by lia.
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]); lia.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_68_pure : solver_lit_removable_partial_solve_wit_68_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  msat_lit_removable_lits_pointer_even lrm_n M0 c is_learnt_now clause_words.
Qed.


Lemma proof_of_solver_lit_removable_safety_wit_21 : solver_lit_removable_safety_wit_21.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 match goal with |- context [Z.land ?z 31] => assert (Hmask : 0 <= Z.land z 31 <= 31) by (replace 31 with (Z.ones 5) by reflexivity; rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound z 32 ltac:(lia)); change (0 <= z mod 32 <= 31); lia) end. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_4_split_goal_1 : solver_lit_removable_which_implies_wit_4_split_goal_1.
Abort.


Lemma proof_of_solver_lit_removable_which_implies_wit_4 : solver_lit_removable_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_now tagged_now stack_now done) as Hinv.
  bind_fact (0 < Zlength stack_now) as Hlen.
  bind_fact (v = Znth (Zlength stack_now - 1) stack_now 0) as Hv.
  pose proof (list_last_sublist__lit_removable
    stack_now v Hlen Hv) as Hlast.
  Exists (sublist 0 (Zlength stack_now - 1) stack_now).
  entailer!.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_8_split_goal_1 : solver_lit_removable_which_implies_wit_8_split_goal_1.
Abort.


Lemma proof_of_solver_lit_removable_which_implies_wit_8 : solver_lit_removable_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (CharArray.seg_split_to_missing_i
    tags_ptr 0 v lrm_n tags_now 0 ltac:(lia)).
  cancel.
  replace (v - 0) with v by lia.
  cancel.
Qed.


