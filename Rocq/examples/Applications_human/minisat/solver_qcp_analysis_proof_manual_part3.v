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
Lemma proof_of_solver_analyze_entail_wit_11_2 : solver_analyze_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  msat_analyze_resolve Mact phase Ccur clause_words2 is_learnt2 orderpos_ptr_clause activity_ptr_clause.
Qed.


Lemma proof_of_solver_analyze_entail_wit_14_2_learnt : solver_analyze_entail_wit_14_2_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame words_done Sdone Rdone learnt_done Mdone.
Qed.


Lemma proof_of_solver_analyze_entail_wit_18 : solver_analyze_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists phase_3 Ccur_3 words_3 Mcur_3
    phase_3 Ccur_3 words_3 Mcur_3.
  msat_manual_entailer_with ltac:(assumption).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_11_pure : solver_analyze_partial_solve_wit_11_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_23_pure : solver_analyze_partial_solve_wit_23_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_25_pure : solver_analyze_partial_solve_wit_25_pure.
Proof.
  msat_analyze_reason_target_lit_bound.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_89_learnt_pure : solver_analyze_partial_solve_wit_89_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_learnt_offset_congruence.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_115_learnt_pure : solver_analyze_partial_solve_wit_115_learnt_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as Hwf_words.
  pose proof (Forall_Znth_elim _ _ _ 0 (j - 0) Hwf_words ltac:(lia)) as Hlit.
  unfold lit_wf_c in Hlit.
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_168_pure : solver_analyze_partial_solve_wit_168_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_done words_uip kept_done removed_done words_done T_done i j ) as
      H_analyze_minimize_loop_inv.
  unfold analyze_minimize_loop_inv in H_analyze_minimize_loop_inv.
  destruct H_analyze_minimize_loop_inv as (Hj & Hji & HiLen & Hlen & _).
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_return_wit_2 : solver_analyze_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (analysis_core_equiv_base_completion__api_reentry
    M0 Mfinal PreH1) as Hreuse.
  unfold analysis_core_equiv in PreH1.
  unfold solver_analyze_post.
  Exists Mfinal words_final blevel.
  split_pure_spatial; [cancel; try reflexivity | split_pures; dump_pre_spatial; solve [auto | tauto | lia | int_auto] ..].
Qed.



Lemma proof_of_solver_analyze_safety_wit_34_learnt : solver_analyze_safety_wit_34_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_analyze_scan_count_bound.
Qed.


Lemma proof_of_solver_analyze_safety_wit_35_learnt : solver_analyze_safety_wit_35_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_analyze_scan_count_bound.
Qed.


Lemma proof_of_solver_analyze_safety_wit_58 : solver_analyze_safety_wit_58.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  assert (Hbounds : cnt - 1 <= INT_MAX /\ INT_MIN <= cnt - 1).
  { unfold analyze_backward_scan_inv in H_analyze_backward_scan_inv.
    destruct H_analyze_backward_scan_inv as
      (Hready & Hinv & Hcnt & Hcntpos & Hind & Hwords & Hroot & Hlits &
       Htags & Hperm & HrankS & HrankR & Hex).
    assert (Hnmax : 2 * anz_n <= INT_MAX).
    { destruct Hready as [M_ready_base_hyp [Hcancel Hready_rest]].
      destruct Hcancel as [Hweak Hcancel_rest].
      destruct Hweak as [Hcapacity Hcontext].
      destruct K as [A_inst | A_proc]; cbn in Hcontext.
      - pose proof (msw_shape Hcontext) as Hshape.
        pose proof (msw_size Hcontext) as Hsize.
        unfold solver_shape in Hshape.
        destruct Hshape as (_ & _ & Hliteral_bound & _).
        rewrite <- Hsize in Hliteral_bound. exact Hliteral_bound.
      - pose proof (msa_shape Hcontext) as Hshape.
        pose proof (msa_size Hcontext) as Hsize.
        unfold solver_shape in Hshape.
        destruct Hshape as (_ & _ & Hliteral_bound & _).
        rewrite <- Hsize in Hliteral_bound. exact Hliteral_bound. }
    destruct Hinv as (_ & Hnodup & HlevelsS & HassignedS & HlevelsR &
                      HrankOrder & HlevelsLearnt & HfalseLearnt).
    destruct Htags as (Htags_length & Htagged_nodup & Htagged_range &
                       Htag_values & Htag_exact).
    assert (Hanalysis_range :
      Forall (fun v => 0 <= v < anz_n) (analyze_tags Sresolved Rresolved learnt_resolved)).
    { rewrite Forall_forall in Htagged_range |- *.
      intros v Hv.
      apply Htagged_range.
      eapply Permutation_in.
      - apply Permutation_sym. exact Hperm.
      - exact Hv. }
    unfold analyze_tags in Hnodup, Hanalysis_range.
    assert (HnodupS : NoDup Sresolved).
    { eapply NoDup_app_remove_r. exact Hnodup. }
    assert (HrangeS : Forall (fun v => 0 <= v < anz_n) Sresolved).
    { rewrite Forall_app in Hanalysis_range.
      exact (proj1 Hanalysis_range). }
    assert (Hn : 0 <= anz_n) by lia.
    rewrite Forall_forall in HrangeS.
    pose proof (NoDup_Z_bounded_length Sresolved anz_n Hn HnodupS HrangeS) as HlenS.
    rewrite Zlength_correct in Hcnt.
    split; lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_1 : solver_analyze_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_pre, solver_rep_levels_wl_at,
    solver_rep_analyze_at, solver_rep_at.
  Intros act asg opos rsn trl tgs.
  Exists rsn trl tgs.
  Exists act asg opos.
  unfold z_nil.
  split_pure_spatial.
  - msat_entailer_with ltac:(int_auto).
  - split_pures.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. unfold repeat_Z. tauto.
    + dump_pre_spatial. tauto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact H0.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_14 : solver_analyze_which_implies_wit_14.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mact anz_focus phase c Ccur words cnt ind p ) as
    H_analyze_resolution_loop_inv.
  pose proof (analyze_resolution_real_clause_source__analyze
    anz_n anz_F anz_A_arr K Mact anz_focus phase c Ccur words cnt ind p
    H_analyze_resolution_loop_inv H_is_tag) as Hsource.
  destruct Hsource as
    [[Hbinary [HC [Hwf Hinitialized]]] | [co [Hbinary [Hin [HC Hwf]]]]].
  - subst c Ccur.
    rewrite (binary_scratch_initialized _ _ Hinitialized).
    unfold MiniSatClause.rep at 1.
    Exists false activity_ptr_loop orderpos_ptr_loop (ms_binary_lits Mact).
    unfold analysis_clause_remainder.
    Left. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
  - unfold msolver_db in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply in_split in Hin. destruct Hin as [pre [post Hprob]].
      rewrite Hprob.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) activity_ptr_loop orderpos_ptr_loop (co_lits co).
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
      Exists (co_learnt co) activity_ptr_loop orderpos_ptr_loop (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Right. Exists co pre post. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
      * cbn [fst snd msat_false].
        unfold msat_false.
        cancel.
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_7 : solver_lit_removable_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (j - 0) with j in * by lia.
  assert (Hstep : removable_rollback_inv lrm_n top (j + 1) (ms_tagged M0)
    (ms_tags M0) tags_now tagged_now
    (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2)).
  { eapply removable_rollback_step__lit_removable; eauto. }
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "tagged") tagged tagged_now cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_full tags_ptr
      (Znth j tagged_now 0) lrm_n 0 tags_rollback_2).
  { dump_pre_spatial. lia. }
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2)).
  destruct (Z_lt_ge_dec (j + 1) (Zlength tagged_now)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth (j + 1) tagged_now 0 < lrm_n).
    { assert (Hexact : analysis_tags_exact lrm_n tags_now tagged_now).
      { unfold removable_rollback_inv in Hstep. tauto. }
      unfold analysis_tags_exact in Hexact.
      destruct Hexact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2).
    msat_manual_entailer_with ltac:(lia).
  - assert (Hjle : j + 1 <= Zlength tagged_now).
    { unfold removable_rollback_inv in Hstep. tauto. }
    assert (Hjeq : j + 1 = Zlength tagged_now) by lia.
    Right. Exists (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2).
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_13_4 : solver_lit_removable_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( incl (v :: stack_scan) (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan stack_scan tags_scan
    tagged_scan Cnext v c i ) as H_removable_reason_scan_inv.
  bind_fact ( Cnext = lits_denote clause_words ) as H_Cnext.
  assert (Hilen : i = Zlength Cnext) by
    (rewrite H_Cnext, lits_denote_length; lia).
  assert (Hfocus : removable_reason_focus lrm_n M0 v c Cnext) by
    (pose proof H_removable_reason_scan_inv as Hscan;
     unfold removable_reason_scan_inv in Hscan; tauto).
  assert (Hnotag : is_tag c = false) by
    (apply even_not_tag;
     assert (Heven : Z.even c = true) by
       (replace c with (2 * (Z.quot c 2));
        [rewrite Z.even_even; reflexivity |
         pose proof (Z.quot_rem c 2 ltac:(lia)); lia]);
     exact Heven).
  assert (Hhead : literal_var (Znth 0 Cnext (Pos 0)) = v) by
    (eapply real_reason_clause_head__lit_removable;
     [exact H_analysis_cancel_ready | exact Hfocus | exact Hnotag]).
  assert (Hloop_done :
    removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0)
      tags_scan tagged_scan stack_scan (v :: done_scan)) by
    (eapply removable_reason_scan_finish__lit_removable;
     [exact H_removable_reason_scan_inv | exact Hilen | exact Hhead]).
  assert (Hstack_incl :
    incl stack_scan (map lit_var_c (mt_trail (ms_core M0)))) by
    (intros x Hx; apply H_incl; right; exact Hx).
  sep_apply clause_db_pair_refold__lit_removable.
  Exists (v :: done_scan)
    stack_scan tags_scan tagged_scan. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_65_pure : solver_lit_removable_partial_solve_wit_65_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (j - 0) with j by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_return_wit_1 : solver_lit_removable_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  assert (Hstack_nil : stack_now = (@nil Z)) by (
    destruct stack_now as [| stack_head stack_tail];
    [reflexivity | rewrite Zlength_cons in *;
      pose proof (Zlength_nonneg stack_tail); lia]).
  sep_apply
    (solver_removable_frame_lengths_keep__lit_removable
      s_pre M0 trail_ptr lrm_wl);
    Intros_p Hframe_lengths;
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
  prop_apply_p (CharArray.seg_Zlength tags_ptr 0 lrm_n tags_now);
    Intros_p Htags_len.
  match goal with
  | Hentry : analysis_tags_exact _ (ms_tags _) _ |- _ =>
      pose proof Hentry as Hentry_shape;
      unfold analysis_tags_exact in Hentry_shape;
      destruct Hentry_shape as [Hentry_len _]
  end.
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
  pose proof (solver_shape_scratch_update__lit_removable
    M0 tags_now tagged_now stack_now
    Hshape ltac:(lia)) as Hshapeout.
  sep_apply (Veci.rep_ptr_rep &(s_pre # "solver_t" ->ₛ "stack") p stack_now).
  sep_apply
    (solver_removable_scratch_refold_general__lit_removable
      s_pre M0 lrm_n reasons_ptr levels_ptr trail_ptr tags_ptr
      tags_now tagged_now stack_now
      lrm_wl Hnsize Hshapeout).
  match goal with
  | Hinv : removable_dfs_loop_inv ?lrm_n ?M0 _ _ (ms_tagged ?M0) _ _ _ _ |- _ =>
      pose proof Hinv as Hcomplete_inv
  end.
  rewrite Hstack_nil in Hcomplete_inv.
  pose proof
    (removable_dfs_complete_post__lit_removable _ _ _ _ _ _ _ _ Hcomplete_inv)
    as (fresh & Htagged_fresh & Htags_exact_out &
        Hremovable & Hassigned_out).
  bind_fact (msolver_seed_shadow M0) as Hseed.
  msat_removable_scratch_carry
    (msolver_scratch_update M0 tags_now tagged_now stack_now)
    H_analysis_cancel_ready Hseed as Hreadyout Hseedout Hequivout.
  pose proof
    (removable_success_post_pure__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus tags_now tagged_now
      stack_now l_pre fresh Hreadyout Hseedout Hequivout
      Hstack_nil Htagged_fresh Htags_exact_out
      Hremovable Hassigned_out) as Hpostpure.
  unfold solver_lit_removable_post.
  Exists (msolver_scratch_update M0 tags_now tagged_now stack_now).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact Hpostpure.
Qed.



Lemma proof_of_solver_lit_removable_safety_wit_34 : solver_lit_removable_safety_wit_34.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : clause_hdr_word _ _ <= _ |- _ => unfold clause_hdr_word in H
  end.
  apply _derivable1_andp_intros.
  all: dump_pre_spatial.
  all: destruct is_learnt_now; lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_1 : solver_lit_removable_which_implies_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
match goal with Hready : analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K ?md lrm_focus, Hreason : Znth (lit_var_c l) (ms_reason_words ?md) 0 <> 0 |- _ =>
 destruct (analysis_cancel_ready_reason_target__lit_removable lrm_n lrm_F lrm_A_arr lrm_K md lrm_focus (lit_var_c l) Hready ltac:(lia) Hreason) as [Croot Htarget];
 destruct (analysis_cancel_ready_reason_core lrm_n lrm_F lrm_A_arr lrm_K md lrm_focus Hready) as [Hsize _]
end. Exists Croot. unfold solver_reason_levels_frame_at. subst lrm_n. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_17 : solver_lit_removable_which_implies_wit_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact lrm_n tags_scan tagged_scan ) as H_analysis_tags_exact.
  bind_fact ( 0 <= v ) as H_v.
  bind_fact ( v < lrm_n ) as H_v_2.
  bind_fact ( Znth v tags_scan 0 = 0 ) as H_Znth.
  bind_fact ( Znth v (ms_reason_words M0) 0 <> 0 ) as H_Znth_2.
  destruct
    (analysis_cancel_ready_reason_target__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus v H_analysis_cancel_ready (conj H_v H_v_2) H_Znth_2)
    as [Cpush Htarget].
  pose proof
    (analysis_tags_exact_untagged_strict__lit_removable
      lrm_n tags_scan tagged_scan v H_analysis_tags_exact (conj H_v H_v_2) H_Znth)
    as Hstrict.
  Exists Cpush.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_10_1_learnt : solver_analyze_entail_wit_10_1_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_analyze_open_at in *.
  msat_analyze_scan_entry Mact phase Ccur clause_words2 is_learnt2 orderpos_ptr_clause activity_ptr_clause.
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_1_learnt : solver_analyze_entail_wit_12_1_learnt.
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
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Mscan_2 = Mact ) as H_Mscan_2.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  set (v := lit_var_c (Znth (j - 0) clause_words2 0)).
  set (Mnext := analyze_tag_step_msolver Mscan_2
    (replace_Znth v 1 (ms_tags Mscan_2))
    (ms_tagged Mscan_2 ++ (v :: nil)) activity1 orderpos1 heap1 var_inc1).
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & _).
  assert (HSold : Sscan_2 = analyze_start_S (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = analyze_start_learnt (msolver_view anz_n Mact)
      (sublist 0 j Ccur)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hreadynew : analysis_cancel_ready anz_n anz_F anz_A_arr K Mnext anz_focus)
    by (unfold Mnext; apply ms_analyze_tag_step_cancel_ready;
        [exact Hreadyold | exact H_order_heap_wf | exact H_u_2]).
  assert (Htagsnew : analysis_tags_exact anz_n (replace_Znth v 1 (ms_tags Mscan_2))
      (ms_tagged Mscan_2 ++ (v :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htagsold | unfold v; lia | unfold v in *; lia]).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags (Sscan_2 ++ (v :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hpermold).
  assert (Hcert : propagation_conflict_cert anz_n anz_F Mact Ccur)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [_ [_ _]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite H_Mscan_2. rewrite Eqv in Hass. exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  assert (Hrqb : Z.of_nat rq < Zlength (mt_trail (ms_core Mscan_2))).
  { apply (trail_pos_bound (ms_core Mscan_2) v rq Hrank). }
  pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
  rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrank) in Hagree.
  assert (Hdqcur : level_of_index (ms_core Mscan_2) (Z.of_nat rq) =
      Zlength (mt_lim (ms_core Mscan_2))).
  { fold v in H_retval_10. rewrite H_retval_10, H_retval_11 in H_Znth.
    replace (v - 0) with v in H_Znth by lia.
    rewrite <- H_Mscan_2 in H_Znth. lia. }
  assert (Hat : at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true).
  { apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite Eqv, <- H_Mscan_2.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite Hrank. cbn. f_equal. exact Hdqcur. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { unfold below_current_b.
    rewrite Eqv, <- H_Mscan_2.
    unfold msolver_view, view_of. cbn [level_of current_level].
    rewrite Hrank. cbn. rewrite Hdqcur, Z.ltb_irrefl, Bool.andb_false_r.
    reflexivity. }
  msat_analyze_start_step_tag q v anz_n Mact Ccur j clause_words2
    Sscan_2 learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow Eqv.
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mnext anz_focus phase Ccur
      (j + 1) ind S0_2 R0_2 learnt0_2 x_2
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
    cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_16_learnt : solver_analyze_entail_wit_12_16_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_5 - 0) (mt_levels (ms_core Mscan_2)) 0 <= 0 ) as H_Znth.
  bind_fact ( retval_5 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_5.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < Zlength clause_words2 ) as H_j_2.
  bind_fact ( analysis_core_equiv Mact Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  set (q := Znth j clause_words2 0).
  set (v := lit_var_c q).
  assert (Eqv : literal_var (lit_denote q) = v).
  { rewrite lit_var_c_denote. reflexivity. }
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Hready : analysis_cancel_ready anz_n anz_F anz_A_arr K Mscan_2 anz_focus)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hrootlt :
      ms_root_level Mscan_2 < Zlength (mt_lim (ms_core Mscan_2)))
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  pose proof (analysis_cancel_ready_trail_wf__analyze
    anz_n anz_F anz_A_arr K Mscan_2 anz_focus Hready) as Htrailwf.
  assert (Hrootnonneg : 0 <= ms_root_level Mscan_2).
  { destruct Hready as [Mentry [[[_ Hbase] _] [Hequiv _]]].
    assert (Eroot : ms_root_level Mscan_2 = ms_root_level Mentry).
    { unfold analysis_core_equiv in Hequiv. tauto. }
    rewrite Eroot.
    destruct K; [pose proof (msw_shape Hbase) as Hshape |
                 pose proof (msa_shape Hbase) as Hshape];
      unfold solver_shape in Hshape; tauto. }
  assert (Hcurpos : 0 < Zlength (mt_lim (ms_core Mscan_2))) by lia.
  assert (Hphys : Znth v (mt_levels (ms_core Mscan_2)) 0 <= 0).
  { replace (j - 0) with j in H_retval_5 by lia.
    fold q in H_retval_5. fold v in H_retval_5.
    rewrite H_retval_5 in H_Znth.
    replace (v - 0) with v in H_Znth by lia. exact H_Znth. }
  assert (Hclass :
      at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = false /\
      below_current_b (msolver_view anz_n Mact) (lit_denote q) = false).
  { destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
    - pose proof (trail_pos_bound (ms_core Mscan_2) v rq Hrank) as Hrqb.
      pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia))
        as Hagree.
      rewrite (trail_pos_var (ms_core Mscan_2) v rq Hrank) in Hagree.
      set (dq := level_of_index (ms_core Mscan_2) (Z.of_nat rq)).
      assert (Hlev : level_of (msolver_view anz_n Mact) v = Some dq).
      { rewrite Eview. unfold msolver_view, view_of.
        cbn [level_of]. rewrite Hrank. reflexivity. }
      assert (Hdqle : dq <= 0).
      { unfold dq. rewrite <- Hagree. exact Hphys. }
      split.
      + unfold at_current_level_b. rewrite Eqv, Hlev.
        rewrite Eview, msolver_view_current_level.
        apply Z.eqb_neq. lia.
      + unfold below_current_b. rewrite Eqv, Hlev.
        destruct (0 <? dq)%Z eqn:Hdq.
        * apply Z.ltb_lt in Hdq. lia.
        * reflexivity.
    - assert (Hlev : level_of (msolver_view anz_n Mact) v = None).
      { rewrite Eview. unfold msolver_view, view_of.
        cbn [level_of]. rewrite Hrank. reflexivity. }
      split; [unfold at_current_level_b|unfold below_current_b];
        rewrite Eqv, Hlev; reflexivity. }
  destruct Hclass as [Hat Hbelow].
  assert (HSold : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
  assert (HSnext : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_S, resolve_new_S in *.
    rewrite Hprefix, filter_app, map_app, filter_app.
    cbn [filter map]. rewrite Hat. cbn [filter map].
    rewrite HSold. rewrite !app_nil_r. reflexivity. }
  assert (HLnext : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 (j + 1) Ccur) S0_2 R0_2 learnt0_2).
  { unfold resolve_learnt, resolve_new_lits in *.
    rewrite Hprefix, filter_app. cbn [filter].
    rewrite Hbelow. cbn [andb filter].
    rewrite HLold. rewrite !app_nil_r. reflexivity. }
  assert (Hinv : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase
      Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2
      learnt_scan_2 words_scan_2 cnt).
  { msat_analyze_scan_unchanged_close phase H_Ccur HSnext HLnext. }
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_30 : solver_analyze_entail_wit_30.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mstats) (ms_tagged Mstats) ) as H_analysis_tags_exact.
  pose proof (analyze_clear_start__analyze anz_n (ms_tags Mstats) (ms_tagged Mstats)
    H_analysis_tags_exact) as Hstart.
  sep_apply_l_atomic (store_int_undef_store_int (&( "j")) j).
  sep_apply_l_atomic (store_uint_undef_store_uint (&( "minl")) minl_v).
  destruct (Z.eq_dec (Zlength (ms_tagged Mstats)) 0) as [Hzero | Hnonzero].
  - Left. Exists (ms_tags Mstats).
    split_pure_spatial.
    + cancel (&( "minl") # UInt |->_).
      cancel.
    + split_pures; dump_pre_spatial; solve [auto | lia].
  - assert (Hpositive : 0 < Zlength (ms_tagged Mstats)) by lia.
    pose proof (analysis_tags_exact_index_range__analyze
      anz_n (ms_tags Mstats) (ms_tagged Mstats) 0 H_analysis_tags_exact ltac:(lia)) as Hhead.
    Right. Exists (ms_tags Mstats).
    split_pure_spatial.
    + cancel (&( "minl") # UInt |->_).
      cancel.
    + split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_analyze_entail_wit_32 : solver_analyze_entail_wit_32.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_clear_loop_inv anz_n i (ms_tagged Mstats) (ms_tags Mstats) tags_now ) as
      H_analyze_clear_loop_inv.
  pose proof (analyze_clear_done__analyze anz_n i (ms_tagged Mstats) (ms_tags Mstats) tags_now
    H_analyze_clear_loop_inv ltac:(lia)) as Hdone.
  sep_apply (Veci.rep_ptr_rep (&( s_pre # "solver_t" ->ₛ "tagged")) tagged
    (sublist 0 0 (ms_tagged Mstats))).
  Exists (sublist 0 0 (ms_tagged Mstats)) tags_now.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_solver_analyze_partial_solve_wit_35_pure : solver_analyze_partial_solve_wit_35_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( retval_2 = clause_hdr_word is_learnt_now (Zlength clause_words) % 2 ) as H_retval_2.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase_2 c Ccur_2 words_2 cnt ind p
      ) as H_analyze_resolution_loop_inv.
  bind_fact ( 0 < c ) as H_c.
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  assert (Hlearnt_now : is_learnt_now = msat_true).
  { destruct is_learnt_now.
    - reflexivity.
    - unfold clause_hdr_word in H_retval_2.
      remember (Zlength clause_words) as z.
      assert (Hz : 0 <= z).
      { subst z. apply Zlength_nonneg. }
      destruct z as [|zpos|zneg].
      + change (retval_2 = 0) in H_retval_2. lia.
      + simpl in H_retval_2.
        assert (Hrem : Z.rem (Z.pos (xO zpos)) 2 = 0).
        { rewrite Pos2Z.inj_xO, Z.mul_comm. apply Z.rem_mul. lia. }
        rewrite Hrem in H_retval_2.
        lia.
      + lia. }
  unfold msat_true in Hlearnt_now.
  pose proof H_analyze_resolution_loop_inv as Hloop.
  unfold analyze_resolution_loop_inv in Hloop.
  destruct Hloop as [Hready _].
  destruct (analysis_cancel_ready_db_tags__analyze
    anz_n anz_F anz_A_arr K Mcur anz_focus Hready) as [Hprob [Hlearnt Hcla]].
  split_pures.
  - dump_pre_spatial. exact H_is_tag.
  - dump_pre_spatial. exact H_c.
  - dump_pre_spatial. exact Hcla.
  - unfold analysis_clause_remainder.
    Split.
    + Intros_p Hbinary.
      dump_pre_spatial.
      destruct Hbinary as [_ [Hnotlearnt _]].
      congruence.
    + Intros_p Hreal.
      unfold clause_db_pair_remainder.
      Split.
      * Intros co pre post.
        dump_pre_spatial.
        match goal with
        | Hfocus : ms_prob Mcur = _ /\ _ |- _ =>
            destruct Hfocus as [Hdecomp [_ Htag]]
        end.
        assert (Hin : In (c, co) (ms_prob Mcur)).
        { rewrite Hdecomp. apply in_or_app. right. left. reflexivity. }
        unfold prob_db in Hprob.
        rewrite Forall_forall in Hprob.
        specialize (Hprob _ Hin).
        simpl in Hprob.
        congruence.
      * Intros co pre post.
        dump_pre_spatial.
        match goal with
        | Hfocus : ms_learnt Mcur = _ /\ _ |- _ =>
            destruct Hfocus as [Hdecomp _]
        end.
        unfold db_words.
        rewrite Hdecomp, map_app.
        simpl.
        apply in_or_app. right. left. reflexivity.
  - dump_pre_spatial. exact Hlearnt_now.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_71_learnt_pure : solver_analyze_partial_solve_wit_71_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_analyze_word_range_context anz_n j clause_words2.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_98_learnt_pure : solver_analyze_partial_solve_wit_98_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_117_learnt_pure : solver_analyze_partial_solve_wit_117_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Forall_Znth_elim _ _ _ 0 j PreH24 (conj PreH25 PreH26)) as Hlit.
  unfold lit_wf_c in Hlit.
  replace (j - 0) with j by lia.
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_safety_wit_2 : solver_analyze_safety_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K M0 anz_focus ) as H_analysis_cancel_ready.
  destruct H_analysis_cancel_ready as [Mentry [Hcancel [Hequiv Hrest]]].
  destruct Hcancel as [[Hpending Hweak] Hcancel_rest].
  destruct K; cbn in Hweak.
  - pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    unfold analysis_core_equiv in Hequiv.
    assert (Hbounds :
      ms_qtail M0 - 1 <= INT_MAX /\ INT_MIN <= ms_qtail M0 - 1) by lia.
    (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - pose proof (msa_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    unfold analysis_core_equiv in Hequiv.
    assert (Hbounds :
      ms_qtail M0 - 1 <= INT_MAX /\ INT_MIN <= ms_qtail M0 - 1) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_safety_wit_37_learnt : solver_analyze_safety_wit_37_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 msat_analyze_scan_count_bound.
Qed.


Lemma proof_of_solver_analyze_safety_wit_51_learnt : solver_analyze_safety_wit_51_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures.
 - dump_pre_spatial. msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_analyze_safety_wit_53_learnt : solver_analyze_safety_wit_53_learnt.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pures; dump_pre_spatial.
 - msat_analyze_bound_scan_index_by_nodup anz_n Ccur j Hinv clause_words2.
 - lia.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_2 : solver_analyze_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hready : analysis_cancel_ready ?n ?F ?A ?K ?Msol ?focus |-
      solver_rep_analyze_at ?s ?Msol ?reasons ?levels ?trail ?tags ?wl |-- _ =>
      let Hsize := fresh "Hsize" in
      pose proof (analysis_cancel_ready_reason_core n F A K Msol focus Hready)
        as [Hsize _];
      sep_apply (solver_rep_analyze_at_open
        s Msol n reasons levels trail tags wl (eq_sym Hsize))
  end.
  Intros activity orderpos.
  Exists activity orderpos.
  unfold msat_false.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_8 : solver_analyze_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (CharArray.full_Zlength tags anz_n
    (replace_Znth (lit_var_c q) 1 (ms_tags Mcur))).
  Exists (replace_Znth (lit_var_c q) 1 (ms_tags Mcur)).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_33 : solver_analyze_which_implies_wit_33.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Forall_Znth_elim
    _ _ words_compact 0 i PreH1 ltac:(lia)) as Hwf.
  replace (i - 0) with i by lia.
  pose proof (lit_var_c_in_range anz_n _ Hwf) as Hrange.
  entailer!.
Qed.


Lemma proof_of_solver_lit_removable_entail_wit_6_2 : solver_lit_removable_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  bind_fact ( retval_8 = lit_var_c retval_7 ) as H_retval_8.
  bind_fact ( retval_7 = tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) ) as
      H_retval_7.
  bind_fact ( 0 <= lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) ) as
      H_lit_var_c.
  bind_fact ( lit_var_c (tag_lit (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0)) < lrm_n )
      as H_lit_var_c_2.
  bind_fact ( top = Zlength (ms_tagged M0) ) as H_top.
  bind_fact ( analysis_tags_exact lrm_n tags_now tagged_now ) as H_analysis_tags_exact.
  replace (retval_5 - 1) with (Zlength stack_now - 1) in * by lia.
  subst stack_after.
  assert (Hrollback : removable_rollback_inv lrm_n top top (ms_tagged M0)
    (ms_tags M0) tags_now tagged_now tags_now).
  { eapply removable_rollback_start__lit_removable; eauto. }
  assert (Htop0 : 0 <= top).
  { rewrite H_top. apply Zlength_nonneg. }
  assert (Hr8 : 0 <= retval_8 < lrm_n).
  { rewrite H_retval_8, H_retval_7. split; [exact H_lit_var_c | exact H_lit_var_c_2]. }
  lazymatch type of (store_int_undef_store_int (&( "v")) retval_8) with
  | ?A1 |-- ?B1 =>
  lazymatch type of (store_ptr_undef_store_ptr (&( "c"))
    (Znth (Znth (Zlength stack_now - 1) stack_now 0)
      (ms_reason_words M0) 0)) with
  | ?A2 |-- ?B2 =>
  lazymatch type of (store_int_undef_store_int (&( "v"))
    (Znth (Zlength stack_now - 1) stack_now 0)) with
  | ?A3 |-- ?B3 =>
  lazymatch type of (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr) with
  | ?A4 |-- ?B4 =>
  lazymatch type of (store_ptr_undef_store_ptr (&( "levels")) levels_ptr) with
  | ?A5 |-- ?B5 =>
      assert (Hundef : A1 ** A2 ** A3 ** A4 ** A5 |-- B1 ** B2 ** B3 ** B4 ** B5)
  end end end end end.
  { sep_apply (store_int_undef_store_int (&( "v")) retval_8).
    sep_apply (store_ptr_undef_store_ptr (&( "c"))
      (Znth (Znth (Zlength stack_now - 1) stack_now 0)
        (ms_reason_words M0) 0)).
    sep_apply (store_int_undef_store_int (&( "v"))
      (Znth (Zlength stack_now - 1) stack_now 0)).
    sep_apply
      (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr).
    sep_apply
      (store_ptr_undef_store_ptr (&( "levels")) levels_ptr).
    cancel. }
  sep_apply Hundef. clear Hundef.
  msat_restore_array_read PtrArray.missing_i_merge_to_seg
    reasons_ptr retval_8 lrm_n (ms_reason_words M0).
  msat_restore_array_read IntArray.missing_i_merge_to_seg
    levels_ptr retval_8 lrm_n (mt_levels (ms_core M0)).
  msat_restore_array_read CharArray.missing_i_merge_to_seg
    tags_ptr retval_8 lrm_n tags_now.
  sep_apply (Veci.rep_ptr_rep (&( s_pre # "solver_t" ->ₛ "stack")) p
    (sublist 0 (Zlength stack_now - 1) stack_now)).
  destruct (Z_lt_ge_dec top (Zlength tagged_now)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth top tagged_now 0 < lrm_n).
    { unfold analysis_tags_exact in H_analysis_tags_exact.
      destruct H_analysis_tags_exact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists tags_now.
    msat_manual_entailer_with ltac:(lia).
  - assert (Htople : top <= Zlength tagged_now).
    { unfold removable_rollback_inv in Hrollback. tauto. }
    assert (Htopeq : top = Zlength tagged_now) by lia.
    Right. Exists tags_now.
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_10_1 : solver_lit_removable_entail_wit_10_1.
Proof.
  (LLM_pre_process ltac:(lia || nia || int_auto));
  subst retval;
  bind_fact ( top = Zlength (ms_tagged M0) ) as Htop;
  bind_fact ( lits = clause_lits_addr c ) as Hlits;
  bind_fact ( analysis_tags_exact lrm_n tags_scan tagged_scan ) as Htags;
  bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan stack_scan
    tags_scan tagged_scan Cnext v c i ) as Hscan;
  replace (i - 0) with i in * by lia;
  replace (retval_3 - 0) with retval_3 in * by lia;
  assert (Hdfs : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_scan tagged_scan (v :: stack_scan) done_scan)
    by (unfold removable_reason_scan_inv in Hscan; tauto);
  assert (Hrollback : removable_rollback_inv lrm_n top top (ms_tagged M0)
    (ms_tags M0) tags_scan tagged_scan tags_scan)
    by (eapply removable_rollback_start__lit_removable; eauto);
  assert (Htop0 : 0 <= top) by (rewrite Htop; apply Zlength_nonneg);
  assert (Hundef :
    ((&( "v")) # Int |-> retval_3) ** ((&( "i")) # Int |-> i) **
    ((&( "v")) # Int |-> v) ** ((&( "reasons")) # Ptr |-> reasons_ptr) **
    ((&( "levels")) # Ptr |-> levels_ptr) |--
    ((&( "v")) # Int |->_) ** ((&( "i")) # Int |->_) **
    ((&( "v")) # Int |->_) ** ((&( "reasons")) # Ptr |->_) **
    ((&( "levels")) # Ptr |->_))
    by (sep_apply (store_int_undef_store_int (&( "v")) retval_3);
        sep_apply (store_int_undef_store_int (&( "i")) i);
        sep_apply (store_int_undef_store_int (&( "v")) v);
        sep_apply (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr);
        sep_apply (store_ptr_undef_store_ptr (&( "levels")) levels_ptr);
        cancel);
  sep_apply Hundef;
  rewrite Hlits;
  destruct (Z_lt_ge_dec top (Zlength tagged_scan)) as [Hlt | Hge];
  [ assert (Htagvar : 0 <= Znth top tagged_scan 0 < lrm_n)
      by (unfold analysis_tags_exact in Htags;
          destruct Htags as [_ [_ [Hbounds _]]];
          eapply Forall_Znth_elim; [exact Hbounds | lia]);
    Left; Exists tags_scan;
    msat_manual_entailer_with ltac:(lia)
  | assert (Htople : top <= Zlength tagged_scan)
      by (unfold removable_rollback_inv in Hrollback; tauto);
    assert (Htopeq : top = Zlength tagged_scan) by lia;
    Right; Exists tags_scan;
    msat_manual_entailer_with ltac:(lia) ].
Qed.



Lemma proof_of_solver_lit_removable_partial_solve_wit_11_pure : solver_lit_removable_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_lit_var_parity_bounds l_pre.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_3 : solver_lit_removable_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst v.
  bind_fact ( removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now tagged_now stack_now done ) as
    H_removable_dfs_loop_inv.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( 0 < Zlength stack_now ) as H_Zlength.
  destruct (removable_dfs_last_reason__lit_removable
    lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now tagged_now stack_now done
    H_removable_dfs_loop_inv H_Zlength) as [Cnext Htarget].
  destruct (analysis_cancel_ready_reason_core
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Hsize _].
  pose proof Htarget as Hrange.
  unfold reason_target_wf in Hrange.
  destruct Hrange as [Hvrange [_ [Hnonzero _]]].
  Exists Cnext. unfold removable_reason_focus.
  msat_manual_entailer_with ltac:(lia).
Qed.


