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
Lemma proof_of_solver_analyze_entail_wit_6 : solver_analyze_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  assert (Horderpos_len : Zlength orderpos1 = anz_n).
  { unfold order_heap_wf, heap_wf in H_order_heap_wf. cbn in H_order_heap_wf. tauto. }
  Exists var_inc1 activity1 heap1 orderpos1.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_4_learnt : solver_analyze_entail_wit_12_4_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
  bind_fact ( retval_9 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( Permutation (ms_order Mscan_2) heap1 ) as H_Permutation.
  bind_fact ( retval_7 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_7.
  bind_fact ( retval_6 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_6.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= lit_var_c (Znth (j - 0) clause_words2 0) ) as H_lit_var_c.
  bind_fact ( lit_var_c (Znth (j - 0) clause_words2 0) < anz_n ) as H_lit_var_c_2.
  bind_fact ( Znth (lit_var_c (Znth (j - 0) clause_words2 0)) (ms_tags Mscan_2) 0 = 0 ) as H_Znth_2.
  bind_fact ( analysis_core_equiv M0 Mscan_2 ) as H_analysis_core_equiv.
  bind_fact ( msolver_seed_shadow Mscan_2 ) as H_msolver_seed_shadow.
  bind_fact ( phase = AnalyzeSelected ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hready & Htags0 & Hperm0 & Hcnt0 & Hden0 & Hwords0).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hvalid & HSscan & HRscan & HLscan).
  assert (HcoreAct : analysis_core_equiv Mact Mscan_2)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hjlo : 1 <= j)
    by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HviewAct : msolver_view anz_n Mscan_2 = msolver_view anz_n Mact)
    by (symmetry; apply ms_analysis_core_equiv_view; exact HcoreAct).
  set (q := Znth j clause_words2 0).
  set (qv := lit_var_c q).
  assert (Hqrange : 0 <= qv < anz_n).
  { unfold qv, q.
    replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hqcell0 : Znth qv (ms_tags Mscan_2) 0 = 0).
  { unfold qv, q. replace (j - 0) with j in H_Znth_2 by lia. exact H_Znth_2. }
  assert (Hqnotghost : ~ In qv (analyze_tags Sscan_2 Rscan_2 learnt_scan_2))
    by (apply (ms_analyze_var_untagged anz_n (ms_tags Mscan_2)
          (ms_tagged Mscan_2));
        [exact Htags0 | exact Hperm0 | exact Hqrange | rewrite Hqcell0; lia]).
  assert (Hqneqx : qv <> x_2).
  { intro Heq. apply Hqnotghost. rewrite Heq, HRscan. unfold analyze_tags.
    apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
  assert (HqinC : In (lit_denote q) Ccur).
  { rewrite H_Ccur. unfold lits_denote. apply in_map. unfold q.
    apply Znth_In. split; assumption. }
  assert (Hqvar : literal_var (lit_denote q) = qv)
    by (unfold qv; apply lit_var_c_denote).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  assert (Hraw : Znth qv (mt_levels (ms_core Mscan_2)) 0 =
    Zlength (mt_lim (ms_core Mscan_2))).
  { rewrite H_retval_10, H_retval_11 in H_Znth.
    replace (j - 0) with j in H_Znth by lia.
    replace (lit_var_c (Znth j clause_words2 0) - 0) with qv in H_Znth
      by (unfold qv, q; lia).
    exact H_Znth. }
  assert (HvalidScan : reason_valid (msolver_view anz_n Mscan_2) x_2 Ccur)
    by (rewrite HviewAct; exact Hvalid).
  destruct (msat_analyze_e12_scan_lit_current anz_n Mscan_2 Ccur
      (lit_denote q) qv x_2 HvalidScan HqinC Hqvar Hqneqx Htrailwf Hraw)
    as (HqcurScan & HqbelowScan).
  assert (HqcurrentAct :
    at_current_level_b (msolver_view anz_n Mact) (lit_denote q) = true)
    by (rewrite <- HviewAct; exact HqcurScan).
  assert (Hqbelow :
    below_current_b (msolver_view anz_n Mact) (lit_denote q) = false)
    by (rewrite <- HviewAct; exact HqbelowScan).
  assert (Hsub : sublist 1 (j + 1) Ccur =
    sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hqnotseen : zmem qv (analyze_tags S0_2 R0_2 learnt0_2) = false)
    by (exact (msat_analyze_e12_notin_initial (msolver_view anz_n Mact) Ccur
          j x_2 qv S0_2 R0_2 Sscan_2 Rscan_2 learnt0_2 learnt_scan_2
          Hqnotghost Hqneqx HSscan HRscan HLscan)).
  destruct (msat_analyze_e12_resolve_step_tag (msolver_view anz_n Mact) Ccur
      j (lit_denote q) qv x_2 S0_2 R0_2 Sscan_2 learnt0_2 learnt_scan_2
      Hqvar Hsub HqcurrentAct Hqbelow Hqnotseen HSscan HLscan)
    as (HSnext & HLnext).
  assert (HtagsNew : analysis_tags_exact anz_n
      (replace_Znth qv 1 (ms_tags Mscan_2)) (ms_tagged Mscan_2 ++ (qv :: nil)))
    by (apply ms_analysis_tags_exact_snoc;
        [exact Htags0 | exact Hqrange | rewrite Hqcell0; lia]).
  assert (HpermNew : Permutation (ms_tagged Mscan_2 ++ (qv :: nil))
      (analyze_tags (Sscan_2 ++ (qv :: nil)) Rscan_2 learnt_scan_2))
    by (apply ms_analyze_tags_perm_snoc_s; exact Hperm0).
  set (Mnext := analyze_tag_step_msolver Mscan_2
    (replace_Znth qv 1 (ms_tags Mscan_2))
    (ms_tagged Mscan_2 ++ (qv :: nil))
    activity1 orderpos1 heap1 var_inc1).
  assert (HreadyNext :
    analysis_cancel_ready anz_n anz_F anz_A_arr K Mnext anz_focus)
    by (unfold Mnext; apply msat_analyze_e12_tag_ready_perm;
        [exact Hready | exact H_order_heap_wf | exact H_Permutation]).
  msat_analyze_tag_step_carry Mnext Mact M0 HcoreAct
    H_analysis_core_equiv H_msolver_seed_shadow.
  assert (HscanNext : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact
      Mnext anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (qv :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  assert (Hret6 : retval_6 = qv)
    by (rewrite H_retval_6; replace (j - 0) with j by lia; reflexivity).
  assert (Hret7 : retval_7 = qv)
    by (rewrite H_retval_7; replace (j - 0) with j by lia; reflexivity).
  assert (HremainderNext :
    analysis_clause_remainder Mnext c is_learnt2 clause_words2 =
      analysis_clause_remainder Mscan_2 c is_learnt2 clause_words2)
    by reflexivity.
  assert (HframeNext :
    solver_analyze_frame s_pre Mnext anz_wl = solver_analyze_frame s_pre Mscan_2 anz_wl)
    by (unfold Mnext; apply solver_analyze_frame_analyze_tag_step).
  assert (HinertNext :
    solver_analyze_inert_at s_pre Mnext anz_n activity_ptr_scan_2
      orderpos_ptr_scan_2 reasons levels_ptr trail tags
    = solver_analyze_inert_at s_pre Mscan_2 anz_n activity_ptr_scan_2
      orderpos_ptr_scan_2 reasons levels_ptr trail tags)
    by (unfold Mnext; apply solver_analyze_inert_at_tag_step).
  rewrite Hret6, Hret7.
  Right.
  Exists activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ qv :: nil)
    Rscan_2 learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - rewrite HremainderNext, HframeNext, HinertNext.
    unfold Mnext, analyze_tag_step_msolver, msolver_analysis_update.
    cbn [ms_qtail ms_cap ms_activity ms_orderpos ms_reason_words ms_core ms_tags ms_order ms_stack ms_tagged ms_var_inc ms_cla_inc ms_learnt ms_prob ms_binary ms_binary_lits ms_stats].
    msat_cancel_sound.
    sep_apply CharArray.full_to_seg.
    msat_cancel_sound; cancel.
  - msat_manual_entailer_with ltac:(first [assumption | lia | congruence]).
Qed.


Lemma proof_of_solver_analyze_entail_wit_14_1 : solver_analyze_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia).
  Exists words1 S1 R3 learnt1 Mtag; msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_analyze_entail_wit_14_3_learnt : solver_analyze_entail_wit_14_3_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame words_done Sdone Rdone learnt_done Mdone.
Qed.


Lemma proof_of_solver_analyze_entail_wit_31 : solver_analyze_entail_wit_31.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( analyze_clear_loop_inv anz_n i (ms_tagged Mstats) (ms_tags Mstats) tags_now_2 ) as
      H_analyze_clear_loop_inv.
  replace (i - 0) with i in * by lia.
  assert (Hstep : analyze_clear_loop_inv anz_n (i + 1)
    (ms_tagged Mstats) (ms_tags Mstats)
    (replace_Znth (Znth i (ms_tagged Mstats) 0) 0 tags_now_2)).
  { eapply analyze_clear_step__analyze; eauto. }
  sep_apply (Veci.rep_ptr_intro &(s_pre # "solver_t" ->ₛ "tagged") tagged (ms_tagged Mstats) cap _ _ _ eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  destruct (Z.eq_dec (i + 1) (Zlength (ms_tagged Mstats))) as [Heq | Hneq].
  - Left. Exists (replace_Znth (Znth i (ms_tagged Mstats) 0) 0 tags_now_2).
    sep_apply_l_atomic (CharArray.missing_i_merge_to_seg
      tags 0 (Znth i (ms_tagged Mstats) 0) anz_n 0 tags_now_2).
    (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
    rewrite Z.sub_0_r.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - assert (Hlt : i + 1 < Zlength (ms_tagged Mstats)) by lia.
    pose proof (analysis_tags_exact_index_range__analyze
      anz_n (ms_tags Mstats) (ms_tagged Mstats) (i + 1)
      ltac:(unfold analyze_clear_loop_inv in H_analyze_clear_loop_inv; tauto) ltac:(lia)) as Hnext.
    Right. Exists (replace_Znth (Znth i (ms_tagged Mstats) 0) 0 tags_now_2).
    sep_apply_l_atomic (CharArray.missing_i_merge_to_seg
      tags 0 (Znth i (ms_tagged Mstats) 0) anz_n 0 tags_now_2).
    (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
    rewrite Z.sub_0_r.
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_analyze_partial_solve_wit_36_learnt_pure : solver_analyze_partial_solve_wit_36_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( In c (db_words (ms_learnt Mcur)) ) as H_In.
  bind_fact ( msat_fp32_nonnegative (ms_cla_inc Mcur) ) as H_msat_fp32_nonnegative.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase_2 c Ccur_2 words_2 cnt ind p
      ) as H_analyze_resolution_loop_inv.
  pose proof H_analyze_resolution_loop_inv as Hloop.
  unfold analyze_resolution_loop_inv in Hloop.
  destruct Hloop as [Hready _].
  destruct (analysis_cancel_ready_db_tags__analyze
    anz_n anz_F anz_A_arr K Mcur anz_focus Hready) as [_ [Hlearnt _]].
  split_pures.
  - dump_pre_spatial. exact H_In.
  - dump_pre_spatial. exact H_msat_fp32_nonnegative.
  - dump_pre_spatial. exact Hlearnt.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_81_learnt_pure : solver_analyze_partial_solve_wit_81_learnt_pure.
Proof.
  (LLM_pre_process ltac:(lia || int_auto)); msat_analyze_clause_word_range anz_n j clause_words2 0.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_99_learnt_pure : solver_analyze_partial_solve_wit_99_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_107_learnt_pure : solver_analyze_partial_solve_wit_107_learnt_pure.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_close_clause_word_range_any_index anz_n clause_words2 j.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_140_pure : solver_analyze_partial_solve_wit_140_pure.
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
  assert (Htwo : 2 * anz_n <= INT_MAX).
  {
    destruct Hready as [Mbase [[[_ Hinv] _] _]].
    destruct K as [A_inst | A_proc]; cbn in Hinv;
      [ pose proof (msw_size Hinv) as Hsize; pose proof (msw_shape Hinv) as Hshape
      | pose proof (msa_size Hinv) as Hsize; pose proof (msa_shape Hinv) as Hshape ];
      unfold solver_shape in Hshape; lia.
  }
  unfold lit_wf_c in Hlit.
  split_pures; dump_pre_spatial;
    replace (ind - 1 + 1 - 0) with (ind - 1 + 1) by lia;
    lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_187_pure : solver_analyze_partial_solve_wit_187_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Forall_Znth_elim _ _ _ 0 i PreH5 (conj PreH6 PreH7)) as Hlit.
  unfold lit_wf_c in Hlit.
  match goal with H : analysis_cancel_ready _ _ _ _ _ _ |- _ => rename H into Hready end.
  unfold analysis_cancel_ready in Hready.
  destruct Hready as [Mbase [Hprop [Hequiv _]]].
  unfold propagation_cancel_ready in Hprop.
  destruct Hprop as [Hweak _].
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as [_ Hweak].
  assert (Htwo_n : 2 * anz_n <= INT_MAX) by
    (destruct K as [A_inst | A_proc]; cbn in Hweak;
     [ pose proof (msw_shape Hweak) as Hshape;
       pose proof (msw_size Hweak) as Hsize;
       unfold solver_shape in Hshape;
       destruct Hshape as [_ [_ [Htwo _]]];
       rewrite Hsize; exact Htwo
     | pose proof (msa_shape Hweak) as Hshape;
       pose proof (msa_size Hweak) as Hsize;
       unfold solver_shape in Hshape;
       destruct Hshape as [_ [_ [Htwo _]]];
       rewrite Hsize; exact Htwo ]).
  apply _derivable1_andp_intros; dump_pre_spatial; rewrite Z.sub_0_r; lia.
Qed.



Lemma proof_of_solver_analyze_which_implies_wit_25 : solver_analyze_which_implies_wit_25.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Forall_Znth_elim
    _ _ words_min 0 i PreH1 ltac:(lia)) as Hwf.
  replace (i - 0) with i by lia.
  pose proof (lit_var_c_in_range anz_n _ Hwf) as Hrange.
  entailer!.
Qed.


Lemma proof_of_solver_analyze_which_implies_wit_25_split_goal_1 : solver_analyze_which_implies_wit_25_split_goal_1.
Abort.


Lemma proof_of_solver_analyze_which_implies_wit_25_split_goal_2 : solver_analyze_which_implies_wit_25_split_goal_2.
Abort.


Lemma proof_of_solver_analyze_which_implies_wit_30 : solver_analyze_which_implies_wit_30.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try rename anz_n into n.
  try rename anz_F into F.
  try rename anz_A_arr into A_arr.
  try rename anz_focus into focus.
  bind_fact ( analysis_core_equiv M0 Mstats ) as H_analysis_core_equiv.
  bind_fact ( msolver_seed_shadow Mstats ) as H_msolver_seed_shadow.
  bind_fact ( analysis_cancel_ready n F A_arr K Mstats focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert n F Mstats words_compact ) as H_analyze_clause_cert.
  bind_fact ( Zlength tagged_list = 0 ) as H_Zlength.
  bind_fact ( analysis_tags_exact n tags_final tagged_list ) as H_analysis_tags_exact.
  assert (Htagged_nil : tagged_list = nil).
  { destruct tagged_list as [|a rest]; [reflexivity|].
    rewrite Zlength_cons in H_Zlength.
    pose proof (Zlength_nonneg rest). lia. }
  subst tagged_list.
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K Mstats focus H_analysis_cancel_ready) as [Hsize _].
  assert (Htags_zero : tags_final = repeat_Z 0 n)
    by exact (analysis_tags_exact_nil_zero n tags_final
                H_analysis_tags_exact).
  unfold analysis_tags_exact in H_analysis_tags_exact.
  destruct H_analysis_tags_exact as
    [Htags_len [Hnodup [Hrange [Hbits Hiff]]]].
  assert (Hn_nonneg : 0 <= n).
  { rewrite <- Htags_len. apply Zlength_nonneg. }
  assert (Hframe_lengths_keep :
    solver_tags_tagged_frame_at s Mstats reasons levels trail anz_wl |--
      “ Zlength (ms_activity Mstats) = ms_size Mstats /\
        Zlength (ms_orderpos Mstats) = ms_size Mstats /\
        Zlength (ms_stats Mstats) = 11 ” &&
      solver_tags_tagged_frame_at s Mstats reasons levels trail anz_wl).
  { unfold solver_tags_tagged_frame_at at 1.
    sep_apply
      (solver_removable_frame_lengths_keep__lit_removable
        s Mstats trail anz_wl).
    Intros_p Hframe_lengths.
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
    unfold solver_tags_tagged_frame_at.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]). }
  sep_apply Hframe_lengths_keep.
  Intros_p Hframe_lengths.
  destruct Hframe_lengths as
    (Hactivity_len & Horder_len & Hstats_len).
  pose proof H_analysis_cancel_ready as Hready.
  unfold analysis_cancel_ready in Hready.
  destruct Hready as
    [Mbase [Hprop [Hequiv [Hheap [Hcovers [Hcurrent [Hfocus Hcla]]]]]]].
  unfold propagation_cancel_ready in Hprop.
  destruct Hprop as [Hweak _].
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as [_ Hweak].
  assert (Hshape_base : solver_shape Mbase).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_shape Hweak).
    - exact (msa_shape Hweak). }
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Ebinary & Ebinarylits &
     Ewm & Emodel & Ecladecay & Eseed &
     Ependingq & Epending & Esimpassigns & Esimpprops).
  set (Mclear := msolver_scratch_update Mstats tags_final nil (ms_stack Mstats)).
  assert (Htags_size : Zlength tags_final = ms_size Mstats).
  { rewrite Htags_len. exact Hsize. }
  assert (Hshape : solver_shape Mclear).
  { unfold solver_shape in Hshape_base.
    rewrite <- Esize, <- Ecap, <- Eqtail, <- Ecore, <- Eroot,
      <- Ewords, <- Ebinary, <- Ebinarylits, <- Ewm,
      <- Ependingq, <- Epending in Hshape_base.
    destruct Hshape_base as
      (Hsrange & Hcapmax & Htwice & Hassigns & Hlevels_len &
       Hreasons_len & Horder_old & Hactivity_old & Htags_old &
       Htrail_len & Hqhead_range & Hpending_range & Hpending_flag &
       Hpending_case & Hqtail_range & Hwm_len &
       Hbinary_lits_len & Hstats_old & Hroot_nonneg &
       Hbinary_nonzero & Hbinary_even).
    subst Mclear.
    unfold solver_shape, msolver_scratch_update, msolver_analysis_update. cbn.
    repeat split; tauto. }
  assert (Hcore : analysis_core_equiv M0 Mclear).
  { subst Mclear.
    change (analysis_core_equiv M0 Mstats).
    exact H_analysis_core_equiv. }
  assert (Hseed : msolver_seed_shadow Mclear).
  { subst Mclear.
    change (msolver_seed_shadow Mstats).
    exact H_msolver_seed_shadow. }
  assert (Hcancel : analysis_cancel_ready n F A_arr K Mclear focus).
  { subst Mclear.
    change (analysis_cancel_ready n F A_arr K Mstats focus).
    exact H_analysis_cancel_ready. }
  assert (Hcert : analyze_clause_cert n F Mclear words_compact).
  { subst Mclear.
    change (analyze_clause_cert n F Mstats words_compact).
    exact H_analyze_clause_cert. }
  Exists Mclear.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_rep_analyze_at, solver_rep_at,
      solver_tags_tagged_frame_at, solver_removable_frame_at,
      solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
      solver_trail_array_rep, solver_scalars_rep, solver_vecs_rep,
      solver_ptrs_rep, solver_var_arrays_rep, clause_new_scalars_frame.
  Intros act asg opos.
  Exists act asg opos.
  subst Mclear. unfold msolver_scratch_update, msolver_analysis_update. cbn.
  rewrite Hsize.
  unfold solver_fp_rep, DoubleArray.seg, IntArray.seg,
    PtrArray.seg, CharArray.seg.
  cbn.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_lit_removable_entail_wit_13_2 : solver_lit_removable_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( Znth retval_7 tags_now_2 0 <> 0 ) as H_Znth.
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
  bind_fact ( analysis_tags_exact lrm_n tags_now_2 tagged_now_2 ) as H_analysis_tags_exact.
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
  all: (assert (Hseen :
    In (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) tagged_now_2) by
    (eapply analysis_tags_exact_nonzero_in__lit_removable;
    [exact H_analysis_tags_exact | lia |
     exact H_Znth]));
    (assert (Hr : reason_of (msolver_view lrm_n M0) v = Some Cnext) by
    (eapply removable_reason_focus_view__lit_removable;
    [exact H_analysis_cancel_ready | exact H_removable_reason_focus])).
  all: (assert (Hside : forall q, In q Cnext -> literal_var q <> v ->
    level_of (msolver_view lrm_n M0) (literal_var q) = Some 0 \/
    In (literal_var q) (ms_tagged M0) \/
    In (literal_var q) (v :: done_2) \/ In (literal_var q) stack_after) by
    (eapply tagged_reason_side_seen__lit_removable;
    [exact H_analysis_cancel_ready | exact Hloop_top | exact H_removable_reason_focus | exact H_is_tag |
     exact Hseen]));
    (assert (Hloop_done :
    removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0)
      tags_now_2 tagged_now_2 stack_after (v :: done_2)) by
    (eapply removable_dfs_loop_inv_finish_head__lit_removable;
    [exact Hloop_top | exact Hr | exact Hside])).
  all: assert (Hstack_incl :
    incl stack_after (map lit_var_c (mt_trail (ms_core M0)))) by
    (intros x Hx; apply H_incl; rewrite H_stack_now_2;
     apply in_or_app; left; exact Hx).
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



Lemma proof_of_solver_lit_removable_partial_solve_wit_28_pure : solver_lit_removable_partial_solve_wit_28_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) = msat_true ) as H_is_tag.
  unfold removable_reason_focus, reason_target_wf in *.
  destruct H_removable_reason_focus as [_ [_ [_ [_ Hkind]]]].
  destruct Hkind as [[Htag [Hpositive Hlit]] | [co [Htag [_ [_ _]]]]].
  - unfold lit_wf_c in Hlit.
    (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - unfold msat_true in H_is_tag.
    rewrite Htag in H_is_tag. discriminate.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_30_pure : solver_lit_removable_partial_solve_wit_30_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_lit_removable_retval_var_bounds retval retval_7 stack_now M0 lrm_n Hv Hw Hlo Hhi.
Qed.


Lemma proof_of_solver_lit_removable_partial_solve_wit_67_pure : solver_lit_removable_partial_solve_wit_67_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : removable_rollback_inv _ _ _ _ _ _ _ _ |- _ => unfold removable_rollback_inv in H end.
  assert (Htopj : top <= j) by tauto.
  assert (Htop_nonneg : 0 <= top) by tauto.
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_2_split_goal_spatial : solver_lit_removable_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_2_split_goal_1 : solver_lit_removable_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace (lit_var_c l - 0) with (lit_var_c l) by lia.
  reflexivity.
Qed.


Lemma proof_of_solver_lit_removable_which_implies_wit_2 : solver_lit_removable_which_implies_wit_2.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_solver_lit_removable_which_implies_wit_2_split_goal_spatial M0 lrm_n reasons_ptr l PreH1 PreH2).
- Goal_apply (proof_of_solver_lit_removable_which_implies_wit_2_split_goal_1 M0 lrm_n reasons_ptr l PreH1 PreH2).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_6_learnt : solver_analyze_entail_wit_12_6_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
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
  bind_fact ( phase = AnalyzeInitial ) as H_phase.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_initial_pack H_phase H_analyze_clause_scan_inv)
    as (Hcert & HSold & HLold).
  msat_analyze_tag_step_open v Mnext j clause_words2 activity1
    orderpos1 heap1 var_inc1 Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (EcoreScan : ms_core Mscan_2 = ms_core Mact).
  { unfold analysis_core_equiv in H_analysis_core_equiv. tauto. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
  destruct Hcert as [_ [Hfalse [HwfC [HndC [lcur [Hlcur Hlevcur]]]]]].
  destruct (eval_partial_false_shape _ _
    (Hfalse (lit_denote q) HqC)) as [b [Hass _]].
  assert (Eqv : literal_var (lit_denote q) = v)
    by (rewrite lit_var_c_denote; unfold q, v;
        replace (j - 0) with j by lia; reflexivity).
  assert (Hpermnew : Permutation (ms_tagged Mscan_2 ++ (v :: nil))
      (analyze_tags Sscan_2 Rscan_2
        (learnt_scan_2 ++ (lit_denote q :: nil))))
    by (rewrite <- Eqv; apply ms_analyze_tags_perm_snoc_l; exact Hpermold).
  assert (Hmt : mt_pv (ms_core Mscan_2) v = Some b).
  { rewrite mt_pv_nonneg by (unfold v; lia).
    rewrite EcoreScan. rewrite Eqv in Hass.
    exact Hass. }
  destruct (trail_pos (ms_core Mscan_2) v) as [rq|] eqn:Hrank.
  2: { pose proof (proj2 (view_unassigned_iff anz_n (ms_core Mscan_2) v Htrailwf)
         Hrank) as Hnone.
       rewrite Hmt in Hnone. discriminate. }
  msat_analyze_initial_level_readback v anz_n Mact Mscan_2 rq
    Hrank Htrailwf Eview H_retval_5 H_Znth_2 H_retval_10 H_retval_11 H_Znth.
  msat_analyze_offlevel_flags anz_n Mact q dq Hlevq Hdqne Eqv Eview.
  assert (Hwordlenold : Zlength words_scan_2 = 1 + Zlength learnt_scan_2)
    by (apply ms_learnt_words_len; assumption).
  assert (Hwordsnext : lits_denote (tl (words_scan_2 ++ (q :: nil))) =
      learnt_scan_2 ++ (lit_denote q :: nil))
    by (apply ms_learnt_words_snoc; assumption).
  msat_analyze_start_step_word q anz_n Mact Ccur j clause_words2 Sscan_2
    learnt_scan_2 H_Ccur H_j_2 HSold HLold Hat Hbelow.
  assert (Hwordlennew :
      1 <= Zlength (words_scan_2 ++ (q :: nil)) <= anz_n).
  { pose proof (ms_analyze_start_learnt_room anz_n (j + 1)
      (msolver_view anz_n Mact) Ccur lcur HwfC HndC Hlcur
      ltac:(rewrite msolver_view_current_level; exact Hlevcur)) as Hroom.
    rewrite <- HLnext, Zlength_app, Zlength_cons, Zlength_nil in Hroom.
    rewrite Zlength_app, Zlength_cons, Zlength_nil, Hwordlenold.
    pose proof (Zlength_nonneg learnt_scan_2). lia. }
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
    replace (j - 0) with j by lia.
    fold q.
    fold v in H_retval_7, H_retval_6.
    rewrite H_retval_7, H_retval_6.
    sep_apply CharArray.full_to_seg.
    cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_8_learnt : solver_analyze_entail_wit_12_8_learnt.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_analyze_open_at.
  intros.
  bind_fact ( Znth (retval_9 - 0) (mt_levels (ms_core Mscan_2)) 0 <> retval_10 ) as H_Znth.
  bind_fact ( retval_10 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
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
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Right.
  destruct (ms_analyze_scan_inv_pack H_analyze_clause_scan_inv)
    as (Hreadyold & Htagsold & Hpermold & Hcntold & Hwordsold & Hwordlower).
  destruct (ms_analyze_scan_selected_pack H_phase H_analyze_clause_scan_inv)
    as (Hinx & Hreason & HSold & ERscan & HLold).
  msat_analyze_tag_step_open v Mnext j clause_words2 activity1
    orderpos1 heap1 var_inc1 Hreadyold H_order_heap_wf H_u_2 Htagsold.
  assert (Eview : msolver_view anz_n Mact = msolver_view anz_n Mscan_2)
    by (apply ms_analysis_core_equiv_view; exact H_analysis_core_equiv).
  assert (Hnotcur : ~ In v (analyze_tags Sscan_2 Rscan_2 learnt_scan_2))
    by (apply (ms_analyze_var_untagged anz_n (ms_tags Mscan_2)
          (ms_tagged Mscan_2));
        [exact Htagsold | exact Hpermold | unfold v; lia | unfold v in *; lia]).
  assert (Hvneqx : v <> x_2).
  { intro Heq. apply Hnotcur. rewrite Heq.
    unfold analyze_tags. apply in_or_app. right.
    apply in_or_app. left. rewrite ERscan. simpl. tauto. }
  assert (Hnotinitial : ~ In v (analyze_tags S0_2 R0_2 learnt0_2)).
  { intro Hin. apply Hnotcur.
    unfold analyze_tags in *.
    rewrite !in_app_iff in *.
    destruct Hin as [HinS|[HinR|HinL]].
    - left. rewrite HSold. unfold resolve_S.
      apply in_or_app. left. apply In_zremove_iff. tauto.
    - right. left. rewrite ERscan. simpl. tauto.
    - right. right. rewrite HLold. unfold resolve_learnt.
      rewrite map_app. apply in_or_app. left. exact HinL. }
  assert (Hnotmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = false).
  { apply zmem_false_iff. exact Hnotinitial. }
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  set (q := Znth j clause_words2 0).
  assert (HqC : In (lit_denote q) Ccur)
    by (rewrite H_Ccur; apply lits_denote_in; unfold q;
        apply Znth_In; split; [exact H_j|exact H_j_2]).
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
    replace (j - 0) with j by lia.
    fold q.
    fold v in H_retval_7, H_retval_6.
    rewrite H_retval_7, H_retval_6.
    sep_apply CharArray.full_to_seg.
    cancel.
  - msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_12_10_learnt : solver_analyze_entail_wit_12_10_learnt.
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
  assert (Htags : analysis_tags_exact anz_n (ms_tags Mscan_2)
      (ms_tagged Mscan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (Hperm : Permutation (ms_tagged Mscan_2)
      (analyze_tags Sscan_2 Rscan_2 learnt_scan_2)) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv).
  assert (HSold : Sscan_2 = resolve_S (msolver_view anz_n Mact) x_2
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (HLold : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mact)
      (sublist 1 j Ccur) S0_2 R0_2 learnt0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (ERscan : Rscan_2 = x_2 :: R0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hinx : In x_2 S0_2) by (msat_analyze_scan_inv_part H_analyze_clause_scan_inv H_phase).
  assert (Hempty : sublist 1 1 Ccur = nil) by (apply ms_sublist_one_one_nil).
  assert (Hv : 0 <= v < anz_n).
  { unfold v, q. replace (j - 0) with j in H_lit_var_c, H_lit_var_c_2 by lia. lia. }
  assert (Hseen : In v (ms_tagged Mscan_2)).
  { eapply analysis_tags_exact_nonzero_in__lit_removable;
      [exact Htags | exact Hv |].
    intro Hzero. apply H_Znth.
    rewrite H_retval_4, !Z.sub_0_r. exact Hzero. }
  pose proof (Permutation_in v Hperm Hseen) as HinCur.
  assert (HinInitial : In v (analyze_tags S0_2 R0_2 learnt0_2)).
  { unfold analyze_tags in HinCur |- *.
    rewrite !in_app_iff in HinCur |- *.
    destruct HinCur as [HinS|[HinR|HinL]].
    - left. rewrite HSold in HinS.
      subst j. rewrite Hempty in HinS.
      unfold resolve_S, resolve_new_S in HinS.
      cbn in HinS. rewrite app_nil_r in HinS.
      apply In_zremove_iff in HinS. tauto.
    - rewrite ERscan in HinR. cbn in HinR.
      destruct HinR as [<-|HinR].
      + left. exact Hinx.
      + right. left. exact HinR.
    - right. right. rewrite HLold in HinL.
      subst j. rewrite Hempty in HinL.
      unfold resolve_learnt, resolve_new_lits in HinL.
      cbn in HinL. rewrite app_nil_r in HinL. exact HinL. }
  assert (Hmem : zmem v (analyze_tags S0_2 R0_2 learnt0_2) = true).
  { apply zmem_true_iff. exact HinInitial. }
  assert (Hprefix : sublist 1 (j + 1) Ccur =
      sublist 1 j Ccur ++ (lit_denote q :: nil))
    by (unfold q; exact (ms_analyze_sublist_snoc clause_words2 Ccur 1 j
          H_Ccur ltac:(lia) ltac:(lia) H_j_2)).
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


Lemma proof_of_solver_analyze_entail_wit_13_3_learnt : solver_analyze_entail_wit_13_3_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_3 anz_focus phase Ccur j ind S0_3 R0_3
      learnt0_3 x_3 Sscan_3 Rscan_3 learnt_scan_3 words_scan_3 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  pose proof H_analyze_clause_scan_inv as Hscan_original.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  subst phase Mact. cbn in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as
    [Hready [Hequiv_scan [Hind_scan [Hroot
    [HCwf [HCnodup [Hjscan [Hcnt [Hwords [Hden
    [Htags [Hperm Hselected]]]]]]]]]]]].
  destruct Hselected as
    [Hcntpos [Hjmin [HxS [Hrank [Hrankmax [Hainv
    [Hreason [Hvalid [Hentails [HS [HR Hlearnt]]]]]]]]]]].
  pose proof Hready as Hready_reason.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mscan_3 anz_focus Hready_reason) as
    [_ [Hmatch _]].
  pose proof Hready as Hready_entry.
  destruct Hready_entry as [Mready [Hcancel [Hequiv_entry _]]].
  destruct Hcancel as [Hweak _].
  destruct Hweak as [_ Hinv].
  assert (Hwfready : mtrail_wf anz_n (ms_core Mready)) by
    (destruct K;
     [exact (msw_trail_wf Hinv)|exact (msa_trail_wf Hinv)]).
  assert (Hdbwfready : db_wf anz_n (msolver_db Mready)) by
    (destruct K;
     [exact (msw_db_wf Hinv)|exact (msa_db_wf Hinv)]).
  assert (Hwf : mtrail_wf anz_n (ms_core Mscan_3)).
  { pose proof Hequiv_entry as Hequiv_wf.
    unfold analysis_core_equiv in Hequiv_wf.
    destruct Hequiv_wf as [_ [_ [_ [Ecore _]]]].
    rewrite Ecore. exact Hwfready. }
  assert (Hdbwf : db_wf anz_n (msolver_db Mscan_3)).
  { pose proof Hequiv_entry as Hequiv_db.
    unfold analysis_core_equiv in Hequiv_db.
    destruct Hequiv_db as
      [_ [_ [_ [_ [_ [_ [_ [Eprob [Elearnt _]]]]]]]]].
    unfold msolver_db in Hdbwfready |- *.
    rewrite Eprob, Elearnt. exact Hdbwfready. }
  cbn [msolver_view view_of assignment_rank] in Hrank.
  assert (Hidx : 0 <= ind + 1 <
    Zlength (mt_trail (ms_core Mscan_3))).
  { split; [lia|].
    pose proof (trail_pos_bound _ _ _ Hrank) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  pose proof (Forall_Znth_elim _ _ _ 0 (ind + 1)
    (mtw_trail_lits Hwf) Hidx) as Hlit.
  pose proof (lit_var_c_in_range anz_n
    (Znth (ind + 1) (mt_trail (ms_core Mscan_3)) 0) Hlit) as Hrange.
  pose proof (trail_pos_var _ _ _ Hrank) as Hvar.
  rewrite Z2Nat.id in Hvar by lia.
  change (lit_var_c (Znth (ind + 1)
    (mt_trail (ms_core Mscan_3)) 0) = x_3) in Hvar.
  assert (Hxrange : 0 <= x_3 < anz_n) by
    (rewrite <- Hvar; exact Hrange).
  specialize (Hmatch x_3 Hxrange).
  remember (Znth x_3 (ms_reason_words Mscan_3) 0) as w eqn:Hw.
  assert (Hwneq : w <> 0).
  { intro Hw0. unfold reason_word_ok in Hmatch.
    rewrite Hw0 in Hmatch. cbn in Hmatch. congruence. }
  assert (Hwzero : Z.eqb w 0 = false) by
    (apply Z.eqb_neq; exact Hwneq).
  assert (HCge2 : 2 <= Zlength Ccur).
  { destruct (is_tag w) eqn:Htag.
    - unfold reason_word_ok in Hmatch.
      rewrite Hwzero, Htag in Hmatch.
      destruct Hmatch as [_ Hshape].
      rewrite Hreason in Hshape. inversion Hshape. cbn. lia.
    - unfold reason_word_ok in Hmatch.
      rewrite Hwzero, Htag in Hmatch.
      destruct Hmatch as [_ [co [Hin Hshape]]].
      rewrite Hreason in Hshape. inversion Hshape. subst Ccur.
      pose proof (db_wf_obj anz_n (msolver_db Mscan_3) w co Hdbwf Hin) as Hobj.
      unfold obj_wf in Hobj. destruct Hobj as [Hlen _].
      unfold denote_obj. rewrite lits_denote_length. exact Hlen. }
  rewrite H_Ccur, lits_denote_length in HCge2.
  exfalso. lia.
Qed.


