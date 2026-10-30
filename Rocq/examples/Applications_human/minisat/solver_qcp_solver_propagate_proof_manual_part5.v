From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.Reals.Reals.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.


Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.

Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_solver_propagate_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.

Lemma proof_of_solver_propagate_which_implies_wit_58 : solver_propagate_which_implies_wit_58.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( unit_ret <> 0 ) as H_unit_ret.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_entry.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  bind_fact ( watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0.
  bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) (Zlength clause_contents) ) as H_propagation_replacement_scan_inv.
  bind_fact ( clause_lits_pointer scan_current lits ) as H_clause_lits_pointer.
  destruct (propagation_unit_keep_step__propagate_dbu
    source_words retained moved rest garbage watch_memory ii jj scan_current
    raw_suffix H_rest H_propagation_watch_scan_physical) as [garbage_route [memory_route Hkeep]].
  pose proof H_solver_propagation_scan_semantics as Hsem0.
  destruct Hsem0 as [Hlive | Hdead].
  2: { destruct Hdead as [Hnz _]. lia. }
  destruct Hlive as
    [Hzero [Hweak [Hlevel [Hheap [Hcovers [Hreasonless
    [Hp_level [Hp_wf [Hprocessed [Hfrontier Hcarrier]]]]]]]]]].
  assert (Hdbwf : db_wf n (msolver_db Mscan))
    by (destruct (solver_propagation_weak_core_facts__propagate
          n F A_arr K Mscan Hweak) as [_ [_ [Hdb _]]]; exact Hdb).
  pose proof H_propagation_replacement_scan_inv as Hreplacement; unfold propagation_replacement_scan_inv in
      Hreplacement.
  destruct Hreplacement as [Hrange [Hwords [Hslot1 [Hfalse1 Hfalse_tail]]]].
  assert (Hlen : 2 <= Zlength clause_contents) by lia.
  pose proof (propagation_normalized_clause_length watch0 false_lit
    clause_contents Hlen) as Hnormlen.
  assert (Hfalse_tail_norm : forall j,
    2 <= j < Zlength
      (propagation_normalized_clause watch0 false_lit clause_contents) ->
    lit_false (mt_assigns (ms_core Mscan))
      (Znth j (propagation_normalized_clause watch0 false_lit clause_contents) 0)).
  { intros j Hj. apply Hfalse_tail. rewrite Hnormlen in Hj. exact Hj. }
  sep_apply
    (propagation_unit_normalized_clause_db_rebuild__propagate_dbu
      n (ms_prob Mscan) (ms_learnt Mscan) scan_current lits watch0 false_lit
      clause_contents Hdbwf Hlen H_clause_lits_pointer).
  Intros prob_after learnt_after.
  match goal with
  | Hup : db_pair_lits_update _ _ scan_current clause_contents _
      prob_after learnt_after |- _ => rename Hup into Hupdate
  end.
  rewrite H_rest in Hcarrier.
  destruct (propagation_unit_normalized_watcher_transport__propagate_dbu
    n Mscan (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    p scan_current raw_suffix retained clause_contents watch0 false_lit lits
    prob_after learnt_after Hdbwf H_clause_lits_pointer H_false_lit H_watch0 Hcarrier Hupdate
    Hfrontier) as [co [a0 [a1 [tail [Hcontents [Hlong [Hin [Hco_lits
    [Htail [Hwatchcases [Hperm [Hexpected Hfrontierdb]]]]]]]]]]]].
  assert (Hweakdb : solver_propagation_weak n F A_arr K
    (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
      (ms_wm Mscan))).
  { eapply propagation_unit_db_weak_transport__propagate_dbu
      with (p := p) (current := scan_current) (false_lit := false_lit)
        (watch0 := watch0) (a0 := a0) (a1 := a1) (tail := tail)
        (contents := clause_contents) (co := co); eassumption. }
  unfold enqueue_post_at. Intros qtail' assigns' levels' reasons' trail'.
  match goal with Htr : enqueue_transition watch0 _ _ unit_ret _ _ _ _ _ _ _ _ _ _
    |- _ => rename Htr into Henqueue end.
  rewrite H_Znth in Henqueue.
  unfold enqueue_state_at. Intros rsn_enqueue trl_enqueue.
  assert (Hpostbound : 0 <= qtail' <= ms_cap Mscan) by (repeat split; solve [auto | (lia)]).
  destruct (enqueue_transition_nonzero_cases__propagate_dbu
    watch0 scan_current (ms_qtail Mscan) unit_ret qtail'
    (mt_assigns (ms_core Mscan)) (mt_levels (ms_core Mscan))
    (ms_reason_words Mscan) (mt_trail (ms_core Mscan))
    (mt_lim (ms_core Mscan)) assigns' levels' reasons' trail'
    Henqueue H_unit_ret) as [Hret Hcases].
  subst unit_ret.
  assert (Hcellcases :
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 = lit_sig watch0 \/
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 = 0).
  { destruct Hcases as [Hsame | Hfresh]; [left|right]; tauto. }
  assert (Hwatch0wf : lit_wf_c n watch0).
  { change (lit_wf_c n (Znth 0
      (propagation_normalized_clause watch0 false_lit clause_contents) 0)).
    eapply Forall_Znth_elim; [exact Hwords|].
    rewrite propagation_normalized_clause_length by exact Hlen. lia. }
  assert (Hwatchsafe : ~ minisat_processed n
    (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
    (mt_qhead (ms_core Mscan)) (literal_neg (lit_denote watch0))).
  { eapply propagation_unit_watch0_unprocessed__propagate_dbu;
      eassumption. }
  assert (Hcarrierdb : minisat_focus_scan_carrier
    (prob_after ++ learnt_after) p
    (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    (retained ++ scan_current :: nil) raw_suffix).
  { eapply propagation_unit_focus_keep_transport__propagate_dbu
      with (current := scan_current) (false_lit := false_lit)
        (watch0 := watch0) (a0 := a0) (a1 := a1) (tail := tail)
        (contents := clause_contents) (co := co); eassumption. }
  set (Mdb := msolver_propagation_db_wmap_update Mscan prob_after learnt_after
    (ms_wm Mscan)).
  assert (Hreuse_db : minisat_propagation_reuse_scan M0 Mdb p 0
    (scan_current :: raw_suffix)).
  { unfold Mdb. apply (minisat_propagation_reuse_normalize__api_reentry
      M0 Mscan p 0 (scan_current :: raw_suffix) scan_current a0 a1 tail watch0
      prob_after learnt_after (ms_wm Mscan)).
    - rewrite <- Hcontents. rewrite <- H_false_lit. exact Hupdate.
    - rewrite <- H_false_lit. exact Hwatchcases.
    - rewrite <- H_rest. exact Hreuse_entry. }
  destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mdb Hweakdb)
    as (_ & _ & Hdbnorm & _ & Htrailnorm).
  assert (Hfocus_cell : Znth (lit_var_c p) (mt_levels (ms_core Mdb)) 0 =
    Zlength (mt_lim (ms_core Mdb))).
  { apply (level_of_msolver_view_levels__analyze n Mdb (lit_var_c p)
      (Zlength (mt_lim (ms_core Mdb))) Htrailnorm). exact Hp_level. }
  pose proof (minisat_propagation_reuse_enqueue__api_reentry
    n M0 Mdb p (scan_current :: raw_suffix) watch0 scan_current
    (lits_denote (propagation_normalized_clause watch0 false_lit clause_contents))
    Hdbnorm Htrailnorm Hp_wf Hwatch0wf Hprocessed Hreuse_db) as Hreuse_enqueued.
  pose proof H_solver_propagation_scan_semantics as Hsemnorm. rewrite H_rest in Hsemnorm.
  assert (Hsemroute : solver_propagation_scan_semantics n F A_arr K
    (msolver_propagation_enqueue_success Mdb watch0 scan_current
      (lits_denote (propagation_normalized_clause watch0 false_lit clause_contents)))
    p 0 (retained ++ scan_current :: nil) raw_suffix).
  { destruct Hcases as [Hsame | Hfresh].
    - eapply propagation_unit_scan_semantics_unchanged__propagate_dbu;
        [exact Hsemnorm|exact Hweakdb|exact Hfrontierdb|exact Hcarrierdb|].
      exact (proj1 Hsame).
    - destruct Hfresh as
        [Hfreshcell [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]].
      assert (Hroom : ms_qtail Mdb < ms_cap Mdb).
      { unfold Mdb, msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update. cbn. lia. }
      eapply propagation_unit_fresh_success_semantics__propagate_dbu
        with (M := Mscan) (Mdb := Mdb) (co := co)
          (old_lits := clause_contents)
          (new_lits := propagation_normalized_clause watch0 false_lit clause_contents)
          (retained := retained) (suffix := raw_suffix)
          (prob_after := prob_after) (learnt_after := learnt_after).
      + reflexivity.
      + exact Hsemnorm.
      + exact Hweak.
      + exact Hweakdb.
      + exact Hdbwf.
      + exact Hin.
      + rewrite Hcontents, Hco_lits. exact Hperm.
      + exact Hupdate.
      + exact Hwords.
      + rewrite propagation_normalized_clause_length by exact Hlen. exact Hlong.
      + reflexivity.
      + rewrite Hslot1. exact Hfalse1.
      + exact Hfalse_tail_norm.
      + exact Hfrontierdb.
      + exact Hcarrierdb.
      + exact Hwatch0wf.
      + exact Hfreshcell.
      + exact Hroom. }
  set (Mpost := msolver_propagation_enqueue_success Mdb watch0 scan_current
    (lits_denote (propagation_normalized_clause watch0 false_lit clause_contents))).
  assert (Hdbpost : msolver_db Mpost = prob_after ++ learnt_after).
  { unfold Mpost, msolver_propagation_enqueue_success.
    destruct (Z.eqb (Znth (lit_var_c watch0) (mt_assigns (ms_core Mdb)) 0) 0);
      reflexivity. }
  assert (Hdbpost_wf : db_wf n (msolver_db Mpost)).
  { rewrite Hdbpost. exact Hdbnorm. }
  destruct (db_pair_lits_update_selected_owner__propagate_dbu
    _ _ _ _ _ _ _ Hupdate) as [selected [Hselected Hselected_words]].
  assert (Hreal : is_tag scan_current = false).
  { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan) scan_current co Hdbwf Hin). }
  assert (Hwatch1 : co_watch1 selected = lit_neg_c p).
  { unfold co_watch1. rewrite Hselected_words.
    unfold propagation_normalized_clause. cbn. exact H_false_lit. }
  assert (Hwatch0_selected : co_watch0 selected = watch0).
  { unfold co_watch0. rewrite Hselected_words. reflexivity. }
  assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mpost p 0 raw_suffix).
  { eapply minisat_propagation_reuse_advance__api_reentry;
      [exact Hreuse_enqueued|].
    apply (minisat_base_focus_word_completed_normalized_real__api_reentry
      n Mpost p scan_current selected Hdbpost_wf Hreal
      ltac:(rewrite Hdbpost; exact Hselected) Hwatch1).
    rewrite Hwatch0_selected.
    apply (propagation_enqueue_partner_base_completed__api_reentry
      n Mdb p watch0 scan_current
      (lits_denote (propagation_normalized_clause watch0 false_lit clause_contents))
      Htrailnorm Hp_wf Hwatch0wf Hprocessed Hfocus_cell).
    destruct Hcellcases as [Htrue|Hfresh]; [right|left]; exact Htrue || exact Hfresh. }
  Exists garbage_route memory_route
    (msolver_propagation_enqueue_success Mdb watch0 scan_current
      (lits_denote (propagation_normalized_clause watch0 false_lit clause_contents)))
    raw_suffix (retained ++ scan_current :: nil) prob_after learnt_after.
  unfold propagation_unit_success_transition, enqueue_post_at, enqueue_state_at.
  Exists qtail' assigns' levels' reasons' trail' rsn_enqueue trl_enqueue.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  apply store_ptr_undef_store_ptr.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_5 : solver_propagate_which_implies_wit_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
prop_apply_p (PtrArray.full_Zlength begin (Zlength source_words) watch_memory).
  Intros.
  pose proof (Znth_split 0 watch_memory ii ltac:(lia)) as Hsplit.
  pose proof msat_ptrarray_seg_split_middle as Hdecomp.
  assert (Hsuffix_len : Zlength watch_memory =
      ii + 1 + Zlength (sublist (ii + 1) (Zlength watch_memory) watch_memory)).
  {
    rewrite Hsplit at 1.
    rewrite Zlength_app, Zlength_cons, Zlength_sublist by lia.
    lia.
  }
  destruct (Z.eq_dec jj ii) as [Heq | Hneq].
  - Right.
    Exists (sublist 0 ii watch_memory)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      (Znth ii watch_memory 0).
    unfold propagation_ptr_segment.
    subst jj.
    sep_apply (PtrArray.full_to_seg begin (Zlength source_words) watch_memory).
    pose proof (Hdecomp begin 0 (Zlength source_words)
      (sublist 0 ii watch_memory) (Znth ii watch_memory 0)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      ltac:(rewrite Zlength_sublist by lia; lia)) as Hdecomp_at.
    rewrite <- Hsplit in Hdecomp_at.
    sep_apply Hdecomp_at.
    rewrite !Zlength_sublist by lia.
    replace (0 + (ii - 0)) with ii by lia.
    replace (ii + 1) with (0 + ii + 1) by lia.
    PtrArray.ArraySimplify.
    prop_apply_p (valid_store_ptr
      (begin + (0 + ii) * sizeof(PTR)) (Znth ii watch_memory 0)).
    Intros.
    unfold valid_ptr_value in *.
    replace (0 + ii) with ii by lia.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; solve [lia | exact Hsplit].
  - Left.
    Exists (sublist 0 ii watch_memory)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      (Znth ii watch_memory 0).
    unfold propagation_ptr_segment.
    sep_apply (PtrArray.full_to_seg begin (Zlength source_words) watch_memory).
    pose proof (Hdecomp begin 0 (Zlength source_words)
      (sublist 0 ii watch_memory) (Znth ii watch_memory 0)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      ltac:(rewrite Zlength_sublist by lia; lia)) as Hdecomp_at.
    rewrite <- Hsplit in Hdecomp_at.
    sep_apply Hdecomp_at.
    rewrite !Zlength_sublist by lia.
    replace (0 + (ii - 0)) with ii by lia.
    replace (ii + 1) with (0 + ii + 1) by lia.
    PtrArray.ArraySimplify.
    prop_apply_p (valid_store_ptr
      (begin + (0 + ii) * sizeof(PTR)) (Znth ii watch_memory 0)).
    Intros.
    unfold valid_ptr_value in *.
    sep_apply (PtrArray.seg_split_to_seg begin 0 jj ii
      (sublist 0 ii watch_memory) ltac:(lia)).
    replace (jj - 0) with jj by lia.
    replace (ii - 0) with ii by lia.
    sep_apply (PtrArray.seg_split_to_seg begin jj (jj + 1) ii
      (sublist jj ii (sublist 0 ii watch_memory)) ltac:(lia)).
    replace (jj + 1 - jj) with 1 by lia.
    rewrite (Zsublist_Zsublist 1 ii 0 jj
      (sublist 0 ii watch_memory)) by lia.
    rewrite (Zsublist_Zsublist (ii - jj) ii 1 jj
      (sublist 0 ii watch_memory)) by lia.
    replace (0 + jj) with jj by lia.
    replace (1 + jj) with (jj + 1) by lia.
    replace (ii - jj + jj) with ii by lia.
    rewrite (sublist_single 0 jj (sublist 0 ii watch_memory)) by
      (rewrite Zlength_sublist by lia; lia).
    PtrArray.ArraySimplify.
    Intros.
    replace (0 + ii) with ii by lia.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; solve [lia | exact Hsplit].
Qed.


Lemma proof_of_solver_propagate_entail_wit_9_1_scan_move : solver_propagate_entail_wit_9_1_scan_move.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_inspects in *.
  subst copy_dst_2.
    bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
    bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_src_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  assert (Hcursor : copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
  assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
  { pose proof H_propagation_watch_scan_physical as Hphysical_len.
    unfold propagation_watch_scan_physical in Hphysical_len.
    tauto. }
  assert (Hcursor_words : copy_src_2 < Zlength watch_memory) by lia.
  pose proof (ms_binary_watch_copy_step__common
    watch_memory raw_prefix scan_current raw_suffix
    ii jj copy_src_2 copy_src_2 copy_memory_2
    H_binary_watch_copy_progress Hcursor_words) as Hprogress_next.
  rewrite replace_Znth_Znth in Hprogress_next.
  Exists copy_memory_2 (copy_src_2 + 1) (copy_src_2 + 1)
         scratch_lits_2 scratch_base_2.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full begin copy_src_2 (Zlength source_words)
      (Znth copy_src_2 copy_memory_2 0) copy_memory_2 ltac:(lia)).
  rewrite ?replace_Znth_Znth.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) copy_memory_2).
  sep_apply (Vecp.rep_ptr_intro ws begin copy_memory_2 cap
    (Zlength copy_memory_2) (Zlength source_words) (Zlength copy_memory_2)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vec_buf_solve)).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_1_scan_same : solver_propagate_entail_wit_11_1_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | try rewrite Hcandidate; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_12_7_scan_move : solver_propagate_entail_wit_12_7_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap);
    [ | subst candidate_post_memory; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close_nested_addr 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_19_3_binary_keep : solver_propagate_entail_wit_19_3_binary_keep.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_binary_keep.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_2_real_satisfied : solver_propagate_entail_wit_20_2_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_5_real_satisfied : solver_propagate_entail_wit_20_5_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_22_real_migrated : solver_propagate_entail_wit_22_real_migrated.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (minisat_propagation_reuse_scan M0 Mroute p 0 rest_route)
    as Hreuse_route.
  bind_fact ( db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents
      (propagation_migrated_clause watch0 candidate (lit_neg_c p) offset clause_contents) prob_route learnt_route )
      as H_db_pair_lits_update.
  bind_fact ( propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry Mscan Mroute p prob_route learnt_route
      scan_wm candidate scan_current
      source_words retained moved rest watch_memory ii jj moved_route rest_route garbage_route (replace_Znth ii
      (Znth ii candidate_post_memory 0) candidate_post_memory) simp_count prop_count ) as
      H_propagation_real_migrated_exit_car.
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  bind_fact ( confl = 0 ) as H_confl.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( candidate_post_memory = watch_memory ) as H_candidate_post_memory.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  set (new_wm := replace_Znth (lit_neg_c candidate)
    (Znth (lit_neg_c candidate) scan_wm nil ++ (scan_current :: nil)) scan_wm).
  unfold propagation_real_migrated_exit_carrier in H_propagation_real_migrated_exit_car.
  destruct H_propagation_real_migrated_exit_car as [HMroute [Htransition [Hstep [Hshape [Hseed
    [Hframe_route [Hfrontier [Hsem [Hsimp [Hprop [Hmemory
    [Hphysical Hwm]]]]]]]]]]]].
  assert (Hwm_new : ms_wm Mroute =
      replace_Znth p (retained ++ rest_route) new_wm).
  { unfold new_wm. exact Hwm. }
  assert (Hbinary : solver_binary_rep Mroute = solver_binary_rep Mscan).
  { rewrite HMroute. unfold solver_binary_rep. reflexivity. }
  assert (Hframe : solver_propagate_frame s_pre Mroute =
      solver_propagate_frame s_pre Mscan).
  { destruct (db_pair_lits_update_words__propagate
      _ _ _ _ _ _ _ H_db_pair_lits_update) as [Hprob_words Hlearnt_words].
    rewrite HMroute.
    apply solver_propagate_frame_db_wmap_update__propagate;
      assumption. }
  assert (Hmemory_length :
      Zlength
        (replace_Znth ii (Znth ii candidate_post_memory 0)
          candidate_post_memory) = Zlength source_words).
  { unfold propagation_watch_scan_physical in Hphysical. intuition. }
  assert (Hsem_confl : solver_propagation_scan_semantics n F A_arr K
      Mroute p confl retained rest_route).
  { rewrite H_confl. exact Hsem. }
  assert (Hreuse_confl : minisat_propagation_reuse_scan M0
    Mroute p confl rest_route).
  { rewrite H_confl. exact Hreuse_route. }
  assert (Hcur2 : Znth (Zlength raw_prefix)
      (replace_Znth (Zlength raw_prefix)
         (Znth (Zlength raw_prefix) watch_memory 0) watch_memory) 0
      = scan_current).
  { rewrite Znth_replace_Znth_Same by
      (rewrite H_watch_memory, Zlength_app, Zlength_cons;
       pose proof (Zlength_nonneg raw_prefix);
       pose proof (Zlength_nonneg raw_suffix); lia).
    rewrite H_Zlength, <- H_candidate_post_memory. exact H_Znth. }
  assert (Hcur_wm : Znth (Zlength raw_prefix) watch_memory 0 = scan_current).
  { rewrite H_watch_memory, app_Znth2 by lia. rewrite Z.sub_diag. reflexivity. }
  rewrite Hcur_wm.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words)
    (replace_Znth ii (Znth ii candidate_post_memory 0) candidate_post_memory)).
  sep_apply (Vecp.rep_ptr_intro ws begin
    (replace_Znth ii (Znth ii candidate_post_memory 0) candidate_post_memory) cap
    (Zlength candidate_post_memory) (Zlength source_words) (Zlength candidate_post_memory));
    [ | rewrite ?Zlength_replace_Znth; first [lia | vec_buf_solve] .. ].
  Left.
  Exists trl_scan rsn_scan prop_count simp_count
    new_wm
    (retained ++ rest_route) source_words moved_route garbage_route
    (replace_Znth ii (Znth ii candidate_post_memory 0)
      candidate_post_memory)
    (ii + 1) jj retained rest_route Mentry.
  Exists Mroute levels_entry.
  split_pure_spatial.
  - try rewrite Hcur2.
    try rewrite <- H_candidate.
    fold new_wm.
    unfold solver_propagation_scan_core_at.
    rewrite Hbinary, Hframe, HMroute.
    unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update.
    cbn. unfold PtrArray.seg, stats_propagate_scan.
    cancel (&( s_pre # "solver_t" ->ₛ "reasons") # Ptr |-> rsn_scan).
    cancel.
    fold new_wm.
    unfold Znth; cbn; csimpl.
    lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel.
  - split_pures; dump_pre_spatial.
    all: lazymatch goal with
        | |- solver_shape _ => exact Hshape
        | |- msolver_seed_shadow _ => exact Hseed
        | |- propagation_caller_frame _ _ => exact Hframe_route
        | |- propagation_scan_frontier _ _ _ => exact Hfrontier
        | |- solver_propagation_scan_semantics _ _ _ _ _ _ _ _ _ => exact Hsem_confl
        | |- minisat_propagation_reuse_scan _ _ _ _ _ => exact Hreuse_confl
        | |- propagation_watch_scan_physical _ _ _ _ _ _ _ _ => exact Hphysical
        | Hfact : ?P |- ?P => exact Hfact
        | _ =>
            rewrite ?HMroute;
            cbn [msolver_propagation_db_wmap_update msolver_propagation_overlay msolver_propagation_update];
            lazymatch goal with
            | Hfact : ?P |- ?P => exact Hfact
            | |- ?x = ?x => reflexivity
            | |- _ = _ => lia
            | |- _ <= _ => lia
            | |- _ < _ => lia
            | |- _ <> _ => lia
            | |- _ /\ _ => lia
            end
        end.
Qed.



Lemma proof_of_solver_propagate_entail_wit_27_1 : solver_propagate_entail_wit_27_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists trl_scan_2 rsn_scan_2 prop_count_2 simp_count_2 scan_wm_2 logical_words_2 source_words_2 moved_2 garbage_2 watch_memory_2 ii_2 jj_2 retained_2 rest_2 Mentry_2.
  Exists Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_entail_wit_29_1 : solver_propagate_entail_wit_29_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_propagate_open_at, stats_propagations, stats_inspects in *.
  msat_propagate_finish_frame lvl_finish levels_entry trl_finish rsn_finish Mfinish.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_88_binary_keep_pure : solver_propagate_partial_solve_wit_88_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures; dump_pre_spatial.
  all: try assumption; try (rewrite PreH6, PreH8; lia); try (rewrite PreH5; lia).
  all: rewrite Znth_replace_Znth_Same by lia; rewrite PreH6, PreH8; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_261_scan_move_pure : solver_propagate_partial_solve_wit_261_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in PreH1 by lia.
  subst retval_3.
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  apply dump_spatial_left.
  all: first [assumption | reflexivity | lia
             | (match goal with H : ?M = msolver_propagation_scan_begin _ _ _ |- _ =>
                  rewrite <- H end; lia)].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_262_scan_move_pure : solver_propagate_partial_solve_wit_262_scan_move_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in PreH1 by lia.
  subst retval_3.
  split_pures; dump_pre_spatial;
    first [assumption | lia
          | (match goal with H : ?M = msolver_propagation_scan_begin _ _ _ |- _ =>
               rewrite <- H end; lia)].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_305_scan_move_pure : solver_propagate_partial_solve_wit_305_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_437_unit_move_pure : solver_propagate_partial_solve_wit_437_unit_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hwf0 : lit_wf_c n watch0).
  { match goal with
    | H : propagation_replacement_scan_inv n Mscan _
            (propagation_normalized_clause watch0 _ _) _ |- _ =>
        destruct H as [_ [Hall _]]; unfold propagation_normalized_clause in Hall;
        inversion Hall; assumption
    end. }
  assert (Henq : enqueue_input (ms_size Mscan) watch0 (ms_qtail Mscan)
      (mt_assigns (ms_core Mscan)) (mt_levels (ms_core Mscan))
      (ms_reason_words Mscan) (mt_trail (ms_core Mscan))).
  { match goal with
    | H : solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest |- _ =>
        exact (propagation_scan_enqueue_input__propagate n F A_arr K Mscan p retained rest
                 watch0 H Hwf0)
    end. }
  assert (Hshape' : solver_shape Mscan) by assumption.
  unfold solver_shape in Hshape'.
  split_pures; dump_pre_spatial; first [assumption | lia].
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_438_unit_same_pure : solver_propagate_partial_solve_wit_438_unit_same_pure.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Hwf0 : solver_qcp_model.lit_wf_c n watch0).
  { match goal with
    | H : solver_qcp_model.propagation_replacement_scan_inv n Mscan _
            (solver_qcp_model.propagation_normalized_clause watch0 _ _) _ |- _ =>
        destruct H as [_ [Hall _]];
        unfold solver_qcp_model.propagation_normalized_clause in Hall;
        inversion Hall; assumption
    end. }
  assert (Henq :
    enqueue_input
      (solver_qcp_model.ms_size Mscan) watch0
      (solver_qcp_model.ms_qtail Mscan)
      (solver_qcp_model.mt_assigns (solver_qcp_model.ms_core Mscan))
      (solver_qcp_model.mt_levels (solver_qcp_model.ms_core Mscan))
      (solver_qcp_model.ms_reason_words Mscan)
      (solver_qcp_model.mt_trail (solver_qcp_model.ms_core Mscan))).
  { match goal with
    | H : solver_qcp_model.solver_propagation_scan_semantics
            n F A_arr K Mscan p 0 retained rest |- _ =>
        exact
          (solver_qcp_proof_automation.propagation_scan_enqueue_input__propagate
            n F A_arr K Mscan p retained rest watch0 H Hwf0)
    end. }
  assert (Hshape' : solver_qcp_model.solver_shape Mscan) by assumption.
  unfold solver_qcp_model.solver_shape in Hshape'.
  split_pures; dump_pre_spatial; first [assumption | lia].
Qed.



Lemma proof_of_solver_propagate_safety_wit_213_scan_same : solver_propagate_safety_wit_213_scan_same.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst retval. pose proof (lit_sign_c_range candidate). rewrite signed_last_nbits_8_lit_sign. msat_manual_entailer_with ltac:(int_auto || lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_20 : solver_propagate_which_implies_wit_20.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( ms_wm Mscan = replace_Znth p logical_words scan_wm ) as H_ms_wm.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( clause_is_lit_result scan_current 0 ) as H_clause_is_lit_result.
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [Hlive | Hconflict]; [|decompose [and] Hconflict; lia].
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hlivecovers &
     Hliveearliest & Hlivelevel & Hp_wf & Hprocessed & Hwatch_except &
     Hscan_carrier).
  assert (Hdbwf : db_wf n (msolver_db Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_db_wf) (@msa_db_wf). }
  assert (Hwmexact : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact) (@msa_wmap_exact). }
  assert (Hsize : n = ms_size Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_size) (@msa_size). }
  assert (Hrest : rest = scan_current :: raw_suffix)
    by (eapply propagation_watch_scan_rest_head__propagate;
        [ eassumption
        | eassumption
        | eassumption ]).
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as
    (Hscan & Hmemory & Hretlen & Hprefixlen & Hmemorylen).
  assert (Hscan_wm_len : Zlength scan_wm = 2 * n).
  { pose proof Hwmexact as [Hwm_len _].
    rewrite H_ms_wm, Zlength_replace_Znth in Hwm_len. exact Hwm_len. }
  assert (Hcurrent_in :
    In scan_current (Znth p (ms_wm Mscan) nil)).
  {
    rewrite H_ms_wm, Znth_replace_Znth_Same by lia.
    subst logical_words.
    apply in_or_app. right.
    rewrite Hrest. left. reflexivity.
  }
  unfold clause_is_lit_result in H_clause_is_lit_result.
  destruct H_clause_is_lit_result as [[Hret Htag] | [Hret Hreal]]; [lia|].
  destruct (wmap_real_witness n (msolver_db Mscan) (ms_wm Mscan)
    p scan_current Hdbwf Hwmexact
    ltac:(destruct Hp_wf; lia) Hcurrent_in Hreal)
    as [co [Hco [Hlen Hwatched]]].
  pose proof (db_wf_obj n (msolver_db Mscan) scan_current co
    Hdbwf Hco) as Hobj.
  destruct Hobj as [Hobjlen [Hobjlits Hobjnodup]].
  assert (Hw0 : lit_wf_c n (Znth 0 (co_lits co) 0)).
  {
    eapply Forall_Znth_elim; [exact Hobjlits|lia].
  }
  assert (Hw1 : lit_wf_c n (Znth 1 (co_lits co) 0)).
  {
    eapply Forall_Znth_elim; [exact Hobjlits|lia].
  }
  pose proof (lit_var_c_in_range n (Znth 0 (co_lits co) 0) Hw0) as Hv0.
  pose proof (lit_var_c_in_range n (Znth 1 (co_lits co) 0) Hw1) as Hv1.
  assert (Hcontents : clause_db_pair_contents
    (ms_prob Mscan) (ms_learnt Mscan) scan_current (co_lits co)).
  {
    exists co. split; [exact Hco|reflexivity].
  }
  assert (Hfocus :
    clause_db_rep (ms_prob Mscan) ** clause_db_rep (ms_learnt Mscan)
    |-- clause_db_pair_focus (ms_prob Mscan) (ms_learnt Mscan)
      scan_current (co_lits co)).
  {
    apply in_app_or in Hco as [Hprob | Hlearnt].
    - apply in_split in Hprob as [pre [post Hprob]].
      rewrite Hprob.
      sep_apply (clause_db_rep_app_elim pre
        ((scan_current, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold clause_db_pair_focus.
      Exists (co_learnt co).
      unfold clause_db_pair_remainder.
      Left.
      Exists co pre post.
      cbn [fst snd].
      split_pure_spatial.
      + cancel (MiniSatClause.rep scan_current (co_learnt co) (co_lits co)).
        cancel.
      + dump_pre_spatial. auto.
    - apply in_split in Hlearnt as [pre [post Hlearnt]].
      rewrite Hlearnt.
      sep_apply (clause_db_rep_app_elim pre
        ((scan_current, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold clause_db_pair_focus.
      Exists (co_learnt co).
      unfold clause_db_pair_remainder.
      Right.
      Exists co pre post.
      cbn [fst snd].
      split_pure_spatial.
      + cancel (MiniSatClause.rep scan_current (co_learnt co) (co_lits co)).
        cancel.
      + dump_pre_spatial. auto.
  }
  Exists (co_lits co).
  sep_apply Hfocus.
  unfold lit_wf_c in Hw0, Hw1.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_24 : solver_propagate_which_implies_wit_24.
Proof.
LLM_pre_process ltac:(lia || int_auto).
pose proof (lit_sign_c_range w0) as Hsign.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_54 : solver_propagate_which_implies_wit_54.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold propagation_unit_conflict_ready in PreH8.
  destruct PreH8 as [Hdbupdate [Hroute Hsem]].
  pose proof msat_binary_watch_write_prefix as Hwrite_prefix.
  unfold propagation_watch_scan_physical in PreH7.
  destruct PreH7 as
    [Hscaninv [Hwatchmemory [Hretlen [Hprefixlen Hwatchlen]]]].
  unfold binary_watch_copy_progress in PreH6.
  destruct PreH6 as
    (copied & uncopied & Hcopywords & Hrawprefixlen & Hjjrange &
     Hsuffixparts & Hsrcidx & Hdstidx & Hcopydef & Hcopylen).
  subst raw_suffix.
  assert (Hsrcend : copy_src = Zlength source_words) by
    (pose proof ptr_size_pos as Hptrpos;
     apply Z.le_antisymm;
     [exact PreH5 |
      apply (proj2 (Z.mul_le_mono_pos_r _ _ _ Hptrpos));
      rewrite PreH3, PreH2 in PreH1;
      change (sizeof (PTR)) with (Z.of_nat ptr_size) in PreH1;
      lia]).
  pose proof Hwatchlen as HX.
  rewrite Hcopywords in HX.
  rewrite Zlength_app in HX.
  rewrite Zlength_cons in HX.
  rewrite Zlength_app in HX.
  assert (Huncopiedlen : Zlength uncopied = 0) by lia.
  assert (Huncopied : uncopied = nil) by
    (destruct uncopied as [|u uncopied];
     [reflexivity |
      rewrite Zlength_cons in Huncopiedlen;
      pose proof (Zlength_nonneg uncopied);
      lia]).
  subst uncopied.
  rewrite app_nil_r in Hcopywords.
  assert (Hrest_sub :
    rest = sublist ii (Zlength watch_memory) watch_memory) by
    (rewrite Hwatchmemory;
     rewrite app_assoc;
     rewrite <- Hprefixlen;
     rewrite sublist_app_exact2;
     reflexivity).
  assert (Hcopied_sub :
    scan_current :: copied =
      sublist ii (Zlength watch_memory) watch_memory) by
    (rewrite Hcopywords;
     rewrite <- Hrawprefixlen;
     rewrite sublist_app_exact2;
     reflexivity).
  assert (Hrest : rest = scan_current :: copied) by
    (rewrite Hrest_sub, Hcopied_sub; reflexivity).
  assert (Hdstend : copy_dst = Zlength (retained ++ rest)) by
    (rewrite Zlength_app, Hrest, Zlength_cons; lia).
  assert (Hscanfinal :
    wlist_scan_inv source_words (retained ++ rest) moved nil) by
    (unfold wlist_scan_inv in *;
     rewrite app_nil_r;
     rewrite <- app_assoc;
     eapply Permutation_trans;
     [|exact Hscaninv];
     apply Permutation_app_head;
     apply Permutation_app_comm).
  assert (Hroom :
    Zlength (scan_current :: copied) <= Zlength (garbage ++ rest)) by
    (rewrite Zlength_app, Hrest, Zlength_cons;
     pose proof (Zlength_nonneg garbage);
     lia).
  destruct (Hwrite_prefix (scan_current :: copied) retained
    (garbage ++ rest) jj Hretlen Hroom) as
    (tail' & Hwritten & Htaillen).
  assert (Hcopyfromwrite :
    copy_memory =
      binary_watch_write jj (scan_current :: copied) watch_memory) by
    (rewrite Hcopydef; cbn [binary_watch_write]; reflexivity).
  assert (Hcopydecomp :
    copy_memory = (retained ++ rest) ++ tail') by
    (rewrite Hcopyfromwrite, Hwatchmemory, Hwritten, Hrest;
     apply app_assoc).
  assert (Hphysical_final :
    propagation_watch_scan_physical source_words (retained ++ rest)
      moved nil tail' copy_memory
      (Zlength source_words) (Zlength (retained ++ rest))) by
    (unfold propagation_watch_scan_physical;
     refine (conj Hscanfinal (conj _ (conj eq_refl (conj _ _))));
     [rewrite app_nil_r; exact Hcopydecomp |
      rewrite <- Hcopydecomp; lia |
      lia]).
  assert (Htransition' :
    propagation_unit_conflict_transition n F A_arr K Mscan p scan_current
      prob_route learnt_route (retained ++ rest) Mroute) by
    (split; [exact Hroute | exact Hsem]).
  assert (Hstep :
    propagation_scan_conflict_step source_words retained moved rest
      copy_memory tail' (retained ++ rest)) by
    (unfold propagation_scan_conflict_step;
     split; [reflexivity | exact Hphysical_final]).
  Exists tail' (retained ++ rest).
  split_pure_spatial.
  - sep_apply
      (store_int_undef_store_int &( "false_lit") false_lit).
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_60 : solver_propagate_which_implies_wit_60.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst j.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    replace (begin + jj * sizeof(PTR) - begin) with (jj * sizeof(PTR)) by ring.
    rewrite Z.quot_mul.
    + reflexivity.
    + change (sizeof (PTR)) with ptr_size_Z. solve_arch.
Qed.


Lemma proof_of_solver_propagate_entail_wit_11_4_scan_same : solver_propagate_entail_wit_11_4_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | subst candidate_post_memory; first [reflexivity | lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_16_1_unit_conflict_copy : solver_propagate_entail_wit_16_1_unit_conflict_copy.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( copy_dst_2 = copy_src_2 ) as H_copy_dst_2.
  bind_fact ( i < endvar ) as H_i.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src_2 * sizeof ( PTR ) ) as H_i_2.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  Exists (replace_Znth copy_dst_2
    (Znth copy_src_2
      (replace_Znth copy_src_2 (Znth copy_src_2 copy_memory_2 0)
        copy_memory_2) 0)
    (replace_Znth copy_src_2 (Znth copy_src_2 copy_memory_2 0)
      copy_memory_2))
    (copy_dst_2 + 1) (copy_src_2 + 1).
  assert (Hbound : 0 <= copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2. unfold_arch. cbn in H_endvar, H_i_2. nia. }
  split_pure_spatial.
  - rewrite H_copy_dst_2, !replace_Znth_Znth.
    sep_apply (PtrArray.missing_i_merge_to_full begin copy_src_2
      (Zlength source_words) (Znth copy_src_2 copy_memory_2 0) copy_memory_2
      Hbound).
    rewrite replace_Znth_Znth.
    sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) copy_memory_2).
    sep_apply (Vecp.rep_ptr_intro ws begin copy_memory_2 cap
      (Zlength copy_memory_2) (Zlength source_words) (Zlength copy_memory_2));
      [ | first [lia | vec_buf_solve] .. ].
    cancel.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    { rewrite ?H_copy_dst_2. repeat rewrite replace_Znth_Znth. lia. }
    assert (Hcursor_words : copy_src_2 < Zlength watch_memory).
    { assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
      { unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
        tauto. }
      rewrite Hwatch_len.
      change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2.
      unfold_arch. cbn in H_endvar, H_i_2. nia. }
    pose proof (ms_binary_watch_copy_step__common
      watch_memory raw_prefix scan_current raw_suffix
      ii jj copy_src_2 copy_dst_2 copy_memory_2
      H_binary_watch_copy_progress Hcursor_words) as Hprogress_next.
    rewrite ?H_copy_dst_2 in Hprogress_next |- *.
    repeat rewrite replace_Znth_Znth in Hprogress_next.
    repeat rewrite replace_Znth_Znth.
    exact Hprogress_next.
Qed.



Lemma proof_of_solver_propagate_entail_wit_19_4_binary_keep : solver_propagate_entail_wit_19_4_binary_keep.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_binary_keep.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_7_real_satisfied : solver_propagate_entail_wit_20_7_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_21_real_satisfied : solver_propagate_entail_wit_20_21_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_24_1_real_satisfied : solver_propagate_entail_wit_24_1_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  subst lvl_next.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at, stats_propagate_scan.
    cbn -[ptr_size_Z Znth Vecp.rep_ptr].
    cancel (solver_propagate_frame s_pre Mnext).
    cancel.
    csimpl. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.



Lemma proof_of_solver_propagate_entail_wit_24_2_real_satisfied : solver_propagate_entail_wit_24_2_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stats_propagations, stats_inspects.
  msat_split_after_llm.
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Right.
  Exists trl_next rsn_next simp_count_next prop_count_next next_wm
    logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next
    retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_92_binary_keep_pure : solver_propagate_partial_solve_wit_92_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stats_propagations, stats_inspects.
  msat_propagation_keep_scan_key ltac:((dump_pre_spatial; try assumption)).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_249_scan_move_pure : solver_propagate_partial_solve_wit_249_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_263_scan_move_pure : solver_propagate_partial_solve_wit_263_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in PreH1 by lia.
  subst retval_3.
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  apply dump_spatial_left.
  all: first
    [ assumption
    | reflexivity
    | lia
    | match goal with
      | H : ?M = msolver_propagation_scan_begin _ _ _ |- _ => rewrite <- H; lia
      end ].
Qed.
