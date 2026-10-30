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

Lemma proof_of_solver_propagate_entail_wit_26_2_real_migrated : solver_propagate_entail_wit_26_2_real_migrated.
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



Lemma proof_of_solver_propagate_partial_solve_wit_53_scan_same_pure : solver_propagate_partial_solve_wit_53_scan_same_pure.
Abort.



Lemma proof_of_solver_propagate_partial_solve_wit_86_binary_keep_pure : solver_propagate_partial_solve_wit_86_binary_keep_pure.
Abort.


Lemma proof_of_solver_propagate_partial_solve_wit_93_binary_keep_pure : solver_propagate_partial_solve_wit_93_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stats_propagations, stats_inspects.
  msat_propagation_keep_scan_key ltac:((dump_pre_spatial; try assumption)).
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_295_scan_same_pure : solver_propagate_partial_solve_wit_295_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_303_scan_same_pure : solver_propagate_partial_solve_wit_303_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_442_unit_move_pure : solver_propagate_partial_solve_wit_442_unit_move_pure.
Proof.
  LLM_pre_process ltac:(idtac).
  split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - rewrite propagation_normalized_clause_length by lia.
    rewrite <- PreH42. exact PreH9.
  - rewrite propagation_normalized_clause_length by lia.
    exact PreH9.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_443_unit_same_pure : solver_propagate_partial_solve_wit_443_unit_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  all: rewrite propagation_normalized_clause_length by lia;
       try rewrite <- PreH43; exact PreH10.
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_16 : solver_propagate_which_implies_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  bind_fact ( propagation_scan_open n F A_arr K M0 Mentry Mscan p 0 source_words retained moved rest garbage
    watch_memory ii jj scan_current raw_suffix ) as H_propagation_scan_open.
  bind_fact ( propagation_binary_conflict_scan_ready n Mscan p scan_current source_words simp_count
    prop_count ) as H_propagation_binary_conflict_scan_r.
  bind_fact ( ms_wm Mscan = replace_Znth p (retained ++ rest) scan_wm ) as H_ms_wm.
  bind_fact ( 0 <= p ) as Hp_lo.
  bind_fact ( p < 2 * n ) as Hp_hi.
  bind_fact ( ws = Vecp.slot wlists_entry p ) as H_ws.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i.
  bind_fact (j = begin + copy_dst * sizeof(PTR)) as Hcopy_j.
  bind_fact (i >= endvar) as Hcopy_end.
  bind_fact (0 <= copy_dst) as Hcopy_nonnegative.
  bind_fact (copy_dst <= copy_src) as Hcopy_order.
  bind_fact (copy_src <= Zlength source_words) as Hcopy_bound.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src copy_dst
    copy_memory ) as H_binary_watch_copy_progress.
  bind_fact ( clause_lits_pointer (ms_binary Mscan) scratch_base ) as H_clause_lits_pointer.
  bind_fact ( Zlength scratch_lits = 2 ) as H_Zlength_3.
  unfold propagation_scan_open in H_propagation_scan_open.
  destruct H_propagation_scan_open as
    (Hshape & Hseed & Hframe & Hfront & Hsem & Hphys & Hrest & Hscanconfl).
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_initial.
  pose proof Hsem as Hsem_initial.
  rewrite Hrest in Hsem_initial, Hreuse_initial.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hpriorconf]; [|decompose [and] Hpriorconf; lia].
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hlivecovers &
     Hliveearliest & Hlivelevel & Hp_wf & Hprocessed & Hwatch_except &
     Hscan_carrier).
  unfold enqueue_post_at, enqueue_state_at.
  Intros qtail' assigns' levels' reasons' trail' s_reasons s_trail.
  unfold enqueue_transition in H.
  destruct H as [H | [H | H]];
    try solve [decompose [and] H; lia].
  destruct H as
    (Henq_assigned & Henq_notsig & Henqzero & Henq_assigns &
     Henq_levels & Henq_reasons & Henq_trail & Henq_qtail).
  subst qtail' assigns' levels' reasons' trail'.
  assert (Hconfl : confl = ms_binary Mscan) by lia.
  subst confl.
  prop_apply_p (valid_store_ptr &( s # "solver_t" ->ₛ "binary") (ms_binary Mscan)).
  Intros.
  unfold valid_ptr_value in *.
  destruct H as [_ [Hbinlo Hbinhi]].
  unfold clause_lits_pointer in H_clause_lits_pointer.
  subst scratch_base.
  unfold propagation_binary_conflict_scan_ready in H_propagation_binary_conflict_scan_r.
  destruct H_propagation_binary_conflict_scan_r as
    (Htagged & Hcovers & Hearliest & Hlevel & Hsimp & Hprop & Hsource0).
  bind_fact (Zlength copy_memory = Zlength source_words) as Hcmlen.
  sep_apply (Vecp.rep_ptr_bounds ws begin copy_memory).
  Intros_p Hcapb.
  subst simp_count prop_count.
  assert (Hscratch :
    scratch_lits = tag_lit scan_current :: lit_neg_c p :: nil).
  {
    apply (proj2
      (list_eq_ext scratch_lits
        (tag_lit scan_current :: lit_neg_c p :: nil) 0)).
    split.
    - simpl. exact H_Zlength_3.
    - intros k Hk.
      assert (Hk_cases : k = 0 \/ k = 1) by lia.
      destruct Hk_cases as [-> | ->]; simpl; assumption.
  }
  subst scratch_lits.
  set (Mroute :=
    msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p).
  pose proof (msat_binary_conflict_route_weak n F A_arr K Mscan p
    scan_current Hweak) as Hroute_weak.
  pose proof (msat_binary_conflict_route_semantics n F A_arr K Mscan p
    scan_current retained rest raw_suffix scan_wm
    Hweak Hroute_weak Hshape Hp_wf Hprocessed Hlivelevel Hproplevel
    Hlivecovers Hliveearliest Hwatch_except Htagged Hrest
    Henq_assigned Henq_notsig H_ms_wm) as Hroute_sem.
  destruct (msat_binary_conflict_exit_package n F A_arr K M0 Mentry Mscan p
    scan_current s begin i j endvar copy_src copy_dst ii jj source_words
    retained moved rest garbage raw_prefix raw_suffix watch_memory copy_memory
    Hshape Hseed Hframe Hfront Hrest Hphys H_binary_watch_copy_progress
    Hroute_sem H_endvar H_i Hcopy_j Hcopy_end Hcopy_nonnegative Hcopy_order Hcopy_bound Hbinlo) as
    ([tail' Hexit] & Hiend & Hjend & Hbinary_pos & Hbinary_even & Hfr_route).
  destruct (solver_propagation_weak_core_facts__propagate
    n F A_arr K Mscan Hweak) as (_ & _ & Hdb & Hwm & Htrail).
  destruct (propagation_scan_current_tag_facts__propagate
    n F A_arr K Mscan p 0 retained (scan_current :: raw_suffix)
    scan_current raw_suffix Hsem_initial eq_refl Htagged) as (_ & _ & Hcurrent_wf).
  pose proof (addclause_assigned_false n (ms_core Mscan)
    (tag_lit scan_current) Htrail Hcurrent_wf Henq_assigned Henq_notsig) as Hcurrent_false.
  pose proof (minisat_propagation_reuse_binary_conflict__api_reentry
    n F A_arr K M0 Mscan p retained scan_current raw_suffix
    Hsem_initial Hreuse_initial Htagged Hcurrent_false ltac:(lia)) as Hreuse_route.
  Exists s_reasons s_trail Mroute tail' (retained ++ rest).
  subst Mroute.
  cbn [msolver_propagation_binary_conflict msolver_propagation_overlay msolver_propagation_update ] in *.
  clear - Hexit Hiend Hjend H_ms_wm Hp_lo Hp_hi H_ws H_endvar
    Hsource0 Hcmlen Hcapb Hbinary_pos Hbinary_even Hfr_route Hreuse_route.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_propagation_scan_arrays_noqh_at,
    solver_propagation_scan_core_at, solver_binary_rep, binary_scratch_rep,
    stats_propagate_scan, MiniSatClause.rep, activity_state,
    clause_hdr_word, clause_hdr_addr, clause_act_addr, clause_lits_addr.
  rewrite Hfr_route.
  unfold msolver_propagation_binary_conflict,
    msolver_propagation_overlay, msolver_propagation_update.
  cbn.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  all: try assumption.
  unfold PtrArray.seg, IntArray.seg, CharArray.seg.
  cbn.
  cancel.
  csimpl.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_23 : solver_propagate_which_implies_wit_23.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  bind_fact ( ms_wm Mscan = replace_Znth p logical_words scan_wm ) as H_ms_wm.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( clause_is_lit_result scan_current 0 ) as H_clause_is_lit_result.
  bind_fact ( clause_db_pair_contents (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents ) as
      H_clause_db_pair_contents.
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as
    (Hscan & Hmemory & Hkept_len & Hprefix_len & Hmemory_len).
  assert (Hrest : rest = scan_current :: raw_suffix).
  {
    assert (Hparts :
      (retained ++ garbage) ++ rest =
      raw_prefix ++ scan_current :: raw_suffix).
    {
      rewrite <- app_assoc, <- Hmemory, H_watch_memory.
      reflexivity.
    }
    apply app_eq_app in Hparts as
      [[middle [Hleft Hright]] | [middle [Hleft Hright]]].
    - assert (Hmiddle_len : Zlength middle = 0).
      {
        rewrite Hleft, Zlength_app in Hprefix_len.
        lia.
      }
      assert (Hmiddle : middle = nil).
      {
        destruct middle as [|x middle]; [reflexivity|].
        rewrite Zlength_cons in Hmiddle_len.
        pose proof (Zlength_nonneg middle).
        lia.
      }
      subst middle. simpl in Hright. symmetry. exact Hright.
    - assert (Hmiddle_len : Zlength middle = 0).
      {
        rewrite Hleft, Zlength_app in H_Zlength.
        lia.
      }
      assert (Hmiddle : middle = nil).
      {
        destruct middle as [|x middle]; [reflexivity|].
        rewrite Zlength_cons in Hmiddle_len.
        pose proof (Zlength_nonneg middle).
        lia.
      }
      subst middle. simpl in Hright. exact Hright.
  }
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [[Hconfl Hlive] | Hconflict].
  - subst confl.
    assert (Hreuse_scan : minisat_propagation_reuse_scan M0 Mscan p 0 rest).
    { assumption. }
    pose proof Hlive as Hlive_all.
    destruct Hlive as
      (Hweak & Hproplevel & Hheapready & Hcovers & Hearliest & Hlevel &
       Hp_wf & Hprocessed & Hwatch_except & Hcarrier).
    assert (Hsemantics :
      solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest).
    {
      unfold solver_propagation_scan_semantics.
      left. split; [reflexivity|exact Hlive_all].
    }
    assert (Hdbwf : db_wf n (msolver_db Mscan)).
    {
      unfold solver_propagation_weak in Hweak.
      destruct K; destruct Hweak as [_ Hinv].
      - exact (msw_db_wf Hinv).
      - exact (msa_db_wf Hinv).
    }
    assert (Hwmexact : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
    {
      unfold solver_propagation_weak in Hweak.
      destruct K; destruct Hweak as [_ Hinv].
      - exact (msw_wmap_exact Hinv).
      - exact (msa_wmap_exact Hinv).
    }
    assert (Hcurrent_in : In scan_current (Znth p (ms_wm Mscan) nil)).
    {
      assert (Hwmlen : Zlength scan_wm = 2 * n)
        by (destruct Hwmexact as [Hlen _];
            rewrite H_ms_wm, Zlength_replace_Znth in Hlen; exact Hlen).
      rewrite H_ms_wm, Znth_replace_Znth_Same by lia.
      rewrite H_logical_words, Hrest.
      apply in_or_app. right. left. reflexivity.
    }
    unfold clause_is_lit_result in H_clause_is_lit_result.
    destruct H_clause_is_lit_result as [[Hret _] | [_ Hreal]]; [lia|].
    destruct (wmap_real_witness n (msolver_db Mscan) (ms_wm Mscan)
      p scan_current Hdbwf Hwmexact
      Hp_wf Hcurrent_in Hreal)
      as [co [Hco [Hco_len Hco_watch]]].
    unfold clause_db_pair_contents in H_clause_db_pair_contents.
    destruct H_clause_db_pair_contents as [co_target [Htarget Htarget_lits]].
    change (In (scan_current, co_target) (msolver_db Mscan)) in Htarget.
    assert (Hsame : co = co_target).
    {
      eapply db_wf_lookup_unique; eassumption.
    }
    subst co_target.
    unfold co_watch0, co_watch1 in Hco_watch.
    rewrite Htarget_lits in Hco_watch.
    destruct Hco_watch as [Hwatch | Hwatch].
    + Right.
      assert (Hslot : Znth 0 clause_contents 0 = lit_neg_c p).
      {
        rewrite <- Hwatch.
        rewrite lit_neg_c_involutive. reflexivity.
      }
      split_pure_spatial.
      * cancel.
      * split_pures; dump_pre_spatial.
        -- unfold real_watch_pair. left. exact Hslot.
        -- exact Hslot.
        -- exact Hrest.
        -- reflexivity.
        -- exact Hsemantics.
        -- exact Hreuse_scan.
    + Left.
      assert (Hslot : Znth 1 clause_contents 0 = lit_neg_c p).
      {
        rewrite <- Hwatch.
        rewrite lit_neg_c_involutive. reflexivity.
      }
      split_pure_spatial.
      * cancel.
      * split_pures; dump_pre_spatial.
        -- unfold real_watch_pair. right. exact Hslot.
        -- exact Hslot.
        -- exact Hrest.
        -- reflexivity.
        -- exact Hsemantics.
        -- exact Hreuse_scan.
  - destruct Hconflict as [_ [Hnil _]].
    rewrite Hrest in Hnil. discriminate.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_38 : solver_propagate_which_implies_wit_38.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( real_watch_pair p clause_contents ) as H_real_watch_pair.
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  assert (Hdestination_of_contents :
      clause_db_pair_contents (ms_prob Mscan) (ms_learnt Mscan)
        scan_current clause_contents ->
      propagation_destination_ok (2 * ms_size Mscan)
        p (lit_neg_c candidate)).
  { intro Hcontents.
    assert (Hp : lit_wf_c n p).
    { destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
      - destruct Hlive as (_ & _ & _ & _ & _ & _ & _ & Hp & _).
        exact Hp.
      - destruct Hconf as (_ & _ & Hcancel & _).
        unfold propagation_cancel_ready in Hcancel. tauto. }
    assert (Hweak : solver_propagation_weak n F A_arr K Mscan).
    { destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
      - destruct Hlive as (_ & Hweak & _). exact Hweak.
      - destruct Hconf as (_ & _ & Hcancel & _).
        exact (proj1 Hcancel). }
    assert (Hshape_db : n = ms_size Mscan /\
        db_wf n (msolver_db Mscan)).
    { unfold solver_propagation_weak in Hweak.
      destruct Hweak as [_ Hweak].
      destruct K as [A_inst | A_proc]; cbn in Hweak.
      - split; [exact (msw_size Hweak) | exact (msw_db_wf Hweak)].
      - split; [exact (msa_size Hweak) | exact (msa_db_wf Hweak)]. }
    destruct Hshape_db as [Hsize Hdb].
    destruct Hcontents as [co [Hin Hco]].
    change (In (scan_current, co) (msolver_db Mscan)) in Hin.
    pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdb Hin)
      as Hobj.
    unfold obj_wf in Hobj. rewrite Hco in Hobj.
    destruct Hobj as [Hlen [Hall Hnodup]].
    assert (Hcandidate_at : candidate = Znth offset clause_contents 0).
    { rewrite H_candidate.
      rewrite (Znth_sublist 0 2 (offset - 2) (Zlength clause_contents)
        clause_contents) by lia.
      replace (offset - 2 + 2) with offset by lia. reflexivity. }
    subst candidate.
    assert (Hcandidate_wf : lit_wf_c n (Znth offset clause_contents 0)).
    { apply (Forall_Znth_elim Z (lit_wf_c n) clause_contents 0 offset Hall).
      lia. }
    assert (Hdistinct_at : forall w,
        0 <= w < 2 ->
        Znth w clause_contents 0 = lit_neg_c p ->
        lit_var_c (Znth offset clause_contents 0) <>
        lit_var_c (lit_neg_c p)).
    { intros w Hw Hwatched.
      pose proof (Znth_split 0 clause_contents offset ltac:(lia))
        as Hsplit.
      pose proof Hnodup as Hnodup_split.
      rewrite Hsplit, map_app in Hnodup_split. simpl in Hnodup_split.
      assert (Hinprefix :
          In (lit_var_c (lit_neg_c p))
            (map lit_var_c (sublist 0 offset clause_contents))).
      { apply in_map.
        assert (Hprefix_value :
            Znth w (sublist 0 offset clause_contents) 0 =
            lit_neg_c p).
        { rewrite Znth_sublist0 by lia. exact Hwatched. }
        rewrite <- Hprefix_value.
        apply Znth_In. rewrite Zlength_sublist by lia. lia. }
      pose proof (NoDup_app_disjoint
        (map lit_var_c (sublist 0 offset clause_contents))
        (lit_var_c (Znth offset clause_contents 0) ::
         map lit_var_c
           (sublist (offset + 1) (Zlength clause_contents) clause_contents))
        (lit_var_c (lit_neg_c p))
        Hnodup_split Hinprefix) as Hnotin.
      intro Heq. apply Hnotin. simpl. left. exact Heq. }
    assert (Hcandidate_distinct :
        lit_var_c (Znth offset clause_contents 0) <>
        lit_var_c (lit_neg_c p)).
    { destruct H_real_watch_pair as [Hwatch | Hwatch].
      - apply (Hdistinct_at 0); [lia | exact Hwatch].
      - apply (Hdistinct_at 1); [lia | exact Hwatch]. }
    pose proof (lit_neg_c_wf n (Znth offset clause_contents 0)
      Hcandidate_wf) as Htarget.
    unfold propagation_destination_ok.
    split; [destruct Hp; lia |]. split.
    - rewrite <- Hsize. rewrite Hcandidate_at. exact Htarget.
    - intro Heq. apply Hcandidate_distinct.
      rewrite Hcandidate_at in Heq.
      rewrite lit_var_c_neg. rewrite <- Heq. rewrite lit_var_c_neg.
      reflexivity. }
  unfold clause_db_pair_frame at 1. Intros is_learnt.
  unfold clause_db_pair_remainder at 1. Split.
  - Intros co pre post.
    destruct H as [Hprob [Hlits Hlearnt]].
    assert (Hcontents : clause_db_pair_contents
        (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents).
    { exists co. split; [|exact Hlits].
      apply in_or_app. left. rewrite Hprob.
      apply in_or_app. right. simpl. auto. }
    specialize (Hdestination_of_contents Hcontents).
    unfold clause_db_pair_frame. Exists is_learnt.
    unfold clause_db_pair_remainder. Left. Exists co pre post.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - Intros co pre post.
    destruct H as [Hlearntdb [Hlits Hlearnt]].
    assert (Hcontents : clause_db_pair_contents
        (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents).
    { exists co. split; [|exact Hlits].
      apply in_or_app. right. rewrite Hlearntdb.
      apply in_or_app. right. simpl. auto. }
    specialize (Hdestination_of_contents Hcontents).
    unfold clause_db_pair_frame. Exists is_learnt.
    unfold clause_db_pair_remainder. Right. Exists co pre post.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_entail_wit_6_1_scan_same : solver_propagate_entail_wit_6_1_scan_same.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  cancel.
  bind_fact ( retval_6 = lit_neg_c p ) as H_retval_6.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth ii (Znth ii tagged_memory 0) tagged_memory )
      as H_tagged_enqueue_conflict_memory.
  bind_fact ( retval_2 = tag_lit (Znth ii tagged_memory 0) ) as H_retval_2.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest )
      as H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj )
      as H_propagation_watch_scan_physical.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  assert (Hwm_src : Zlength watch_memory = Zlength source_words) by assumption.
  assert (Htecm_len : Zlength tagged_enqueue_conflict_memory = Zlength source_words).
  { rewrite H_tagged_enqueue_conflict_memory, replace_Znth_Znth, H_tagged_memory,
      Zlength_replace_Znth. exact Hwm_src. }
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) tagged_enqueue_conflict_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin tagged_enqueue_conflict_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | first [lia | vec_buf_solve] .. ].
  rewrite H_Znth in H_retval_2.
  subst retval_2.
  subst retval_3.
  subst retval_4.
  pose proof H_propagation_watch_scan_physical as Hphys.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as [Hscan_inv [Hmemory [Hkept_len [Hprefix_len Hmemory_len]]]].
  assert (Hconfl : confl = 0).
  { pose proof H_solver_propagation_scan_semantics as Hsem0.
    unfold solver_propagation_scan_semantics in Hsem0.
    destruct Hsem0 as [[Hc _] | [_ [Hrest0 _]]].
    - exact Hc.
    - subst rest.
      rewrite app_nil_r in Hmemory.
      rewrite Hmemory, Hprefix_len in Hmemory_len.
      lia. }
  subst confl.
  assert (Hconcat :
    raw_prefix ++ scan_current :: raw_suffix = (retained ++ garbage) ++ rest).
  { rewrite <- H_watch_memory. rewrite Hmemory, app_assoc. reflexivity. }
  assert (Hrest : rest = scan_current :: raw_suffix).
  { apply app_eq_app in Hconcat as [[m [Hm Htail]] | [m [Hm Htail]]].
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in H_Zlength_2. rewrite Zlength_app, Hprefix_len in H_Zlength_2.
        lia. }
      destruct m as [|a m].
      + exact Htail.
      + exfalso. rewrite Zlength_cons in HZ.
        pose proof (Zlength_nonneg m). lia.
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in Hprefix_len. rewrite Zlength_app, H_Zlength_2 in Hprefix_len.
        lia. }
      destruct m as [|a m].
      + symmetry. simpl in Htail. exact Htail.
      + exfalso. rewrite Zlength_cons in HZ.
        pose proof (Zlength_nonneg m). lia. }
  pose proof H_solver_propagation_scan_semantics as Hsem.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconflict];
  [ destruct Hlive as
      [_ [Hweak [Hprop_level [Hheap_ready [Hheap_covers
         [Hreasonless [Hcurrent_level Hscan_tail]]]]]]]
  | destruct Hconflict as [Hnonzero _];
    exfalso; apply Hnonzero; reflexivity ].
  cancel.
  Exists (clause_lits_addr (ms_binary Mscan)).
  rewrite H_retval_6.
  subst retval_5.
  rewrite ?Z.mul_0_l, ?Z.mul_1_l, ?Z.add_0_r.
  cancel.
  split_pure_spatial.
  - cancel (solver_propagate_frame s_pre Mscan).
    cancel.
  - split_pures; dump_pre_spatial.
    all: lazymatch goal with
         | Hfact : ?P |- ?P => exact Hfact
         | |- clause_lits_pointer _ _ =>
             unfold clause_lits_pointer; reflexivity
         | |- Znth _ _ _ = _ =>
             rewrite H_tagged_enqueue_conflict_memory, replace_Znth_Znth;
             exact H_Znth
         | |- _ = replace_Znth _ _ _ =>
             rewrite H_tagged_enqueue_conflict_memory, replace_Znth_Znth;
             exact H_tagged_memory
         | |- propagation_binary_conflict_scan_ready _ _ _ _ _ _ _ =>
             unfold propagation_binary_conflict_scan_ready;
             split; [exact H_is_tag|];
             split; [exact Hheap_covers|];
             split; [exact Hreasonless|];
             split; [exact Hcurrent_level|];
             split; [exact H_simp_count|];
             split; [exact H_prop_count|];
             lia
         | _ => solve [auto | int_auto]
         end.
Qed.



Lemma proof_of_solver_propagate_entail_wit_8_scan_same : solver_propagate_entail_wit_8_scan_same.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  cancel.
  bind_fact ( retval_2 = tag_lit (Znth ii tagged_enqueue_conflict_memory 0) ) as H_retval_2.
  bind_fact ( scratch_base0 = clause_lits_addr (ms_binary Mscan) ) as H_scratch_base0.
  bind_fact ( retval = clause_lits_addr (ms_binary Mscan) ) as H_retval_ptr.
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( confl = ms_binary Mscan ) as H_confl.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth jj scan_current watch_memory )
      as H_tagged_enqueue_conflict_memory.
  rewrite <- H_scratch_base0.
  rewrite H_confl.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) tagged_enqueue_conflict_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin tagged_enqueue_conflict_memory cap);
    [ | first [lia | vec_buf_solve] .. ].
  cancel.
  Exists tagged_enqueue_conflict_memory (jj + 1) (ii + 1)
         (retval_2 :: lit_neg_c p :: nil) scratch_base0.
  cancel.
  unfold IntArray.full, IntArray.seg, store_array.
  split_pure_spatial.
  - rewrite H_Znth in H_retval_2.
    rewrite H_retval_ptr, <- H_scratch_base0.
    simpl.
    split_pure_spatial.
    + change (sizeof (INT)) with 4 in *.
      cancel.
      cancel.
      cancel (solver_propagate_frame s_pre Mscan).
      repeat cancel.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures; dump_pre_spatial;
      solve [auto | lia | msat_binary_copy_start_close raw_suffix H_watch_memory
        H_Zlength_2 H_tagged_enqueue_conflict_memory H_retval_2 H_Znth].
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_3_scan_same : solver_propagate_entail_wit_11_3_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap);
    [ | subst candidate_post_memory; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_6_scan_same : solver_propagate_entail_wit_11_6_scan_same.
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



Lemma proof_of_solver_propagate_entail_wit_20_14_real_satisfied : solver_propagate_entail_wit_20_14_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_19_real_satisfied : solver_propagate_entail_wit_20_19_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_23_2_binary_keep : solver_propagate_entail_wit_23_2_binary_keep.
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



Lemma proof_of_solver_propagate_partial_solve_wit_257_scan_same_pure : solver_propagate_partial_solve_wit_257_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_309_scan_same_pure : solver_propagate_partial_solve_wit_309_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_413_scan_same_pure : solver_propagate_partial_solve_wit_413_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcand : 0 <= candidate).
  { assert (Hv : 0 <= lit_var_c candidate) by assumption.
    unfold lit_var_c in Hv.
    destruct (Z_lt_le_dec candidate 0) as [Hneg | Hok]; [| exact Hok].
    assert (candidate / 2 < 0) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  prop_apply_p (store_int_range (lits + offset * sizeof(INT)) candidate).
  Intros_p Hrange.
  change Int.max_signed with 2147483647 in Hrange.
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_propagate_return_wit_2 : solver_propagate_return_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename M1 into Mcur.
bind_fact (solver_shape Mcur) as Hshape.
bind_fact (solver_propagation_loop_inv n F A_arr K M0 Mcur cf) as Hloop.
bind_fact (minisat_propagation_reuse_loop n M0 Mcur cf) as Hreuse.
destruct Hloop as [Hframe [[Hzero Hinv] | [Hnonzero Hconflict]]].
- destruct Hreuse as [Hcompleted [Hresident Hconflict_resident]].
  assert (Hdrained : mt_qhead (ms_core Mcur) = ms_qtail Mcur) by lia.
  assert (Hlive : minisat_propagation_reuse_live M0 Mcur).
  { split. intro Hentry. exact (proj1 (Hcompleted Hentry) Hzero). exact Hresident. }
  sep_apply (solver_propagation_open_refold__propagate s_pre Mcur assigns_entry rsn levels_entry trl wlists_entry Hshape).
  Exists Mcur. msat_manual_entailer_with ltac:(lia || tauto).
- contradiction.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_6 : solver_propagate_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (msat_propagate_watch_current_write_refold watch_memory ii jj source_words raw_prefix scan_current raw_suffix begin PreH1 PreH2 PreH3 PreH4).
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_25 : solver_propagate_which_implies_wit_25.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (msat_propagate_watch_current_write_refold watch_memory ii jj source_words raw_prefix scan_current raw_suffix begin PreH1 PreH2 PreH3 PreH4).
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_19 : solver_propagate_which_implies_wit_19.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_entry.
  bind_fact ( tagged_word scan_current ) as H_tagged_word.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  unfold enqueue_post_at.
  Intros qtail' assigns' levels' reasons' trail'.
  unfold enqueue_state_at.
  Intros rsn_enqueue trl_enqueue.
  assert (Hpostbound : 0 <= qtail' <= ms_cap Mscan).
  { (repeat split; solve [auto | (lia)]). }
  pose proof (msat_scan_keep_step_exists source_words retained moved rest
    garbage watch_memory raw_suffix ii jj scan_current
    H_propagation_watch_scan_physical H_rest) as Hphysical.
  pose proof H_solver_propagation_scan_semantics as Hsemkeep.
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [Hlive | Hconflict].
  2: { decompose [and] Hconflict; lia. }
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hcovers &
     Hreasonless & Hplevel & Hp_wf & Hprocessed & Hfrontier & Hcarrier).
  destruct (msat_propagate_weak_core_fields n F A_arr K Mscan Hweak) as
    (Hdbwf & Htwf & Hshape & Hwmexact & Hstable & Hreasonsmem & Hreasonbin &
     Hsize).
  destruct (msat_scan_current_focus_facts n Mscan p scan_current qtail'
    assigns' levels' reasons' trail' retained rest raw_suffix
    Hdbwf Hwmexact Hp_wf Hprocessed H_tagged_word H_rest Hcarrier H) as
    (Hqwf & Hwmword & Hcarrier_scan).
  rewrite H_rest in Hreuse_entry.
  pose proof (level_of_msolver_view_levels__analyze n Mscan (lit_var_c p)
    (Zlength (mt_lim (ms_core Mscan))) Htwf Hplevel) as Hfocus_cell.
  pose proof (minisat_propagation_reuse_enqueue__api_reentry
    n M0 Mscan p (scan_current :: raw_suffix) (tag_lit scan_current)
    (tag_of_lit p) (lit_denote (tag_lit scan_current) :: literal_neg (lit_denote p) :: nil)
    Hdbwf Htwf Hp_wf Hqwf Hprocessed Hreuse_entry) as Hreuse_enqueued.
  pose proof H as Henqueue.
  unfold enqueue_transition in H.
  destruct H as [Hsame | [Hconflict | Hfresh]].
  - destruct Hsame as
      (Hqtrue & _ & Hassigneq & Hlevelseq & Hreasonseq & Htraileq & Hqtaileq).
    pose proof (msat_enqueue_same_identity Mscan p scan_current Hqtrue)
      as HMidentity.
    pose proof (msat_scan_step_semantics_keep n F A_arr K Mscan p
      scan_current retained rest raw_suffix Hsemkeep Hcarrier_scan) as Hsem'.
    assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mscan p 0 raw_suffix).
    { rewrite HMidentity in Hreuse_enqueued.
      eapply minisat_propagation_reuse_advance__api_reentry;
        [exact Hreuse_enqueued|].
      apply (minisat_base_focus_word_completed_binary__api_reentry
        n Mscan p scan_current Hdbwf H_tagged_word).
      apply (propagation_true_partner_base_completed__api_reentry
        n (ms_core Mscan) p (tag_lit scan_current) Htwf Hqwf Hfocus_cell Hqtrue). }
    destruct Hphysical as [garbage_route [memory_route Hphysical]].
    subst assigns' levels' reasons' trail' qtail'.
    Exists garbage_route memory_route Mscan raw_suffix
      (retained ++ scan_current :: nil).
    unfold propagation_binary_keep_transition.
    Exists (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)).
    unfold enqueue_state_at.
    Exists rsn_enqueue trl_enqueue.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - decompose [and] Hconflict; lia.
  - destruct Hfresh as
      (Hfreshcell & _ & Hassigneq & Hlevelseq & Hreasonseq & Htraileq &
       Hqtaileq).
    pose proof (msat_enqueue_fresh_scan_semantics n F A_arr K Mscan p
      scan_current retained rest raw_suffix Hsemkeep H_tagged_word H_rest
      Hqwf Hwmword Hcarrier_scan Hfreshcell
      ltac:(rewrite Hqtaileq in Hpostbound; lia)) as Hsem'.
    set (q := tag_lit scan_current) in *.
    set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))
      in *.
    set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      rc) in *.
    assert (Hdbpost : db_wf n (msolver_db Mpost)).
    { unfold Mpost, msolver_propagation_enqueue_success.
      destruct (Z.eqb (Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0) 0);
        exact Hdbwf. }
    assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mpost p 0 raw_suffix).
    { eapply minisat_propagation_reuse_advance__api_reentry;
        [exact Hreuse_enqueued|].
      apply (minisat_base_focus_word_completed_binary__api_reentry
        n Mpost p scan_current Hdbpost H_tagged_word).
      apply (propagation_enqueue_partner_base_completed__api_reentry
        n Mscan p q (tag_of_lit p) rc Htwf Hp_wf Hqwf Hprocessed Hfocus_cell).
      left. exact Hfreshcell. }
    destruct Hphysical as [garbage_route [memory_route Hphysical]].
    subst assigns' levels' reasons' trail' qtail'.
    Exists garbage_route memory_route Mpost raw_suffix
      (retained ++ scan_current :: nil).
    unfold propagation_binary_keep_transition.
    Exists (ms_qtail Mscan + 1)
      (replace_Znth (lit_var_c q) (lit_sig q)
        (mt_assigns (ms_core Mscan)))
      (replace_Znth (lit_var_c q) (Zlength (mt_lim (ms_core Mscan)))
        (mt_levels (ms_core Mscan)))
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan))
      (mt_trail (ms_core Mscan) ++ q :: nil).
    unfold enqueue_state_at.
    Exists rsn_enqueue trl_enqueue.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_22 : solver_propagate_which_implies_wit_22.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( 2 <= Zlength clause_contents ) as H_Zlength.
  destruct clause_contents as [|a0 [|a1 tail]]; [cbn in H_Zlength; lia .. |].
  pose proof (Zlength_nonneg tail).
  rewrite !sublist_cons2, sublist_self by (rewrite ?Zlength_cons; lia).
  sep_apply_l_atomic (IntArray.full_unfold clause_base (Zlength (a0 :: a1 :: tail)) (a1 :: tail) a0).
  sep_apply_l_atomic (IntArray.seg_unfold clause_base 1 (Zlength (a0 :: a1 :: tail)) tail a1).
  csimpl.
  change (Znth 0 (a0 :: a1 :: tail) 0) with a0.
  change (Znth 1 (a0 :: a1 :: tail) 0) with a1.
  replace (1 + 1) with 2 by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_29 : solver_propagate_which_implies_wit_29.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold clause_db_pair_frame.
  Exists is_learnt_scan.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_40 : solver_propagate_which_implies_wit_40.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same.
  - cancel.
  - rewrite Zlength_sublist; lia.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_45 : solver_propagate_which_implies_wit_45.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stats_propagations in *.
  pose proof (msat_propagate_scan_db_wf _ _ _ _ _ _ _ _ PreH5) as Hdbwf.
  sep_apply (propagation_migrated_clause_db_rebuild__propagate_dbu n (ms_prob Mscan)
      (ms_learnt Mscan) scan_current lits stop k offset false_lit p candidate (2 * lit_sign_c
      candidate - 1) watch0 clause_contents Hdbwf PreH21).
  Intros prob_after learnt_after.
  destruct (msat_propagate_real_migrated_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH7 PreH8 PreH9 PreH12 PreH13 PreH17 PreH18 PreH19
      PreH21 PreH22 PreH23 PreH25 PreH26 PreH27 ltac:(eassumption) PreH6)
      as [Hwmlen [Htargetrange [Htargetneq [Hexit Hreuseroute]]]].
  inversion PreH24; subst destination_index destination_ptr destination_words.
  change (Vecp.rep (Vecp.slot wlists_entry (lit_neg_c candidate))
      (Znth (lit_neg_c candidate) scan_wm nil ++ (scan_current :: nil)))
    with (VecpArray.vec_store wlists_entry (lit_neg_c candidate)
      (Znth (lit_neg_c candidate) scan_wm nil ++ (scan_current :: nil))).
  sep_apply (VecpArray.missing2_merge_to_missing_i wlists_entry p (lit_neg_c candidate) (2 * n)
      scan_wm (Znth (lit_neg_c candidate) scan_wm nil ++ (scan_current :: nil)));
    [ | lia | lia | lia ].
  sep_apply (store_ptr_undef_store_ptr (&("k"))).
  sep_apply (store_ptr_undef_store_ptr (&("stop"))).
  sep_apply (store_ptr_undef_store_ptr (&("lits"))).
  Exists (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
      (propagation_move_wmap p (lit_neg_c candidate) scan_wm
      (retained ++ raw_suffix) scan_current)) (garbage ++ (scan_current :: nil))
      raw_suffix (moved ++ (scan_current :: nil)) prob_after learnt_after.
  msat_manual_entailer_with ltac:(first [assumption | reflexivity]).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_57 : solver_propagate_which_implies_wit_57.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin 0 jj (sublist 0 jj candidate_post_memory)).
  Intros.
  prop_apply_p (PtrArray.seg_valid begin (jj + 1) ii
    (sublist (jj + 1) ii candidate_post_memory)).
  Intros.
  prop_apply_p (PtrArray.seg_valid begin (ii + 1) (Zlength source_words)
    (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
  Intros.
  sep_apply (PtrArray.seg_single begin jj scan_current).
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj candidate_post_memory) (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
    (sublist 0 jj candidate_post_memory ++ scan_current :: nil)
    (sublist (jj + 1) ii candidate_post_memory) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    ((sublist 0 jj candidate_post_memory ++ scan_current :: nil) ++
      sublist (jj + 1) ii candidate_post_memory)
    (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (((sublist 0 jj candidate_post_memory ++ scan_current :: nil) ++
      sublist (jj + 1) ii candidate_post_memory) ++ scan_current :: nil)
    (sublist (ii + 1) (Zlength source_words) candidate_post_memory) ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  assert (Htail :
    sublist (jj + 1) (Zlength candidate_post_memory) candidate_post_memory =
      sublist (jj + 1) ii candidate_post_memory ++
        scan_current :: sublist (ii + 1) (Zlength candidate_post_memory)
          candidate_post_memory).
  {
    rewrite (sublist_split (jj + 1) (Zlength candidate_post_memory) ii) by lia.
    rewrite (sublist_split ii (Zlength candidate_post_memory) (ii + 1)) by lia.
    rewrite (sublist_single 0 ii candidate_post_memory) by lia.
    rewrite PreH1.
    reflexivity.
  }
  pose proof (Znth_split 0 candidate_post_memory jj ltac:(lia)) as Hsplit.
  assert (Hreplace :
    replace_Znth jj scan_current candidate_post_memory =
      sublist 0 jj candidate_post_memory ++
        scan_current :: sublist (jj + 1) (Zlength candidate_post_memory)
          candidate_post_memory).
  {
    rewrite Hsplit at 1.
    rewrite replace_Znth_app_r by
      (rewrite Zlength_sublist by lia; lia).
    rewrite replace_Znth_nothing by
      (rewrite Zlength_sublist by lia; lia).
    rewrite Zlength_sublist by lia.
    replace (jj - (jj - 0)) with 0 by lia.
    unfold replace_Znth.
    simpl.
    reflexivity.
  }
  rewrite Hreplace, Htail.
  rewrite <- !app_assoc.
  simpl.
  rewrite <- PreH2.
  cancel.
Qed.
