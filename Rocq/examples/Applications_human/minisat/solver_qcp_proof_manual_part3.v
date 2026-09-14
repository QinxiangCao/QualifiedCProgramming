Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_goal.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_common.
Local Open Scope sac.

(* Part 3 of the manual proof corpus. C-function families in source order:
   assume, enqueue, selectionsort, solver_analyze, solver_lit_removable,
   solver_propagate, solver_search, solver_simplify, solver_solve, sortrnd.
   Each family is marked by a section banner below. Shared tactic helpers
   and structural lemma helpers for solver_propagate's which_implies
   proofs precede the first family block. *)

(* The `clause_lits_pointer` side condition of the [solver_lit_removable]
   cancel step: the binary half of the analysis-cancel database yields the
   remainder pointer's well-formedness, whose evenness turns the C `c % 2`
   test into `Z.rem c 2 = 0` and lets the entailer close the pointer
   arithmetic.  [cn] is the variable count, [Mm] the model record, [cc] the
   clause handle, [lrn] its learnt flag and [cw] its word list. *)
Ltac msat_lit_removable_lits_pointer_even_p3 cn Mm cc lrn cw :=
  let Hdb_bin := fresh "Hdb_bin" in
  let Hdb := fresh "Hdb" in
  let Hptr_wf := fresh "Hptr_wf" in
  let Hpos := fresh "Hpos" in
  let Heven := fresh "Heven" in
  let Hrem := fresh "Hrem" in
  match goal with
  | Hready : analysis_cancel_ready ?n0 ?F0 ?A0 ?K0 ?M1 ?focus0 |- _ =>
      pose proof
        (analysis_cancel_ready_db_binary__lit_removable
          n0 F0 A0 K0 M1 focus0 Hready) as Hdb_bin
  end;
  destruct Hdb_bin as [Hdb _];
  prop_apply_p
    (clause_db_pair_remainder_ptr_wf__lit_removable
      cn (ms_prob Mm) (ms_learnt Mm) cc lrn cw Hdb);
  Intros_p Hptr_wf;
  destruct Hptr_wf as [Hpos Heven];
  assert (Hrem : Z.rem cc 2 = 0)
    by (apply Z.rem_divide; [lia |];
        apply Z.mod_divide; [lia | exact Heven]);
  unfold clause_lits_pointer;
  entailer_with ltac:(lia).

(* The activity-vector length side conditions of the [solver_search] decision
   loop: the model invariant carried by the loop assertion fixes that length,
   which is all the entailment needs.  [nn], [FF], [AA] and [AI] are the
   invariant's size, formula and assignment arguments, [MM] the model. *)
Ltac msat_search_activity_length_close_p3 nn FF AA AI MM :=
  let H_inv := fresh "H_msolver_inv" in
  bind_fact ( msolver_inv nn FF AA AI MM ) as H_inv;
  msat_search_close_activity_length_from_shape H_inv MM.

(* The literal-index range side conditions of [solver_lit_removable]: once the
   entailer has taken the goals it can, what is left is the parity argument on
   the C literal encoding, i.e. [lit_var_c] together with the division and
   remainder equations for the literal [x]. *)
Tactic Notation "msat_lit_var_parity_bounds_p3" ident(x) :=
  aggressive_pre_process;
  try entailer_with ltac:(lia); try lia;
  unfold lit_var_c in *;
  pose proof (Z.div_mod x 2 ltac:(lia));
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)); lia.

(* The [solver_simplify] post-condition frame: unfold the post at the caller's
   model, hand the levels array back through the assigns/levels split lemma and
   take the left-left arm using the two conditional properties exported by
   the post-propagation cut.  [Msp] is the caller's
   model, [Mp] the model after propagation, [sp] the solver pointer, [ap] the
   propagated assignment vector and [lp] the levels pointer. *)
Ltac msat_simplify_propagation_frame_p3 Msp Mp sp ap lp wl :=
  let Hempty := fresh "H_model_empty" in
  let Hpositive := fresh "H_decay_positive" in
  bind_fact ( ms_model Msp = nil -> ms_model Mp = nil ) as Hempty;
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Msp) ->
    msat_fp32_positive_finite (ms_cla_decay Mp) ) as Hpositive;
  unfold solver_simplify_post_at;
  sep_apply_l_atomic
    (solver_rep_assigns_levels_at_levels_at sp Mp ap lp wl);
  Left; Left;
  Exists Mp;
  entailer_with ltac:(lia);
  assumption.

(* The literal-range side condition of the watcher-scan `move` step: the scan
   semantics and the solver shape carried by the loop assertion together bound
   the literal being inspected.  [nn], [FF], [AA] and [KK] are the scan's size,
   formula, assignment and clause-database arguments, [MM] the model, [pp] the
   watcher position and [ret]/[rest0] the retained and remaining watchers. *)
Ltac msat_propagate_scan_lit_range_p3 nn FF AA KK MM pp ret rest0 :=
  let Hsem := fresh "H_solver_propagation_scan_semantics" in
  let Hshape := fresh "H_solver_shape" in
  bind_fact ( solver_propagation_scan_semantics nn FF AA KK MM pp 0 ret rest0 )
    as Hsem;
  bind_fact ( solver_shape MM ) as Hshape;
  msat_propagate_close_scan_lit_range Hsem Hshape nn FF AA KK MM.

(* Keep the pointer size symbolic as ptr_size_Z -- hardcoding
   4 would stop the PtrArray lemma below from matching, and the goal carries the
   unfolded Arch32.ptr_size_Z while PtrArray's lemmas are stated over the
   derived alias, so move any sizeof(PTR) to the Arch alias and fold it back.
   The tactic bounds the missing cell's index by induction over the tagged
   memory and then merges the segment back into the full array.  [bg] is the
   array base, [k] the missing index, [src] the word list whose length bounds
   it, [mem] the tagged memory and [idx] the raw C byte offset. *)
Tactic Notation "msat_propagate_ptr_missing_merge_p3" ident(bg) ident(k)
    ident(src) ident(mem) ident(idx) :=
  assert (Hi : idx = bg + k * sizeof(PTR)) by lia;
  subst idx;
  pose proof (fun lo => ptrarray_missing_i_index_range__lit_removable bg k lo (Zlength src) mem) as Hbounds;
  prop_apply (Hbounds 0);
  Intros;
  try change (sizeof (PTR)) with ptr_size_Z; fold_arch;
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full bg k (Zlength src)
      (Znth k mem 0) mem).


(* The seven [solver_propagation_weak] projections this part reads at a scan
   step, taken in one pass so each caller cites the bundle instead of repeating
   the projection tactic per field. *)
Lemma msat_propagate_weak_core_fields_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver),
    solver_propagation_weak n F A_arr K Mscan ->
    db_wf n (msolver_db Mscan) /\
    mtrail_wf n (ms_core Mscan) /\
    solver_shape Mscan /\
    wmap_exact n (msolver_db Mscan) (ms_wm Mscan) /\
    stable_view (msolver_view n Mscan) /\
    reasons_match n (ms_core Mscan) (msolver_db Mscan)
      (ms_reason_words Mscan) (ms_reason_of Mscan) /\
    binary_reason_same_level Mscan /\
    n = ms_size Mscan.
Proof.
  intros n F A_arr K Mscan Hweak.
  split. { msat_propagate_project_weak_field Hweak K (@msw_db_wf) (@msa_db_wf). }
  split. { msat_propagate_project_weak_field Hweak K (@msw_trail_wf) (@msa_trail_wf). }
  split. { msat_propagate_project_weak_field Hweak K (@msw_shape) (@msa_shape). }
  split.
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact) (@msa_wmap_exact). }
  split. { msat_propagate_project_weak_field Hweak K (@msw_stable) (@msa_stable). }
  split.
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_mem) (@msa_reasons_mem). }
  split.
  { msat_propagate_project_weak_field Hweak K (@msw_reason_bin) (@msa_reason_bin). }
  msat_propagate_project_weak_field Hweak K (@msw_size) (@msa_size).
Qed.

(* Every clause object of the scan-time database is entailed by the formula,
   in both the installed and the assuming propagation context. *)
Lemma msat_propagate_db_entailed_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver),
    solver_propagation_weak n F A_arr K Mscan ->
    forall ptr obj, In (ptr, obj) (msolver_db Mscan) ->
      entails_clause F (denote_obj obj).
Proof.
  intros n F A_arr K Mscan Hweak.
  intros ptr obj Hin.
  assert (Hinc : In (denote_obj obj) (msolver_clauses Mscan)).
  { unfold msolver_clauses. eapply db_clauses_in. exact Hin. }
  unfold solver_propagation_weak in Hweak.
  destruct K; destruct Hweak as [_ Hinv].
  - eapply msolver_inv_db_entailed; [exact Hinv|].
    rewrite msolver_view_installed. exact Hinc.
  - unfold msolver_clauses, msolver_db in Hinc.
    rewrite db_clauses_app in Hinc.
    apply in_app_or in Hinc as [Hprob | Hlearnt].
    + pose proof (msa_db_matches Hinv) as Hmatches.
      unfold db_matches_cnf in Hmatches.
      rewrite Forall_forall in Hmatches.
      destruct (Hmatches _ Hprob) as [c0 [Hc0 Hperm0]].
      eapply entails_clause_perm.
      * apply Permutation_sym. exact Hperm0.
      * apply entails_clause_in. exact Hc0.
    + pose proof (msa_db_implied Hinv) as Himplied.
      unfold db_implied in Himplied.
      rewrite Forall_forall in Himplied.
      exact (Himplied _ Hlearnt).
Qed.

(* Keeping the scanned word: the physical watcher layout of the step that moves
   [scan_current] from the pending suffix into the retained prefix, for either
   garbage shape. *)
Lemma msat_scan_keep_step_exists_p3 :
  forall (source_words retained moved rest garbage watch_memory
          raw_suffix : list Z) (ii jj scan_current : Z),
    propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ->
    rest = scan_current :: raw_suffix ->
    exists garbage_route memory_route,
      propagation_scan_keep_step source_words retained moved rest
        watch_memory ii jj scan_current (retained ++ scan_current :: nil)
        raw_suffix garbage_route memory_route.
Proof.
  intros source_words retained moved rest garbage watch_memory raw_suffix
    ii jj scan_current H_propagation_watch_scan_physical H_rest.
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as
    (Hscan & Hmemory & Hretlen & Hprefixlen & Hmemorylen).
  subst rest.
  destruct garbage as [|g gs].
  - exists nil, watch_memory.
    unfold propagation_scan_keep_step.
    split; [reflexivity|].
    split; [reflexivity|].
    split.
    + assert (Hnth : Znth jj watch_memory 0 = scan_current).
      {
        rewrite Hmemory.
        rewrite app_Znth2 by (rewrite Hretlen; lia).
        replace (jj - Zlength retained) with 0 by lia.
        reflexivity.
      }
      rewrite <- Hnth.
      symmetry. apply replace_Znth_Znth.
    + unfold propagation_watch_scan_physical.
      split. { apply wlist_scan_keep. exact Hscan. }
      split.
      { rewrite Hmemory.
        change (retained ++ (scan_current :: raw_suffix) =
          (retained ++ (scan_current :: nil)) ++ raw_suffix).
        rewrite <- app_assoc. reflexivity. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil, Hretlen. lia. }
      split.
      { rewrite app_nil_r in Hprefixlen.
        rewrite !Zlength_app. cbn. rewrite Hretlen. lia. }
      exact Hmemorylen.
  - exists (gs ++ scan_current :: nil),
      (replace_Znth jj scan_current watch_memory).
    unfold propagation_scan_keep_step.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    unfold propagation_watch_scan_physical.
    split. { apply wlist_scan_keep. exact Hscan. }
    split.
    { rewrite Hmemory.
      rewrite replace_Znth_app_r by (rewrite Hretlen; lia).
      rewrite replace_Znth_nothing by lia.
      replace (jj - Zlength retained) with 0 by lia.
      cbn.
      rewrite <- !app_assoc. reflexivity. }
    split.
    { rewrite Zlength_app, Zlength_cons, Zlength_nil, Hretlen. lia. }
    split.
    { rewrite !Zlength_app in Hprefixlen |- *.
      rewrite !Zlength_app_cons.
      rewrite Zlength_cons in Hprefixlen.
      lia.
    }
    rewrite Zlength_replace_Znth. exact Hmemorylen.
Qed.

(* The scanned word is not the negation of an already-processed literal, on
   any of the three enqueue routes: the queue transition either keeps the cell
   as it is or writes a variable that was unassigned. *)
Lemma msat_scan_target_unprocessed_p3 :
  forall (n : Z) (Mscan : msolver) (p scan_current qtail' : Z)
         (assigns' levels' reasons' trail' : list Z),
    enqueue_transition (tag_lit scan_current) (tag_of_lit p)
      (ms_qtail Mscan) 1 qtail' (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)) (mt_lim (ms_core Mscan))
      assigns' levels' reasons' trail' ->
    lit_wf_c n (tag_lit scan_current) ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    ~ minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan))
        (literal_neg (lit_denote (tag_lit scan_current))).
Proof.
  intros n Mscan p scan_current qtail' assigns' levels' reasons' trail'
    H Hqwf Hprocessed.
  unfold enqueue_transition in H.
  destruct H as [Hsame | [Hconflict | Hfresh]].
  - destruct Hsame as (Hqtrue & _).
    rewrite <- (lit_denote_neg (tag_lit scan_current)) by
      (destruct Hqwf; lia).
    rewrite minisat_processed_denote by (apply lit_neg_c_wf; exact Hqwf).
    intros [Hnegtrue _].
    eapply lit_true_false_contra; [exact Hqtrue|].
    unfold lit_true in Hnegtrue.
    rewrite lit_var_c_neg, lit_sig_neg in Hnegtrue.
    unfold lit_false. exact Hnegtrue.
  - exfalso. decompose [and] Hconflict; lia.
  - destruct Hfresh as (Hfreshcell & _).
    intros [w [Hwwf [Hden Hproc]]].
    pose proof (processed_fresh_target_different
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) w (tag_lit scan_current)
      Hproc Hfreshcell) as Hneq.
    apply Hneq.
    pose proof (f_equal literal_var Hden) as Hvar.
    rewrite literal_var_neg, !lit_var_c_denote in Hvar.
    symmetry. exact Hvar.
Qed.

(* The focused scan word: it is a well-formed literal of a database entry that
   watches [p], it is one of the physical watcher words stored at [p], and
   moving it into the retained prefix preserves the occurrence carrier. *)
Lemma msat_scan_current_focus_facts_p3 :
  forall (n : Z) (Mscan : msolver) (p scan_current qtail' : Z)
         (assigns' levels' reasons' trail' retained rest raw_suffix : list Z),
    db_wf n (msolver_db Mscan) ->
    wmap_exact n (msolver_db Mscan) (ms_wm Mscan) ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    tagged_word scan_current ->
    rest = scan_current :: raw_suffix ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      retained rest ->
    enqueue_transition (tag_lit scan_current) (tag_of_lit p)
      (ms_qtail Mscan) 1 qtail' (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)) (mt_lim (ms_core Mscan))
      assigns' levels' reasons' trail' ->
    lit_wf_c n (tag_lit scan_current) /\
    In scan_current (Znth p (ms_wm Mscan) nil) /\
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix.
Proof.
  intros n Mscan p scan_current qtail' assigns' levels' reasons' trail'
    retained rest raw_suffix
    Hdbwf Hwmexact Hp_wf Hprocessed H_tagged_word H_rest Hcarrier Henqueue.
  unfold tagged_word in H_tagged_word.
  unfold minisat_focus_scan_carrier in Hcarrier.
  destruct Hcarrier as
    [scanned [pending [Hperm [Hscanned_words [Hpending_words Hsafe]]]]].
  rewrite H_rest in Hpending_words.
  destruct pending as [|[focus_owner focus_word] pending'];
    [discriminate|].
  cbn in Hpending_words.
  injection Hpending_words as Hword Hpending_words.
  subst focus_word.
  assert (Htoken : In (focus_owner, scan_current)
    (minisat_focus_contributions (msolver_db Mscan) p)).
  {
    eapply Permutation_in; [exact Hperm|].
    apply in_or_app. right. left. reflexivity.
  }
  unfold minisat_focus_contributions in Htoken.
  apply in_flat_map in Htoken as [[clause_ptr co] [Hco Hentry]].
  unfold minisat_entry_focus_contributions in Hentry.
  apply in_map_iff in Hentry as [entry_word [Hentry Hentry_word]].
  inversion Hentry. subst focus_owner entry_word.
  assert (Hptr_not_tag : is_tag clause_ptr = false).
  {
    apply even_not_tag. eapply db_wf_even; eassumption.
  }
  assert (Hqwatch : tag_lit scan_current = co_watch0 co \/
                     tag_lit scan_current = co_watch1 co).
  {
    unfold entry_watchers in Hentry_word.
    apply in_app_or in Hentry_word as [Hfirst | Hsecond].
    - destruct ((lit_neg_c (co_watch0 co) =? p)%Z) eqn:Heq;
        [|cbn in Hfirst; contradiction].
      destruct ((3 <=? Zlength (co_lits co))%Z) eqn:Hbig;
        cbn in Hfirst; destruct Hfirst as [Hfirst | []].
      + subst scan_current. rewrite Hptr_not_tag in H_tagged_word. discriminate.
      + subst scan_current. rewrite tag_lit_of. right. reflexivity.
    - destruct ((lit_neg_c (co_watch1 co) =? p)%Z) eqn:Heq;
        [|cbn in Hsecond; contradiction].
      destruct ((3 <=? Zlength (co_lits co))%Z) eqn:Hbig;
        cbn in Hsecond; destruct Hsecond as [Hsecond | []].
      + subst scan_current. rewrite Hptr_not_tag in H_tagged_word. discriminate.
      + subst scan_current. rewrite tag_lit_of. left. reflexivity.
  }
  assert (Hqwf : lit_wf_c n (tag_lit scan_current)).
  {
    assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
    destruct Hqwatch as [Hqwatch | Hqwatch]; rewrite Hqwatch.
    - eapply obj_wf_watch0; eassumption.
    - eapply obj_wf_watch1; eassumption.
  }
  pose proof (msat_scan_target_unprocessed_p3 n Mscan p scan_current qtail'
    assigns' levels' reasons' trail' Henqueue Hqwf Hprocessed) as Hnotneg.
  assert (Hwmword : In scan_current (Znth p (ms_wm Mscan) nil)).
  {
    assert (Hexpect : In scan_current (expected_watchers (msolver_db Mscan) p)).
    {
      unfold expected_watchers. apply in_flat_map.
      exists (clause_ptr, co). split; assumption.
    }
    pose proof Hwmexact as [_ Hwm].
    eapply Permutation_in; [apply Permutation_sym; apply Hwm|exact Hexpect].
    exact Hp_wf.
  }
  assert (Hcurrsafe : minisat_occurrence_safe
    (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    (minisat_occurrence_of_entry (clause_ptr, co))).
  {
    unfold minisat_occurrence_safe, minisat_occurrence_of_entry.
    cbn [watch_left watch_right].
    destruct Hqwatch as [Hqw | Hqw]; rewrite <- Hqw; intros Hboth;
      apply Hnotneg; tauto.
  }
  assert (Hcarrier_scan : minisat_focus_scan_carrier
    (msolver_db Mscan) p
    (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    (retained ++ scan_current :: nil) raw_suffix).
  {
    unfold minisat_focus_scan_carrier.
    exists (scanned ++ (minisat_occurrence_of_entry (clause_ptr, co),
      scan_current) :: nil), pending'.
    split.
    + rewrite <- app_assoc. exact Hperm.
    + split.
      * rewrite <- Hscanned_words.
        unfold minisat_focus_words.
        rewrite map_app. reflexivity.
      * split; [exact Hpending_words|].
        apply Forall_app. split; [exact Hsafe|].
        constructor; [exact Hcurrsafe|constructor].
  }
  split; [exact Hqwf|].
  split; [exact Hwmword|exact Hcarrier_scan].
Qed.

(* Enqueueing a literal whose cell already carries its own sign leaves the
   solver model unchanged. *)
Lemma msat_enqueue_same_identity_p3 :
  forall (Mscan : msolver) (p scan_current : Z),
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 =
      lit_sig (tag_lit scan_current) ->
    msolver_propagation_enqueue_success Mscan
      (tag_lit scan_current) (tag_of_lit p)
      (cons (lit_denote (tag_lit scan_current))
        (cons (literal_neg (lit_denote p)) nil)) = Mscan.
Proof.
  intros Mscan p scan_current Hqtrue.
  unfold msolver_propagation_enqueue_success.
  destruct ((Znth (lit_var_c (tag_lit scan_current))
    (mt_assigns (ms_core Mscan)) 0 =? 0)%Z) eqn:Heq.
  - apply Z.eqb_eq in Heq. rewrite Hqtrue in Heq.
    exfalso. apply (lit_sig_nonzero (tag_lit scan_current)). exact Heq.
  - reflexivity.
Qed.

(* Re-packaging the live scan semantics once the focused word has moved into
   the retained prefix: only the carrier conjunct changes. *)
Lemma msat_scan_step_semantics_keep_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z) (retained rest raw_suffix : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix ->
    solver_propagation_scan_semantics n F A_arr K Mscan p 0
      (retained ++ scan_current :: nil) raw_suffix.
Proof.
  intros n F A_arr K Mscan p scan_current retained rest raw_suffix
    Hsem Hcarrier_scan.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconflict]; [|decompose [and] Hconflict; lia].
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hcovers &
     Hreasonless & Hplevel & Hp_wf & Hprocessed & Hfrontier & Hcarrier).
  unfold solver_propagation_scan_semantics. left.
  split; [reflexivity|].
  split; [exact Hweak|].
  split; [exact Hproplevel|].
  split; [exact Hheapready|].
  split; [exact Hcovers|].
  split; [exact Hreasonless|].
  split; [exact Hplevel|].
  split; [exact Hp_wf|].
  split; [exact Hprocessed|].
  split; [exact Hfrontier|exact Hcarrier_scan].
Qed.

(* The enqueue-success model of a variable whose assignment cell is still
   clear is exactly the propagation overlay that writes the four cells. *)
Lemma msat_enqueue_success_overlay_form_p3 :
  forall (Mscan : msolver) (p q : Z),
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) =
    msolver_propagation_overlay Mscan (mt_enqueue (ms_core Mscan) q)
      (ms_qtail Mscan + 1)
      (replace_Znth (lit_var_c q) (tag_of_lit p) (ms_reason_words Mscan))
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
        (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
      (ms_prob Mscan) (ms_learnt Mscan) (ms_binary_lits Mscan)
      (ms_wm Mscan) (ms_wcaps Mscan) (ms_stats Mscan).
Proof.
  intros Mscan p q Hfreshcell.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hfreshb : (Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0
    =? 0)%Z = true) by (apply Z.eqb_eq; exact Hfreshcell).
  unfold Mpost, msolver_propagation_enqueue_success.
  rewrite Hfreshb. reflexivity.
Qed.

(* The same model in the shared [msolver_enqueue_fresh] form that the record
   and propagation lemmas are stated over. *)
Lemma msat_enqueue_success_fresh_form_p3 :
  forall (Mscan : msolver) (p q : Z),
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) =
    msolver_enqueue_fresh Mscan q (tag_of_lit p) (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros Mscan p q Hfreshcell.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  unfold Mpost.
  apply propagation_enqueue_success_fresh__propagate_dbu.
  exact Hfreshcell.
Qed.

(* The binary reason recorded for the enqueued watcher word is entailed by the
   formula: it is the tag literal together with the negated focus literal. *)
Lemma msat_enqueue_fresh_reason_entailed_p3 :
  forall (n : Z) (F : cnf) (Mscan : msolver) (p scan_current : Z),
    db_wf n (msolver_db Mscan) ->
    wmap_exact n (msolver_db Mscan) (ms_wm Mscan) ->
    lit_wf_c n p ->
    In scan_current (Znth p (ms_wm Mscan) nil) ->
    tagged_word scan_current ->
    (forall ptr obj, In (ptr, obj) (msolver_db Mscan) ->
       entails_clause F (denote_obj obj)) ->
    entails_clause F
      (cons (lit_denote (tag_lit scan_current))
        (cons (literal_neg (lit_denote p)) nil)).
Proof.
  intros n F Mscan p scan_current Hdbwf Hwmexact Hp_wf Hwmword
    H_tagged_word Hdbent.
  set (q := tag_lit scan_current) in *.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  unfold rc.
  eapply tagged_reason_entailed.
  - exact Hdbwf.
  - exact Hwmexact.
  - exact Hp_wf.
  - exact Hwmword.
  - exact H_tagged_word.
  - exact Hdbent.
Qed.

(* Every literal of that reason is well formed. *)
Lemma msat_enqueue_fresh_reason_lits_wf_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    lit_wf_c n q ->
    lit_wf_c n p ->
    forall c k, Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) = Some c -> In k c -> literal_wf n k.
Proof.
  intros n Mscan p q Hqwf Hp_wf.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  intros c k Hc Hk. inversion Hc. subst c. unfold rc in Hk.
  destruct Hk as [<- | [<- | []]].
  - apply lit_denote_wf. exact Hqwf.
  - rewrite <- (lit_denote_neg p) by (destruct Hp_wf; lia).
    apply lit_denote_wf. apply lit_neg_c_wf. exact Hp_wf.
Qed.

(* The trail after the unit enqueue is still implied by the formula: the new
   entry is justified by its own binary reason. *)
Lemma msat_enqueue_fresh_trail_implied_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    mtrail_wf n (ms_core Mscan) ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    entails_clause F (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) ->
    trail_implied F (mt_enqueue (ms_core Mscan) q).
Proof.
  intros n F A_arr K Mscan p q Hweak Htwf Hprocessed Hreasonent.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  eapply trail_implied_unit with (rc := rc).
  - exact Htwf.
  - unfold solver_propagation_weak in Hweak.
    destruct K; destruct Hweak as [_ Hinv].
    + exact (msw_trail_impl Hinv).
    + exact (msa_trail_impl Hinv).
  - exact Hreasonent.
  - unfold rc. left. reflexivity.
  - intros k Hk Hkq.
    unfold rc in Hk.
    destruct Hk as [Hk | [Hk | []]]; [congruence|].
    subst k.
    destruct Hprocessed as [_ [idx [Hidx Hpidx]]].
    exists idx. split.
    { pose proof (mtw_qhead_range Htwf). lia. }
    rewrite literal_neg_involutive, Hpidx. reflexivity.
Qed.

(* The focus literal stays false after the enqueue: the enqueue writes a
   different variable, so the focus cell is untouched. *)
Lemma msat_enqueue_fresh_focus_false_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    lit_var_c q <> lit_var_c p ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    eval_partial_literal (assignment (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)))
      (literal_neg (lit_denote p)) = Some false.
Proof.
  intros n Mscan p q Hp_wf Hprocessed Hqpneq Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  assert (Hpviewtrue : eval_partial_literal (assignment (msolver_view n Mscan))
  (lit_denote p) = Some true).
  {
  destruct Hprocessed as [Hptrue _].
  pose proof (proj1 (lit_true_iff (mt_assigns (ms_core Mscan)) p
    (proj1 Hp_wf)) Hptrue) as Hpt.
  rewrite msolver_view_assignment.
  unfold eval_partial_literal in Hpt |- *.
  rewrite lit_var_c_denote.
  rewrite mt_pv_nonneg by
    (exact (proj1 (lit_var_c_in_range n p Hp_wf))).
  unfold assigns_pv, assigns_val in Hpt.
  rewrite lit_var_c_denote in Hpt.
  exact Hpt.
  }
  assert (Hpviewfalse : eval_partial_literal (assignment (msolver_view n Mscan))
  (literal_neg (lit_denote p)) = Some false).
  {
  rewrite eval_partial_literal_neg, Hpviewtrue. reflexivity.
  }
  pose proof (Hothers (lit_var_c p) (fun Heq => Hqpneq (eq_sym Heq)))
    as [Haeq _].
  unfold eval_partial_literal in Hpviewfalse |- *.
  rewrite literal_var_neg, lit_var_c_denote in Hpviewfalse.
  rewrite literal_var_neg, lit_var_c_denote, Haeq.
  exact Hpviewfalse.
Qed.

(* The new reason is a valid reason for the enqueued variable in the post
   view: its other literal is false and ranks below it. *)
Lemma msat_enqueue_fresh_reason_valid_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    lit_var_c q <> lit_var_c p ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    eval_partial_literal (assignment (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)))
      (literal_neg (lit_denote p)) = Some false ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reason_valid (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)).
Proof.
  intros n Mscan p q Hqpneq Hplevel Hp_post_false Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  exists (lit_pol q), (Zlength (mt_lim (ms_core Mscan))), rq.
  split; [exact Hqassigned|].
  split; [exact Hqlevel|].
  split; [exact Hqrank|].
  split.
  { unfold rc. left. rewrite lit_denote_satisfying. reflexivity. }
  intros l Hl Hlv.
  unfold rc in Hl.
  destruct Hl as [Hl | [Hl | []]].
  - subst l. rewrite lit_var_c_denote in Hlv. contradiction.
  - subst l.
    split; [exact Hp_post_false|].
    assert (Hdep : reason_dependency Vpost (lit_var_c q) (lit_var_c p)).
    {
      unfold reason_dependency.
      exists rc, (literal_neg (lit_denote p)).
      repeat split.
      - exact Hqreason.
      - unfold rc. right. left. reflexivity.
      - rewrite literal_var_neg, lit_var_c_denote. reflexivity.
      - intro Heq. apply Hqpneq. symmetry. exact Heq.
      - exact Hp_post_false.
    }
    destruct (Hdependencies (lit_var_c p) Hdep) as [rp [Hrp Hrplt]].
    exists (Zlength (mt_lim (ms_core Mscan))), rp.
    split.
    { pose proof (Hothers (lit_var_c p)
        (fun Heq => Hqpneq (eq_sym Heq))) as [_ [Hleq _]].
      rewrite literal_var_neg, lit_var_c_denote.
      rewrite Hleq. exact Hplevel. }
    split.
    { rewrite literal_var_neg, lit_var_c_denote. exact Hrp. }
    split; [lia|exact Hrplt].
Qed.

(* Stability is preserved by the unit enqueue: the only new assignment is the
   enqueued variable, grounded by its own reason. *)
Lemma msat_enqueue_fresh_stable_view_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    stable_view (msolver_view n Mscan) ->
    reason_valid (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    stable_view (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)).
Proof.
  intros n Mscan p q Hstable Hreasonvalidq Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  unfold stable_view in Hstable |- *.
  destruct Hstable as [Hground Hclosed]. split.
  - unfold grounded_at in Hground |- *.
    intros x b Hxb.
    destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
    + rewrite Hqassigned in Hxb. inversion Hxb. subst b.
      exists (Zlength (mt_lim (ms_core Mscan))), rq.
      split; [exact Hqlevel|]. split; [exact Hqrank|].
      right. exists rc. split; [exact Hqreason|exact Hreasonvalidq].
    + pose proof (Hothers x Hxq) as [Haeq [Hleq [Hreq Hrankeq]]].
      rewrite Haeq in Hxb.
      destruct (Hground x b Hxb) as [d [rx [Hlev [Hrank Hro]]]].
      exists d, rx. split; [rewrite Hleq; exact Hlev|].
      split; [rewrite Hrankeq; exact Hrank|].
      destruct Hro as [Hnone | [c [Hsome Hvalid]]].
      * left. rewrite Hreq. exact Hnone.
      * right. exists c. split; [rewrite Hreq; exact Hsome|].
        destruct Hvalid as
          [b0 [d0 [rx0 [Ha0 [Hl0 [Hr0 [Hin0 Hside]]]]]]].
        exists b0, d0, rx0.
        split; [rewrite Haeq; exact Ha0|].
        split; [rewrite Hleq; exact Hl0|].
        split; [rewrite Hrankeq; exact Hr0|].
        split; [exact Hin0|].
        intros l Hl Hlx.
        destruct (Hside l Hl Hlx) as [Heval [dy [ry [Hly [Hry Hord]]]]].
        assert (Hlq : literal_var l <> lit_var_c q).
        {
          intro Heq.
          destruct (eval_partial_literal_assigned _ _ _ Heval) as [bb Hbb].
          rewrite Heq, Hqnone in Hbb. discriminate.
        }
        pose proof (Hothers (literal_var l) Hlq)
          as [Hla [Hll [_ Hlr]]].
        split.
        { unfold eval_partial_literal in Heval |- *. rewrite Hla. exact Heval. }
        exists dy, ry. repeat split.
        { rewrite Hll. exact Hly. }
        { rewrite Hlr. exact Hry. }
        all: tauto.
  - unfold closed_levels in Hclosed |- *.
    destruct Hclosed as [Hcur [Hbound Hdec]].
    split; [exact Hcur|]. split.
    + intros x b d Hxb Hxd.
      destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
      * rewrite Hqlevel in Hxd. inversion Hxd. subst d.
        unfold Vpost. cbn [view_of mt_enqueue mt_push].
        split; [apply Zlength_nonneg|reflexivity].
      * pose proof (Hothers x Hxq) as [Haeq [Hleq _]].
        rewrite Haeq in Hxb. rewrite Hleq in Hxd.
        exact (Hbound x b d Hxb Hxd).
    + intros d Hd. destruct (Hdec d Hd) as [x [[b Hxb] [Hxl Hxr]]].
      assert (Hxq : x <> lit_var_c q).
      { intro Heq. subst x. rewrite Hqnone in Hxb. discriminate. }
      pose proof (Hothers x Hxq) as [Haeq [Hleq [Hreq _]]].
      exists x. split.
      * exists b. rewrite Haeq. exact Hxb.
      * split; [rewrite Hleq; exact Hxl|]. rewrite Hreq. exact Hxr.
Qed.

(* Every reason of the post view is entailed: the old ones are unchanged and
   the new one is the entailed binary reason. *)
Lemma msat_enqueue_fresh_reasons_entailed_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    entails_clause F (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reasons_entailed F (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)).
Proof.
  intros n F A_arr K Mscan p q Hweak Hreasonent Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  assert (Hold : reasons_entailed F (msolver_view n Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_ent) (@msa_reasons_ent). }
  unfold reasons_entailed in Hold |- *.
  intros x c Hxc.
  destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
  - rewrite Hqreason in Hxc. inversion Hxc. exact Hreasonent.
  - pose proof (Hothers x Hxq) as [_ [_ [Hreq _]]].
    apply (Hold x c). rewrite <- Hreq. exact Hxc.
Qed.

(* Reason literals stay variable-injective: the new reason mentions two
   distinct variables. *)
Lemma msat_enqueue_fresh_reasons_injective_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    lit_var_c q <> lit_var_c p ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reasons_var_injective (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)).
Proof.
  intros n F A_arr K Mscan p q Hweak Hqpneq Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  assert (Hold : reasons_var_injective (msolver_view n Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_inj) (@msa_reasons_inj). }
  unfold reasons_var_injective in Hold |- *.
  intros x c Hxc.
  destruct (Z.eq_dec x (lit_var_c q)) as [-> | Hxq].
  - rewrite Hqreason in Hxc. inversion Hxc. subst c.
    apply NoDup_map_var_injective. unfold rc.
    apply tagged_reason_nodup_vars. exact Hqpneq.
  - pose proof (Hothers x Hxq) as [_ [_ [Hreq _]]].
    apply (Hold x c). rewrite <- Hreq. exact Hxc.
Qed.

(* An assumption true at the root level stays true after the enqueue. *)
Lemma msat_enqueue_fresh_assump_at_root_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    0 <= lit_var_c q < n ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    forall root a,
      literal_wf n a ->
      assump_true_at_root (ms_core Mscan) root a ->
      assump_true_at_root (mt_enqueue (ms_core Mscan) q) root a.
Proof.
  intros n Mscan p q Htwf Hqrange Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  intros root a Hawf [Hatrue Halevel].
  assert (Hneq : literal_var a <> lit_var_c q).
  {
    intro Heq.
    destruct (eval_partial_literal_assigned _ _ _ Hatrue) as [b Hb].
    rewrite Heq in Hb.
    change (mt_pv (ms_core Mscan) (lit_var_c q) = None) in Hqnone.
    rewrite Hqnone in Hb. discriminate.
  }
  pose proof (Hothers (literal_var a) Hneq) as [Haeq _].
  change (mt_pv (mt_enqueue (ms_core Mscan) q) (literal_var a) =
    mt_pv (ms_core Mscan) (literal_var a)) in Haeq.
  split.
  - unfold eval_partial_literal in Hatrue |- *.
    rewrite Haeq. exact Hatrue.
  - unfold mt_enqueue, mt_push. cbn.
    unfold literal_wf, var_in_range in Hawf.
    change (Znth (literal_var a)
      (replace_Znth (lit_var_c q)
        (Zlength (mt_lim (ms_core Mscan)))
        (mt_levels (ms_core Mscan))) 0 <= root).
    rewrite (Znth_replace_Znth_Diff 0 (mt_levels (ms_core Mscan))
      (lit_var_c q) (literal_var a)
      (Zlength (mt_lim (ms_core Mscan)))).
    + exact Halevel.
    + rewrite (mtw_levels_len Htwf). exact Hqrange.
    + rewrite (mtw_levels_len Htwf). exact Hawf.
    + intro Heq. apply Hneq. symmetry. exact Heq.
Qed.

(* Off-cell agreement for the reason-word vector: the enqueue rewrites the
   cell of the enqueued variable and leaves every other cell alone. *)
Lemma msat_reason_word_offcell_agree_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    Zlength (ms_reason_words Mscan) = n ->
    0 <= lit_var_c q < n ->
    forall v, 0 <= v < n -> v <> lit_var_c q ->
      Znth v (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0 = Znth v (ms_reason_words Mscan) 0.
Proof.
  intros n Mscan p q Hwordslen Hqrange.
  { intros v Hv Hvq.
    apply (Znth_replace_Znth_Diff 0 (ms_reason_words Mscan)
      (lit_var_c q) v (tag_of_lit p));
      [rewrite Hwordslen; exact Hqrange|rewrite Hwordslen; exact Hv
      |intro E; apply Hvq; symmetry; exact E]. }
Qed.

(* Off-cell agreement for the level vector. *)
Lemma msat_level_cell_offcell_agree_p3 :
  forall (n : Z) (Mscan : msolver) (q : Z),
    mtrail_wf n (ms_core Mscan) ->
    0 <= lit_var_c q < n ->
    forall v, 0 <= v < n -> v <> lit_var_c q ->
      Znth v (replace_Znth (lit_var_c q) (Zlength (mt_lim (ms_core Mscan)))
        (mt_levels (ms_core Mscan))) 0 = Znth v (mt_levels (ms_core Mscan)) 0.
Proof.
  intros n Mscan q Htwf Hqrange.
  { intros v Hv Hvq.
    apply (Znth_replace_Znth_Diff 0 (mt_levels (ms_core Mscan))
      (lit_var_c q) v (Zlength (mt_lim (ms_core Mscan))));
      [rewrite (mtw_levels_len Htwf); exact Hqrange
      |rewrite (mtw_levels_len Htwf); exact Hv
      |intro E; apply Hvq; symmetry; exact E]. }
Qed.

(* Reason words and reason terms still agree after the enqueue: the enqueued
   cell carries its own tag and every other cell is unchanged. *)
Lemma msat_enqueue_fresh_reasons_match_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    lit_wf_c n p ->
    0 <= lit_var_c q < n ->
    Zlength (ms_reason_words Mscan) = n ->
    reasons_match n (ms_core Mscan) (msolver_db Mscan)
      (ms_reason_words Mscan) (ms_reason_of Mscan) ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    reasons_match n (mt_enqueue (ms_core Mscan) q) (msolver_db Mscan)
      (replace_Znth (lit_var_c q) (tag_of_lit p) (ms_reason_words Mscan))
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
        (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)))).
Proof.
  intros n Mscan p q Htwf Hp_wf Hqrange Hwordslen Hreasonsmem Hassignone.
  pose proof (msat_reason_word_offcell_agree_p3 n Mscan p q Hwordslen Hqrange)
    as Hoffq_words.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  unfold reasons_match. intros v Hv.
  destruct (Z.eq_dec v (lit_var_c q)) as [-> | Hvq].
  - rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
      (lit_var_c q) (tag_of_lit p));
      [|rewrite Hwordslen; exact Hqrange].
    rewrite sat_function_update_eq.
    assert (Hqcell : Znth (lit_var_c q)
      (mt_assigns (mt_enqueue (ms_core Mscan) q)) 0 <> 0).
    {
      unfold mt_enqueue, mt_push. cbn.
      change (Znth (lit_var_c q)
        (replace_Znth (lit_var_c q) (lit_sig q)
          (mt_assigns (ms_core Mscan))) 0 <> 0).
      rewrite (Znth_replace_Znth_Same 0 (mt_assigns (ms_core Mscan))
        (lit_var_c q) (lit_sig q));
        [apply lit_sig_nonzero|].
      rewrite (mtw_assigns_len Htwf). exact Hqrange.
    }
    pose proof (reason_word_of_tag (mt_enqueue (ms_core Mscan) q)
      (lit_var_c q) (msolver_db Mscan) p
      (proj1 Hp_wf) Hqcell) as Hok.
    change (mt_pv (mt_enqueue (ms_core Mscan) q) (lit_var_c q) =
      Some (lit_pol q)) in Hqassigned.
    pose proof (trail_lit_of_denote (mt_enqueue (ms_core Mscan) q)
      (lit_var_c q) (lit_pol q) (proj1 Hqrange) Hqassigned) as Hden.
    rewrite <- lit_denote_satisfying in Hden.
    unfold rc. rewrite Hden in Hok. exact Hok.
  - rewrite (Hoffq_words v Hv Hvq).
    rewrite sat_function_update_neq by (intro E; apply Hvq; symmetry; exact E).
    specialize (Hreasonsmem v Hv).
    assert (Hassignv : Znth v
      (mt_assigns (mt_enqueue (ms_core Mscan) q)) 0 =
      Znth v (mt_assigns (ms_core Mscan)) 0).
    {
      unfold mt_enqueue, mt_push. cbn.
      change (Znth v (replace_Znth (lit_var_c q) (lit_sig q)
        (mt_assigns (ms_core Mscan))) 0 =
        Znth v (mt_assigns (ms_core Mscan)) 0).
      rewrite (Znth_replace_Znth_Diff 0 (mt_assigns (ms_core Mscan))
        (lit_var_c q) v (lit_sig q));
        [reflexivity|rewrite (mtw_assigns_len Htwf); exact Hqrange
        |rewrite (mtw_assigns_len Htwf); exact Hv
        |intro E; apply Hvq; symmetry; exact E].
    }
    assert (Hlitv : trail_lit_of (mt_enqueue (ms_core Mscan) q) v =
      trail_lit_of (ms_core Mscan) v).
    { unfold trail_lit_of. rewrite Hassignv. reflexivity. }
    unfold reason_word_ok in Hreasonsmem |- *.
    rewrite Hassignv, Hlitv. exact Hreasonsmem.
Qed.

(* Tagged reason words still point at database entries after the enqueue. *)
Lemma msat_enqueue_fresh_reason_head_ok_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    0 <= lit_var_c q < n ->
    Zlength (ms_reason_words Mscan) = n ->
    n = ms_size Mscan ->
    reason_head_ok (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros n F A_arr K Mscan p q Hweak Hfreshcell Hqrange Hwordslen Hsize.
  pose proof (msat_enqueue_success_overlay_form_p3 Mscan p q Hfreshcell)
    as HMpost.
  pose proof (msat_reason_word_offcell_agree_p3 n Mscan p q Hwordslen Hqrange)
    as Hoffq_words.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hold : reason_head_ok Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_reason_head) (@msa_reason_head). }
  rewrite HMpost. unfold reason_head_ok in Hold |- *.
  cbn [msolver_propagation_overlay msolver_propagation_update ].
  intros v co0 Hv Htag Hnonzero Hin.
  destruct (Z.eq_dec v (lit_var_c q)) as [-> | Hvq].
  - change (is_tag (Znth (lit_var_c q)
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0) = false) in Htag.
    rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
      (lit_var_c q) (tag_of_lit p)) in Htag;
      [rewrite is_tag_of in Htag; discriminate|].
    rewrite Hwordslen. exact Hqrange.
  - change (is_tag (Znth v
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0) = false) in Htag.
    change (Znth v (replace_Znth (lit_var_c q) (tag_of_lit p)
      (ms_reason_words Mscan)) 0 <> 0) in Hnonzero.
    change (In (Znth v (replace_Znth (lit_var_c q) (tag_of_lit p)
      (ms_reason_words Mscan)) 0, co0) (msolver_db Mscan)) in Hin.
    rewrite (Hoffq_words v ltac:(rewrite Hsize; exact Hv) Hvq)
      in Htag, Hnonzero, Hin.
    eapply Hold; eassumption.
Qed.

(* The focus literal was assigned at the current decision level. *)
Lemma msat_scan_focus_level_is_root_p3 :
  forall (n : Z) (Mscan : msolver) (p : Z),
    mtrail_wf n (ms_core Mscan) ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0 =
      Zlength (mt_lim (ms_core Mscan)).
Proof.
  intros n Mscan p Htwf Hprocessed Hplevel.
  destruct Hprocessed as [Hptrue [ip [Hip Hptrail]]].
  assert (Hipfull : 0 <= ip < Zlength (mt_trail (ms_core Mscan))).
  { pose proof (mtw_qhead_range Htwf). lia. }
  pose proof (trail_pos_of_index (ms_core Mscan) ip
    (mtw_trail_nodup Htwf) Hipfull) as Hpos.
  unfold trail_var in Hpos. rewrite Hptrail in Hpos.
  unfold msolver_view, view_of in Hplevel. cbn in Hplevel.
  rewrite Hpos in Hplevel.
  cbn in Hplevel.
  assert (Hidxlevel : level_of_index (ms_core Mscan) ip =
    Zlength (mt_lim (ms_core Mscan))).
  { rewrite <- (Z2Nat.id ip) by lia. now injection Hplevel. }
  pose proof (mtw_levels_agree Htwf ip Hipfull) as Hagree.
  unfold trail_var in Hagree. rewrite Hptrail in Hagree.
  rewrite Hagree. exact Hidxlevel.
Qed.

(* No tagged reason word already targets the variable being enqueued: such a
   word would make its target assigned, and the enqueued cell is clear. *)
Lemma msat_no_old_tag_targets_fresh_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    n = ms_size Mscan ->
    stable_view (msolver_view n Mscan) ->
    reasons_match n (ms_core Mscan) (msolver_db Mscan)
      (ms_reason_words Mscan) (ms_reason_of Mscan) ->
    binary_reason_same_level Mscan ->
    assigns_one (msolver_view n Mscan)
      (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) (lit_var_c q) (lit_pol q)
      (Zlength (mt_lim (ms_core Mscan)))
      (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    forall v, 0 <= v < n ->
      is_tag (Znth v (ms_reason_words Mscan) 0) = true ->
      lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> lit_var_c q.
Proof.
  intros n Mscan p q Htwf Hsize Hstable Hreasonsmem Hreasonbin Hassignone.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  intros v Hv Htag Heqtarget.
  pose proof (Hreasonsmem v Hv) as Hmatch.
  assert (Hwordnonzero : Znth v (ms_reason_words Mscan) 0 <> 0).
  { intro Hz. rewrite Hz in Htag. discriminate. }
  pose proof (reason_word_ok_nonzero_assigned
    (ms_core Mscan) v (msolver_db Mscan)
    (Znth v (ms_reason_words Mscan) 0) (ms_reason_of Mscan v)
    Hwordnonzero Hmatch) as Hvcell.
  assert (Hassignv : exists b,
    assignment (msolver_view n Mscan) v = Some b).
  {
    change (exists b, mt_pv (ms_core Mscan) v = Some b).
    destruct (mt_pv (ms_core Mscan) v) as [b|] eqn:Hpv;
      [eauto|exfalso].
    apply (proj1 (mt_pv_none_iff n (ms_core Mscan) v Htwf)) in Hpv.
    apply Hpv. apply (proj1 (mtw_assigned_iff Htwf v Hv)). exact Hvcell.
  }
  destruct Hassignv as [b Hassignv].
  pose proof (Hreasonbin v (ltac:(rewrite <- Hsize; exact Hv)) Htag)
    as [Htargetwf [Hlevelsold Htargetneold]].
  assert (Hwordpos : 0 < Znth v (ms_reason_words Mscan) 0).
  { eapply tag_pos_of_lit_wf; eassumption. }
  pose proof (reason_word_ok_tag (ms_core Mscan) v (msolver_db Mscan)
    (Znth v (ms_reason_words Mscan) 0) (ms_reason_of Mscan v)
    Hwordpos Htag Hmatch) as Hraw.
  assert (Hviewraw : reason_of (msolver_view n Mscan) v =
    ms_reason_of Mscan v).
  {
    unfold msolver_view, view_of. cbn.
    destruct (trail_pos (ms_core Mscan) v) eqn:Hpos.
    - reflexivity.
    - apply (proj2 (view_unassigned_iff n (ms_core Mscan) v Htwf)) in Hpos.
      change (mt_pv (ms_core Mscan) v = Some b) in Hassignv.
      rewrite Hpos in Hassignv. discriminate.
  }
  destruct Hstable as [Hground _].
  destruct (Hground v b Hassignv) as [d [rv [Hvlev [Hvrank Hgroundv]]]].
  destruct Hgroundv as [Hnone | [c [Hsome Hvalid]]].
  - rewrite Hviewraw, Hraw in Hnone. discriminate.
  - rewrite Hviewraw, Hraw in Hsome. inversion Hsome. subst c.
    unfold reason_valid in Hvalid.
    destruct Hvalid as [b0 [d0 [r0
      [Ha0 [Hl0 [Hr0 [Hhead Hside]]]]]]].
    specialize (Hside
      (literal_neg (lit_denote
        (tag_lit (Znth v (ms_reason_words Mscan) 0))))
      (or_intror (or_introl eq_refl))).
    assert (Htargetne : literal_var
      (literal_neg (lit_denote
        (tag_lit (Znth v (ms_reason_words Mscan) 0)))) <> v).
    {
      rewrite literal_var_neg, lit_var_c_denote.
      exact Htargetneold.
    }
    specialize (Hside Htargetne).
    destruct Hside as [Hfalse _].
    destruct (eval_partial_literal_assigned _ _ _ Hfalse) as [bt Hbt].
    rewrite literal_var_neg, lit_var_c_denote, Heqtarget in Hbt.
    rewrite Hqnone in Hbt. discriminate.
Qed.

(* Binary reason words keep their same-level invariant after the enqueue: the
   new cell carries the focus tag at the current level, and the old cells are
   unchanged and never target the enqueued variable. *)
Lemma msat_enqueue_fresh_reason_bin_p3 :
  forall (n : Z) (Mscan : msolver) (p q : Z),
    mtrail_wf n (ms_core Mscan) ->
    lit_wf_c n p ->
    n = ms_size Mscan ->
    Zlength (ms_reason_words Mscan) = n ->
    0 <= lit_var_c q < n ->
    lit_var_c q <> lit_var_c p ->
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    binary_reason_same_level Mscan ->
    Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0 =
      Zlength (mt_lim (ms_core Mscan)) ->
    (forall v, 0 <= v < n ->
       is_tag (Znth v (ms_reason_words Mscan) 0) = true ->
       lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> lit_var_c q) ->
    binary_reason_same_level (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros n Mscan p q Htwf Hp_wf Hsize Hwordslen Hqrange Hqpneq Hfreshcell
    Hreasonbin Hprawlevel Hno_old_tag_target.
  pose proof (msat_enqueue_success_overlay_form_p3 Mscan p q Hfreshcell)
    as HMpost.
  pose proof (msat_reason_word_offcell_agree_p3 n Mscan p q Hwordslen Hqrange)
    as Hoffq_words.
  pose proof (msat_level_cell_offcell_agree_p3 n Mscan q Htwf Hqrange)
    as Hoffq_levels.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  rewrite HMpost. unfold binary_reason_same_level.
  unfold msolver_propagation_overlay, msolver_propagation_update.
  cbn.
  intros v Hv Htagpost.
  change (0 <= v < ms_size Mscan) in Hv.
  change (is_tag (Znth v
    (replace_Znth (lit_var_c q) (tag_of_lit p)
      (ms_reason_words Mscan)) 0) = true) in Htagpost.
  destruct (Z.eq_dec v (lit_var_c q)) as [-> | Hvq].
  - rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
      (lit_var_c q) (tag_of_lit p)) in Htagpost;
      [|rewrite Hwordslen; exact Hqrange].
    assert (Hwordq : nth (Z.to_nat (lit_var_c q))
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0 = tag_of_lit p).
    {
      change (Znth (lit_var_c q)
        (replace_Znth (lit_var_c q) (tag_of_lit p)
          (ms_reason_words Mscan)) 0 = tag_of_lit p).
      rewrite (Znth_replace_Znth_Same 0 (ms_reason_words Mscan)
        (lit_var_c q) (tag_of_lit p)); [reflexivity|].
      rewrite Hwordslen. exact Hqrange.
    }
    rewrite Hwordq.
    rewrite tag_lit_of.
    split.
    + rewrite <- Hsize. exact Hp_wf.
    + split.
      * assert (Hlevelp : nth (Z.to_nat (lit_var_c p))
          (replace_Znth (lit_var_c q)
            (Zlength (mt_lim (ms_core Mscan)))
            (mt_levels (ms_core Mscan))) 0 =
          Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0).
        {
          change (Znth (lit_var_c p)
            (replace_Znth (lit_var_c q)
              (Zlength (mt_lim (ms_core Mscan)))
              (mt_levels (ms_core Mscan))) 0 =
            Znth (lit_var_c p) (mt_levels (ms_core Mscan)) 0).
          rewrite (Hoffq_levels (lit_var_c p)
            (lit_var_c_in_range n p Hp_wf)
            (fun E => Hqpneq (eq_sym E))). reflexivity.
        }
        assert (Hlevelq : nth (Z.to_nat (lit_var_c q))
            (replace_Znth (lit_var_c q)
              (Zlength (mt_lim (ms_core Mscan)))
              (mt_levels (ms_core Mscan))) 0 =
            Zlength (mt_lim (ms_core Mscan))).
        {
          change (Znth (lit_var_c q)
            (replace_Znth (lit_var_c q)
              (Zlength (mt_lim (ms_core Mscan)))
              (mt_levels (ms_core Mscan))) 0 =
            Zlength (mt_lim (ms_core Mscan))).
          rewrite (Znth_replace_Znth_Same 0 (mt_levels (ms_core Mscan))
            (lit_var_c q) (Zlength (mt_lim (ms_core Mscan))));
            [reflexivity|].
          rewrite (mtw_levels_len Htwf). exact Hqrange.
        }
        rewrite Hlevelp, Hlevelq. exact Hprawlevel.
      * intro Heq. apply Hqpneq. symmetry. exact Heq.
  - assert (Hvold : 0 <= v < ms_size Mscan) by exact Hv.
    rewrite (Hoffq_words v ltac:(rewrite Hsize; exact Hv) Hvq)
      in Htagpost.
    assert (Hwordv : nth (Z.to_nat v)
      (replace_Znth (lit_var_c q) (tag_of_lit p)
        (ms_reason_words Mscan)) 0 =
      Znth v (ms_reason_words Mscan) 0).
    {
      change (Znth v
        (replace_Znth (lit_var_c q) (tag_of_lit p)
          (ms_reason_words Mscan)) 0 =
        Znth v (ms_reason_words Mscan) 0).
      exact (Hoffq_words v ltac:(rewrite Hsize; exact Hv) Hvq).
    }
    rewrite Hwordv.
    pose proof (Hreasonbin v Hvold Htagpost) as
      [Htargetwf [Hlevelsold Htargetne]].
    assert (Htargetq : lit_var_c
      (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> lit_var_c q).
    { apply Hno_old_tag_target; [rewrite Hsize; exact Hv|exact Htagpost]. }
    change (lit_wf_c (ms_size Mscan)
      (tag_lit (Znth v (ms_reason_words Mscan) 0)) /\
      Znth (lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)))
        (replace_Znth (lit_var_c q)
          (Zlength (mt_lim (ms_core Mscan)))
          (mt_levels (ms_core Mscan))) 0 =
      Znth v (replace_Znth (lit_var_c q)
          (Zlength (mt_lim (ms_core Mscan)))
          (mt_levels (ms_core Mscan))) 0 /\
      lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)) <> v).
    split; [exact Htargetwf|]. split.
    + rewrite (Hoffq_levels
        (lit_var_c (tag_lit (Znth v (ms_reason_words Mscan) 0)))
        (lit_var_c_in_range n _ ltac:(rewrite Hsize; exact Htargetwf))
        Htargetq).
      rewrite (Hoffq_levels v ltac:(rewrite Hsize; exact Hv) Hvq).
      exact Hlevelsold.
    + exact Htargetne.
Qed.

(* The whole [solver_propagation_weak] invariant transfers to the model after
   the unit enqueue, in both propagation contexts: every field is either
   untouched by the enqueue or supplied by one of the facts above. *)
Lemma msat_enqueue_fresh_weak_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (p q : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    mtrail_wf n (ms_core Mscan) ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    solver_shape (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    mtrail_wf n (mt_enqueue (ms_core Mscan) q) ->
    stable_view (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) ->
    reasons_entailed F (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) ->
    reasons_var_injective (view_of n (mt_enqueue (ms_core Mscan) q)
        (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
          (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))))
        (msolver_clauses Mscan)) ->
    trail_implied F (mt_enqueue (ms_core Mscan) q) ->
    reasons_match n (mt_enqueue (ms_core Mscan) q) (msolver_db Mscan)
      (replace_Znth (lit_var_c q) (tag_of_lit p) (ms_reason_words Mscan))
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q)
        (Some (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)))) ->
    reason_head_ok (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    binary_reason_same_level (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))) ->
    (forall root a,
       literal_wf n a ->
       assump_true_at_root (ms_core Mscan) root a ->
       assump_true_at_root (mt_enqueue (ms_core Mscan) q) root a) ->
    solver_propagation_weak n F A_arr K (msolver_propagation_enqueue_success Mscan q (tag_of_lit p)
      (cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil))).
Proof.
  intros n F A_arr K Mscan p q Hweak Htwf Hqwf Hfreshcell Hshape' Htrailwf'
    Hstable' Hreasonsent' Hreasonsinj' Htrailimpl' Hreasonsmem' Hreasonhead'
    Hreasonbin' Hassump_preserve.
  pose proof (msat_enqueue_success_overlay_form_p3 Mscan p q Hfreshcell)
    as HMpost.
  pose proof (msat_enqueue_success_fresh_form_p3 Mscan p q Hfreshcell)
    as HMfresh.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hviewpost : msolver_view n Mpost = Vpost).
  {
    rewrite HMpost. unfold Vpost, msolver_view, msolver_clauses, msolver_db.
    reflexivity.
  }
  assert (Hdbcomplete_preserve :
    cnf_wf n F -> db_complete F Mscan -> db_complete F Mpost).
  { intros _ _. rewrite HMfresh.
    destruct Hweak as [_ HK]. destruct K as [A_inst | A_proc]; cbn in HK.
    - eapply db_complete_enqueue_fresh__record;
        [exact HK|exact Hqwf|exact Hfreshcell].
    - eapply db_complete_enqueue_fresh_assuming__propagate_dbu;
        [exact HK|exact Hqwf|exact Hfreshcell]. }
  unfold solver_propagation_weak in *.
  split.
  - rewrite HMpost. exact (proj1 Hweak).
  - (* One script for both carriers: [destruct] puts the thirty (resp.
       twenty-nine) fields of whichever bundle [K] selects into scope under
       the record's own names, so each arm below is chosen by GOAL HEAD and
       closed by [assumption] rather than by a per-view projection. *)
    destruct K as [A_inst | A_proc]; cbn in *;
      pose proof (proj2 Hweak) as Hold; destruct Hold; constructor.
    all: lazymatch goal with
         | |- solver_shape _ => exact Hshape'
         | |- mtrail_wf _ _ => rewrite HMpost; exact Htrailwf'
         | |- trail_implied _ _ => rewrite HMpost; exact Htrailimpl'
         | |- stable_view _ => rewrite Hviewpost; exact Hstable'
         | |- reasons_entailed _ _ => rewrite Hviewpost; exact Hreasonsent'
         | |- reasons_var_injective _ => rewrite Hviewpost; exact Hreasonsinj'
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- reasons_match _ _ _ _ _ => rewrite HMpost; exact Hreasonsmem'
         | |- reason_head_ok _ => exact Hreasonhead'
         | |- binary_reason_same_level _ => exact Hreasonbin'
         | |- db_complete _ _ => apply Hdbcomplete_preserve; assumption
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- (exists _, _) =>
             lazymatch goal with
             | H : (exists _, _) |- _ => destruct H as [A_x [Hdec Hincl]]
             end;
             exists A_x; split; [|exact Hincl];
             rewrite HMpost; cbn;
             rewrite (decisions_upto_enqueue n (ms_core Mscan) q
               (Zlength (mt_lim (ms_core Mscan))) Htwf); exact Hdec
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- decisions_upto _ _ = _ =>
             rewrite HMpost; cbn;
             rewrite (decisions_upto_enqueue n (ms_core Mscan) q
               (ms_root_level Mscan) Htwf); assumption
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- Forall (assump_true_at_root _ _) _ =>
             rewrite HMpost; cbn; rewrite Forall_forall; intros a Ha;
             apply Hassump_preserve
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- literal_wf _ _ =>
             lazymatch goal with
             | Hwf : Forall (literal_wf _) ?A |- _ =>
                 rewrite Forall_forall in Hwf;
                 first [ apply Hwf; assumption
                       | lazymatch goal with
                         | Hin : incl _ A |- _ => apply Hwf, Hin; assumption
                         end ]
             end
         | _ => idtac
         end.
    all: (lazymatch goal with
         | |- assump_true_at_root _ _ _ =>
             lazymatch goal with
             | Hsat : Forall (assump_true_at_root _ _) _ |- _ =>
                 rewrite Forall_forall in Hsat; apply Hsat; assumption
             end
         | _ => idtac
         end);
      (lazymatch goal with
         | |- _ => first [ assumption | rewrite HMpost; assumption ]
         end).
Qed.

(* The scan semantics after a successful unit enqueue of the focused watcher
   word.  The state facts are re-established field by field from the facts of
   the pre-enqueue scan, and the carrier is the one the caller already moved. *)
Lemma msat_enqueue_fresh_scan_semantics_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z) (retained rest raw_suffix : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    tagged_word scan_current ->
    rest = scan_current :: raw_suffix ->
    lit_wf_c n (tag_lit scan_current) ->
    In scan_current (Znth p (ms_wm Mscan) nil) ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix ->
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    ms_qtail Mscan + 1 <= ms_cap Mscan ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_enqueue_success Mscan (tag_lit scan_current)
        (tag_of_lit p)
        (cons (lit_denote (tag_lit scan_current))
          (cons (literal_neg (lit_denote p)) nil)))
      p 0 (retained ++ scan_current :: nil) raw_suffix.
Proof.
  intros n F A_arr K Mscan p scan_current retained rest raw_suffix
    Hsem H_tagged_word H_rest Hqwf Hwmword Hcarrier_scan Hfreshcell Hcapbound.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconflict]; [|decompose [and] Hconflict; lia].
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hcovers &
     Hreasonless & Hplevel & Hp_wf & Hprocessed & Hfrontier & Hcarrier).
  destruct (msat_propagate_weak_core_fields_p3 n F A_arr K Mscan Hweak) as
    (Hdbwf & Htwf & Hshape & Hwmexact & Hstable & Hreasonsmem & Hreasonbin &
     Hsize).
  pose proof (msat_propagate_db_entailed_p3 n F A_arr K Mscan Hweak) as Hdbent.
  pose proof (msat_enqueue_fresh_reason_entailed_p3 n F Mscan p scan_current
    Hdbwf Hwmexact Hp_wf Hwmword H_tagged_word Hdbent) as Hreasonent.
  pose proof (msat_enqueue_success_overlay_form_p3 Mscan p
    (tag_lit scan_current) Hfreshcell) as HMpost.
  pose proof (msat_enqueue_success_fresh_form_p3 Mscan p
    (tag_lit scan_current) Hfreshcell) as HMfresh.
  set (q := tag_lit scan_current) in *.
  set (rc := cons (lit_denote q) (cons (literal_neg (lit_denote p)) nil)) in *.
  set (Mpost := msolver_propagation_enqueue_success Mscan q (tag_of_lit p) rc)
    in *.
  assert (Hqrange : 0 <= lit_var_c q < n)
    by (apply lit_var_c_in_range; exact Hqwf).
  assert (Hqpneq : lit_var_c q <> lit_var_c p).
  { eapply processed_fresh_target_different; eassumption. }
  pose proof (msat_enqueue_fresh_reason_lits_wf_p3 n Mscan p q Hqwf Hp_wf)
    as Hreasonwf.
  assert (Htrailwf' : mtrail_wf n (mt_enqueue (ms_core Mscan) q)).
  { apply mtrail_wf_enqueue; assumption. }
  assert (Hrcwords : rc = lits_denote (cons q (cons (lit_neg_c p) nil))).
  { unfold rc, lits_denote. cbn [map].
    rewrite (lit_denote_neg p) by (destruct Hp_wf; lia). reflexivity. }
  assert (Hwordswf : Forall (lit_wf_c n) (cons q (cons (lit_neg_c p) nil))).
  { constructor; [exact Hqwf|].
    constructor; [apply lit_neg_c_wf; exact Hp_wf|constructor]. }
  assert (Hassignone : assigns_one (msolver_view n Mscan)
    (view_of n (mt_enqueue (ms_core Mscan) q)
      (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
      (msolver_clauses Mscan))
    (lit_var_c q) (lit_pol q) (Zlength (mt_lim (ms_core Mscan)))
    (Some rc)).
  { rewrite Hrcwords.
    apply (propagation_unit_assigns_one_fresh__propagate_dbu
             n Mscan q (tag_of_lit p) (cons q (cons (lit_neg_c p) nil)));
      [exact Htwf|exact Hqwf|exact Hfreshcell|exact Hwordswf]. }
  pose proof (msat_enqueue_fresh_trail_implied_p3 n F A_arr K Mscan p q Hweak
    Htwf Hprocessed Hreasonent) as Htrailimpl'.
  pose proof Hassignone as Hassignone_packed.
  set (Vpost := view_of n (mt_enqueue (ms_core Mscan) q)
    (sat_function_update (ms_reason_of Mscan) (lit_var_c q) (Some rc))
    (msolver_clauses Mscan)) in Hassignone.
  destruct Hassignone as
    (Hqnone & Hqassigned & Hqlevel & Hqreason & Hqrank & Hothers & Hinst).
  destruct Hqrank as [rq [Hqrank Hdependencies]].
  pose proof (msat_enqueue_fresh_focus_false_p3 n Mscan p q Hp_wf Hprocessed
    Hqpneq Hassignone_packed) as Hp_post_false.
  pose proof (msat_enqueue_fresh_reason_valid_p3 n Mscan p q Hqpneq Hplevel
    Hp_post_false Hassignone_packed) as Hreasonvalidq.
  pose proof (msat_enqueue_fresh_stable_view_p3 n Mscan p q Hstable
    Hreasonvalidq Hassignone_packed) as Hstable'.
  assert (Hviewpost : msolver_view n Mpost = Vpost).
  {
    rewrite HMpost. unfold Vpost, msolver_view, msolver_clauses, msolver_db.
    reflexivity.
  }
  assert (Hshape' : solver_shape Mpost).
  { rewrite HMfresh.
    apply solver_shape_enqueue_fresh__record.
    - exact Hshape.
    - lia.
    - exact (proj1 Hweak). }
  pose proof (msat_enqueue_fresh_reasons_entailed_p3 n F A_arr K Mscan p q
    Hweak Hreasonent Hassignone_packed) as Hreasonsent'.
  pose proof (msat_enqueue_fresh_reasons_injective_p3 n F A_arr K Mscan p q
    Hweak Hqpneq Hassignone_packed) as Hreasonsinj'.
  pose proof (msat_enqueue_fresh_assump_at_root_p3 n Mscan p q Htwf Hqrange
    Hassignone_packed) as Hassump_preserve.
  assert (Hwordslen : Zlength (ms_reason_words Mscan) = n).
  {
    unfold solver_shape in Hshape.
    rewrite Hsize. intuition.
  }
  pose proof (msat_enqueue_fresh_reasons_match_p3 n Mscan p q Htwf Hp_wf
    Hqrange Hwordslen Hreasonsmem Hassignone_packed) as Hreasonsmem'.
  pose proof (msat_enqueue_fresh_reason_head_ok_p3 n F A_arr K Mscan p q Hweak
    Hfreshcell Hqrange Hwordslen Hsize) as Hreasonhead'.
  pose proof (msat_scan_focus_level_is_root_p3 n Mscan p Htwf Hprocessed
    Hplevel) as Hprawlevel.
  pose proof (msat_no_old_tag_targets_fresh_p3 n Mscan p q Htwf Hsize Hstable
    Hreasonsmem Hreasonbin Hassignone_packed) as Hno_old_tag_target.
  pose proof (msat_enqueue_fresh_reason_bin_p3 n Mscan p q Htwf Hp_wf Hsize
    Hwordslen Hqrange Hqpneq Hfreshcell Hreasonbin Hprawlevel
    Hno_old_tag_target) as Hreasonbin'.
  assert (Hreasonless' : current_reasonless_earliest n Mpost).
  { rewrite HMfresh.
    eapply current_reasonless_enqueue_fresh__propagate_dbu.
    - exact Hshape.
    - exact Htwf.
    - exact Hqwf.
    - pose proof (proj1 (tag_of_lit_reason_wf n p Hp_wf)). lia.
    - exact Hreasonless.
    - exact Hassignone_packed. }
  pose proof (msat_enqueue_fresh_weak_p3 n F A_arr K Mscan p q Hweak Htwf
    Hqwf Hfreshcell Hshape' Htrailwf' Hstable' Hreasonsent' Hreasonsinj'
    Htrailimpl' Hreasonsmem' Hreasonhead' Hreasonbin' Hassump_preserve)
    as Hweak'.
  assert (Hproplevel' : prop_level (ms_core Mpost)).
  { rewrite HMpost. apply prop_level_enqueue. exact Hproplevel. }
  assert (Hcovers' : heap_covers n (msolver_heap Mpost)
    (mt_assigns (ms_core Mpost)) (mt_trail (ms_core Mpost))
    (mt_qhead (ms_core Mpost))).
  { rewrite HMfresh.
    eapply heap_covers_enqueue_fresh__record;
      [exact Htwf|exact Hqwf|exact Hcovers]. }
  assert (Hheapready' : propagation_heap_ready n Mpost).
  { left. exact Hcovers'. }
  destruct (processed_enqueue_fresh_equiv__propagate_dbu
    n (ms_core Mscan) q Htwf Hqwf Hfreshcell) as [_ Hfwd].
  assert (Hprocessed_forward : forall w,
    lit_wf_c n w ->
    processed (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) w ->
    processed (mt_assigns (ms_core Mpost))
      (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)) w).
  { rewrite HMfresh. exact Hfwd. }
  assert (Hprocessed' : processed (mt_assigns (ms_core Mpost))
    (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)) p).
  { apply Hprocessed_forward; [exact Hp_wf|exact Hprocessed]. }
  assert (Hplevel' : level_of (msolver_view n Mpost) (lit_var_c p) =
    Some (Zlength (mt_lim (ms_core Mpost)))).
  {
    rewrite Hviewpost.
    destruct (Hothers (lit_var_c p)
      (fun E => Hqpneq (eq_sym E))) as [_ [Hlevelp _]].
    rewrite Hlevelp, Hplevel, HMpost. reflexivity.
  }
  assert (Hfrontier' : minisat_watch_frontier_except n (msolver_db Mpost)
    (mt_assigns (ms_core Mpost)) (mt_trail (ms_core Mpost))
    (mt_qhead (ms_core Mpost)) (lit_denote p)).
  { rewrite HMfresh.
    eapply minisat_watch_frontier_except_enqueue_fresh__propagate_dbu;
      [exact Htwf|exact Hqwf|exact Hfreshcell|exact Hfrontier]. }
  assert (Hcarrier' : minisat_focus_scan_carrier
    (msolver_db Mpost) p
    (minisat_processed n (mt_assigns (ms_core Mpost))
      (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)))
    (retained ++ scan_current :: nil) raw_suffix).
  { rewrite HMfresh.
    eapply minisat_focus_scan_carrier_enqueue_fresh__propagate_dbu;
      [exact Htwf|exact Hqwf|exact Hfreshcell|exact Hcarrier_scan]. }
  unfold solver_propagation_scan_semantics. left.
  split; [reflexivity|].
  split; [exact Hweak'|].
  split; [exact Hproplevel'|].
  split; [exact Hheapready'|].
  split; [exact Hcovers'|].
  split; [exact Hreasonless'|].
  split; [exact Hplevel'|].
  split; [exact Hp_wf|].
  split; [exact Hprocessed'|].
  split; [exact Hfrontier'|exact Hcarrier'].
Qed.

(* Writing a block of watcher words over a prefix of the watch list leaves the
   prefix alone and shortens the tail by exactly the number of words written. *)
Lemma msat_binary_watch_write_prefix_p3 :
  forall (xs prefix tail : list Z) (k : Z),
    Zlength prefix = k ->
    Zlength xs <= Zlength tail ->
    exists tail',
      binary_watch_write k xs (prefix ++ tail) = prefix ++ xs ++ tail' /\
      Zlength tail' = Zlength tail - Zlength xs.
Proof.
  intros xs prefix tail k Hprefix Hroom.
  destruct (binary_watch_write_prefix__propagate_dbu
    xs (prefix ++ tail) prefix k) as [tail' [Hwrite Hlength]].
  - rewrite <- Hprefix. apply Zlength_nonneg.
  - rewrite Zlength_app. lia.
  - exact Hprefix.
  - rewrite <- Hprefix. apply sublist_app_exact1.
  - exists tail'. split; [exact Hwrite|].
    rewrite Zlength_app in Hlength. lia.
Qed.

(* The weak propagation invariant survives installing the temporary binary
   conflict clause: the overlay only rewrites the binary slot. *)
Lemma msat_binary_conflict_route_weak_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z),
    solver_propagation_weak n F A_arr K Mscan ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p).
Proof.
  intros n F A_arr K Mscan p scan_current Hweak.
  unfold solver_propagation_weak in *.
  destruct K;
    destruct Hweak as [Hpending Hinv];
    (split; [exact Hpending|]);
    destruct Hinv;
    constructor;
    cbn [msolver_propagation_binary_conflict msolver_propagation_overlay msolver_propagation_update ] in *;
    try assumption;
    unfold solver_shape in *; cbn in *; tauto.
Qed.

(* The scan semantics of the temporary-binary conflict model: the scan is on
   its conflict arm, and the conflict certificate is the two-literal binary
   clause the solver just wrote. *)
Lemma msat_binary_conflict_route_semantics_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (p scan_current : Z) (retained rest raw_suffix : list Z)
         (scan_wm_pre scan_wm_post : list (list Z)),
    solver_propagation_weak n F A_arr K Mscan ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) ->
    solver_shape Mscan ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    prop_level (ms_core Mscan) ->
    heap_covers n (msolver_heap Mscan) (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) ->
    current_reasonless_earliest n Mscan ->
    minisat_watch_frontier_except n (msolver_db Mscan)
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) (lit_denote p) ->
    tagged_word scan_current ->
    rest = scan_current :: raw_suffix ->
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 <> 0 ->
    Znth (lit_var_c (tag_lit scan_current)) (mt_assigns (ms_core Mscan)) 0 <>
      lit_sig (tag_lit scan_current) ->
    ms_wm Mscan = scan_wm_pre ++ (retained ++ rest) :: scan_wm_post ->
    Zlength scan_wm_pre = p ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) p
      (ms_binary (msolver_propagation_binary_conflict Mscan
        (tag_lit scan_current) p))
      (retained ++ rest) nil.
Proof.
  intros n F A_arr K Mscan p scan_current retained rest raw_suffix
    scan_wm_pre scan_wm_post Hweak Hroute_weak Hshape Hp_wf Hprocessed
    Hlivelevel Hproplevel Hlivecovers Hliveearliest Hwatch_except
    Htagged Hrest Henq_assigned Henq_notsig H_ms_wm H_Zlength.
  set (Mroute := msolver_propagation_binary_conflict Mscan
    (tag_lit scan_current) p) in *.
  assert (Hdbwf : db_wf n (msolver_db Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_db_wf) (@msa_db_wf). }
  assert (Hwmexact : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact) (@msa_wmap_exact). }
  assert (Hdbimplied : db_implied F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_implied) (@msa_db_implied). }
  assert (Hdbmatches : db_matches_cnf F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_matches) (@msa_db_matches). }
  assert (Hbinaryout : ~ In (ms_binary Mscan) (map fst (msolver_db Mscan))).
  { msat_propagate_project_weak_field Hweak K (@msw_binary_out) (@msa_binary_out). }
  assert (Hheapwf : heap_wf n (msolver_heap Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_heap_wf) (@msa_heap_wf). }
  assert (Htrailwf : mtrail_wf n (ms_core Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_trail_wf) (@msa_trail_wf). }
  assert (Hcurrent_in : In scan_current (Znth p (ms_wm Mscan) nil)).
  {
    rewrite H_ms_wm, <- H_Zlength.
    unfold Znth.
    rewrite Zlength_correct, Nat2Z.id, app_nth2 by lia.
    replace (length scan_wm_pre - length scan_wm_pre)%nat with 0%nat by lia.
    simpl. apply in_or_app. right. rewrite Hrest. left. reflexivity.
  }
  destruct (wmap_tag_witness n (msolver_db Mscan) (ms_wm Mscan)
      p scan_current Hdbwf Hwmexact
      ltac:(destruct Hp_wf; lia) Hcurrent_in Htagged)
    as [binary_owner [binary_obj [Hbinary_obj [Hbinary_len Hbinary_perm]]]].
  assert (Hpacked_perm :
    Permutation (co_lits binary_obj)
      (tag_lit scan_current :: lit_neg_c p :: nil)).
  {
    eapply Permutation_trans; [exact Hbinary_perm|]. apply perm_swap.
  }
  pose proof (db_wf_obj n (msolver_db Mscan) binary_owner binary_obj
    Hdbwf Hbinary_obj) as Hobjwf.
  destruct Hobjwf as [Hobjlen [Hobjlits Hobjnodup]].
  assert (Hpacked_wf :
    Forall (lit_wf_c n) (tag_lit scan_current :: lit_neg_c p :: nil)).
  {
    rewrite Forall_forall in Hobjlits |- *.
    intros l Hl. apply Hobjlits.
    eapply Permutation_in; [apply Permutation_sym; exact Hpacked_perm|exact Hl].
  }
  assert (Hpacked_nodup :
    NoDup (map lit_var_c (tag_lit scan_current :: lit_neg_c p :: nil))).
  {
    apply (Permutation_NoDup (Permutation_map lit_var_c Hpacked_perm)).
    exact Hobjnodup.
  }
  assert (Hbinary_entails :
    entails_clause F
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil)).
  {
    eapply tagged_reason_entailed;
      [exact Hdbwf|exact Hwmexact|destruct Hp_wf; lia|
       exact Hcurrent_in|exact Htagged|].
    intros owner obj Hentry.
    unfold msolver_db in Hentry. apply in_app_or in Hentry.
    destruct Hentry as [Hprob | Hlearnt].
    - unfold db_matches_cnf in Hdbmatches.
      rewrite Forall_forall in Hdbmatches.
      destruct (Hdbmatches (denote_obj obj)
        (db_clauses_in (ms_prob Mscan) owner obj Hprob))
        as [original [Horiginal Hperm]].
      eapply entails_clause_perm; [apply Permutation_sym; exact Hperm|].
      apply entails_clause_in. exact Horiginal.
    - unfold db_implied in Hdbimplied.
      rewrite Forall_forall in Hdbimplied.
      apply Hdbimplied. apply (db_clauses_in (ms_learnt Mscan)
        owner obj Hlearnt).
  }
  assert (Hbinary_false :
    clause_false (assigns_pv (mt_assigns (ms_core Mscan)))
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil)).
  {
    unfold clause_false. intros l Hl.
    destruct Hl as [<- | [<- | []]].
    - apply lit_false_iff.
      + pose proof (Forall_inv Hpacked_wf) as Hcur_wf; destruct Hcur_wf; lia.
      + assert (Hv : 0 <= lit_var_c (tag_lit scan_current) < n).
        { apply lit_var_c_in_range. exact (Forall_inv Hpacked_wf). }
        pose proof (Forall_Znth_elim Z lbool_cell
          (mt_assigns (ms_core Mscan)) 0
          (lit_var_c (tag_lit scan_current)) (mtw_cells Htrailwf)) as Hcell.
        rewrite (mtw_assigns_len Htrailwf) in Hcell.
        specialize (Hcell Hv). unfold lbool_cell in Hcell.
        destruct Hcell as [Hcell | [Hcell | Hcell]];
          destruct (lit_sig_values (tag_lit scan_current)) as [Hsig | Hsig];
          rewrite Hsig in Henq_notsig; lia.
    - rewrite <- (lit_denote_neg p ltac:(destruct Hp_wf; lia)).
      apply lit_false_iff.
      + pose proof (Forall_inv (Forall_inv_tail Hpacked_wf)) as Hneg_wf;
        destruct Hneg_wf; lia.
      + destruct Hprocessed as [Hptrue _].
        unfold lit_true, lit_false in *.
        rewrite lit_var_c_neg, lit_sig_neg. lia.
  }
  assert (Hbinary_wf :
    Forall (literal_wf n)
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil)).
  {
    rewrite <- (lit_denote_neg p ltac:(destruct Hp_wf; lia)).
    change (Forall (literal_wf n)
      (lits_denote (tag_lit scan_current :: lit_neg_c p :: nil))).
    apply lits_denote_wf. exact Hpacked_wf.
  }
  assert (Hbinary_nodup :
    NoDup (map literal_var
      (lit_denote (tag_lit scan_current) ::
       literal_neg (lit_denote p) :: nil))).
  {
    rewrite <- (lit_denote_neg p ltac:(destruct Hp_wf; lia)).
    change (NoDup (map literal_var
      (lits_denote (tag_lit scan_current :: lit_neg_c p :: nil)))).
    apply lits_denote_nodup_vars. exact Hpacked_nodup.
  }
  unfold solver_propagation_scan_semantics. right.
  split.
  - subst Mroute. cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ].
    exact (solver_shape_binary_nonnull Mscan Hshape).
  - split.
    + reflexivity.
    + split.
      * unfold propagation_cancel_ready.
        refine (conj Hroute_weak
          (conj _ (conj _ (conj _ (conj _
            (conj _ (conj _ (conj _ _)))))))).
        all: subst Mroute;
          cbn [msolver_propagation_binary_conflict
            msolver_propagation_overlay msolver_propagation_update ]; assumption.
      * exists (lit_denote (tag_lit scan_current) ::
          literal_neg (lit_denote p) :: nil).
        split.
        -- unfold propagation_conflict_cert.
           repeat split; try assumption.
           exists (literal_neg (lit_denote p)).
           split; [right; left; reflexivity|].
           rewrite literal_var_neg, lit_var_c_denote. exact Hlivelevel.
        -- unfold conflict_ptr_denotes. left.
           subst Mroute. cbn [msolver_propagation_binary_conflict
             msolver_propagation_overlay msolver_propagation_update ].
           split; [reflexivity|]. split.
           ++ change (lit_denote (tag_lit scan_current) ::
                literal_neg (lit_denote p) :: nil =
                lit_denote (tag_lit scan_current) ::
                lit_denote (lit_neg_c p) :: nil).
              rewrite lit_denote_neg by (destruct Hp_wf; lia).
              reflexivity.
           ++ exact Hbinaryout.
Qed.

(* The binary-conflict exit package: the physical watcher layout after the
   copy, the exit record for the caller, and the pointer facts the frame needs.
   [tail'] is the untouched remainder of the watch list. *)
Lemma msat_binary_conflict_exit_package_p3 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M0 Mentry Mscan : msolver)
         (p scan_current s begin i j endvar copy_src copy_dst ii jj : Z)
         (source_words retained moved rest garbage raw_prefix raw_suffix
          watch_memory copy_memory : list Z),
    solver_shape Mscan ->
    msolver_seed_shadow Mscan ->
    propagation_caller_frame M0 Mscan ->
    propagation_scan_frontier Mentry Mscan p ->
    rest = scan_current :: raw_suffix ->
    propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ->
    binary_watch_copy_progress watch_memory raw_prefix scan_current
      raw_suffix ii jj copy_src copy_dst copy_memory ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) p
      (ms_binary (msolver_propagation_binary_conflict Mscan
        (tag_lit scan_current) p))
      (retained ++ rest) nil ->
    endvar = begin + Zlength source_words * sizeof ( PTR ) ->
    i = begin + copy_src * sizeof ( PTR ) ->
    j = begin + copy_dst * sizeof ( PTR ) ->
    i >= endvar ->
    0 <= copy_dst ->
    copy_dst <= copy_src ->
    copy_src <= Zlength source_words ->
    0 <= ms_binary Mscan ->
    (exists tail',
       propagation_binary_conflict_exit n F A_arr K M0 Mentry Mscan
         (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p)
         p scan_current (ms_binary Mscan) source_words retained moved rest
         copy_memory tail' (retained ++ rest)) /\
    i = begin + Zlength source_words * sizeof ( PTR ) /\
    j = begin + Zlength (retained ++ rest) * sizeof ( PTR ) /\
    0 < ms_binary Mscan /\
    ms_binary Mscan mod 2 = 0 /\
    solver_propagate_frame s
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) =
      solver_propagate_frame s Mscan.
Proof.
  intros n F A_arr K M0 Mentry Mscan p scan_current s begin i j endvar
    copy_src copy_dst ii jj source_words retained moved rest garbage
    raw_prefix raw_suffix watch_memory copy_memory
    Hshape Hseed Hframe Hfront Hrest Hphys H_binary_watch_copy_progress
    Hroute_sem H_endvar H_i PreH21 PreH18 PreH22 PreH23 PreH24 Hbinlo.
  pose proof msat_binary_watch_write_prefix_p3 as Hwrite_prefix.
  set (Mroute := msolver_propagation_binary_conflict Mscan
    (tag_lit scan_current) p) in *.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as
    (Hscaninv & Hwatchmemory & Hretlen & Hprefixlen & Hwatchlen).
  unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
  destruct H_binary_watch_copy_progress as
    (copied & uncopied & Hcopywords & Hrawprefixlen & Hjjrange &
     Hsuffixparts & Hsrcidx & Hdstidx & Hcopydef & Hcopylen).
  assert (Hsrcend : copy_src = Zlength source_words).
  {
    change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i.
    fold_arch.
    pose proof ptr_size_pos.
    nia.
  }
  assert (Hrawlen : Zlength raw_suffix = Zlength copied).
  {
    rewrite Hcopywords, Zlength_app, Zlength_cons in Hwatchlen.
    lia.
  }
  assert (Huncopiedlen : Zlength uncopied = 0).
  {
    rewrite Hsuffixparts, Zlength_app in Hrawlen. lia.
  }
  assert (Huncopied : uncopied = nil).
  {
    destruct uncopied as [|u uncopied]; [reflexivity|].
    rewrite Zlength_cons in Huncopiedlen.
    pose proof (Zlength_nonneg uncopied). lia.
  }
  subst uncopied. rewrite app_nil_r in Hsuffixparts. subst raw_suffix.
  assert (Hdstend : copy_dst = Zlength (retained ++ rest)).
  {
    rewrite Zlength_app, Hrest, Zlength_cons. lia.
  }
  assert (Hiend : i = begin + Zlength source_words * sizeof(PTR)).
  {
    (* Compute the stride for whatever arch is current
       instead of hardcoding a 32-bit width, so lia works without naming
       a width. *)
    solve_arch.
  }
  assert (Hjend : j = begin + Zlength (retained ++ rest) * sizeof(PTR)).
  {
    (* Compute the stride for whatever arch is current
       instead of hardcoding a 32-bit width, so lia works without naming
       a width. *)
    solve_arch.
  }
  assert (Hscanfinal :
    wlist_scan_inv source_words (retained ++ rest) moved nil).
  {
    unfold wlist_scan_inv in *.
    rewrite app_nil_r. rewrite <- app_assoc.
    eapply Permutation_trans; [|exact Hscaninv].
    apply Permutation_app_head. apply Permutation_app_comm.
  }
  assert (Hroom :
    Zlength (scan_current :: copied) <= Zlength (garbage ++ rest)).
  {
    rewrite Zlength_app, Hrest, Zlength_cons.
    pose proof (Zlength_nonneg garbage). lia.
  }
  destruct (Hwrite_prefix (scan_current :: copied) retained
    (garbage ++ rest) jj Hretlen Hroom) as
    (tail' & Hwritten & Htaillen).
  assert (Hcopyfromwrite :
    copy_memory = binary_watch_write jj (scan_current :: copied)
      watch_memory).
  {
    rewrite Hcopydef. cbn [binary_watch_write]. reflexivity.
  }
  assert (Hcopydecomp :
    copy_memory = (retained ++ rest) ++ tail').
  {
    rewrite Hcopyfromwrite, Hwatchmemory, Hwritten, Hrest.
    apply app_assoc.
  }
  assert (Hphysical_final :
    propagation_watch_scan_physical source_words (retained ++ rest)
      moved nil tail' copy_memory
      (Zlength source_words) (Zlength (retained ++ rest))).
  {
    unfold propagation_watch_scan_physical.
    refine (conj Hscanfinal (conj _ (conj eq_refl (conj _ _)))).
    - rewrite app_nil_r. exact Hcopydecomp.
    - rewrite <- Hcopydecomp. lia.
    - lia.
  }
  assert (Hroute_shape : solver_shape Mroute).
  {
    subst Mroute. unfold solver_shape in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    tauto.
  }
  assert (Hroute_seed : msolver_seed_shadow Mroute).
  {
    subst Mroute. unfold msolver_seed_shadow in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    exact Hseed.
  }
  assert (Hroute_frame : propagation_caller_frame M0 Mroute).
  {
    subst Mroute. unfold propagation_caller_frame in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    exact Hframe.
  }
  assert (Hroute_front : propagation_scan_frontier Mentry Mroute p).
  {
    subst Mroute. unfold propagation_scan_frontier in *.
    cbn [msolver_propagation_binary_conflict
      msolver_propagation_overlay msolver_propagation_update ] in *.
    exact Hfront.
  }
  assert (Hroute_transition :
    propagation_binary_conflict_transition n F A_arr K Mscan p
      scan_current (retained ++ rest) Mroute).
  {
    apply propagation_binary_conflict_transition_intro.
    - reflexivity.
    - exact Hroute_sem.
  }
  assert (Hconflict_step :
    propagation_scan_conflict_step source_words retained moved rest
      copy_memory tail' (retained ++ rest)).
  {
    unfold propagation_scan_conflict_step.
    split; [reflexivity|exact Hphysical_final].
  }
  assert (Hexit :
    propagation_binary_conflict_exit n F A_arr K M0 Mentry Mscan Mroute
      p scan_current (ms_binary Mscan) source_words retained moved rest
      copy_memory tail' (retained ++ rest)).
  {
    unfold propagation_binary_conflict_exit.
    refine (conj Hroute_shape (conj Hroute_seed
      (conj Hroute_frame (conj Hroute_front
        (conj Hroute_transition (conj Hconflict_step
          (conj _ (conj Hphysical_final _)))))))).
    - exact Hroute_sem.
    - subst Mroute. cbn [msolver_propagation_binary_conflict
        msolver_propagation_overlay msolver_propagation_update ]. reflexivity.
  }
  assert (Hbinary_pos : 0 < ms_binary Mscan).
  {
    pose proof (solver_shape_binary_nonnull Mscan Hshape).
    lia.
  }
  assert (Hbinary_even : ms_binary Mscan mod 2 = 0).
  {
    apply clause_ptr_mod2.
    unfold solver_shape in Hshape.
    tauto.
  }
  split; [exists tail'; exact Hexit|].
  split; [exact Hiend|].
  split; [exact Hjend|].
  split; [exact Hbinary_pos|].
  split; [exact Hbinary_even|].
  assert (Hfr_route :
    solver_propagate_frame s
      (msolver_propagation_binary_conflict Mscan (tag_lit scan_current) p) =
    solver_propagate_frame s Mscan).
  { unfold msolver_propagation_binary_conflict.
    apply solver_propagate_frame_overlay__propagate; reflexivity. }
  exact Hfr_route.
Qed.

(* ===== assume entail wits (3 proofs) ===== *)
Lemma proof_of_assume_entail_wit_1 : assume_entail_wit_1.
Proof.
  Unfold.
  right.
  intros.
  subst s_pre l_pre.
  bind_fact ( enqueue_input n l0 qtail assigns levels reasons trail ) as H_enqueue_input.
  assert (Htwon : 2 * n <= INT_MAX).
  { unfold enqueue_input in H_enqueue_input. tauto. }
  assert (Hrange : 0 <= lit_var_c l0 < n).
  { unfold enqueue_input in H_enqueue_input.
    apply lit_var_c_in_range. tauto. }
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_full asg (lit_var_c l0) n
       (Znth (lit_var_c l0) assigns 0) assigns).
  - dump_pre_spatial. exact Hrange.
  - rewrite replace_Znth_Znth.
    msat_manual_entailer_with int_auto.
Qed.

Lemma proof_of_assume_entail_wit_2 : assume_entail_wit_2.
Proof.
  aggressive_pre_process;
    bind_fact ( enqueue_input n l0 qtail assigns levels reasons trail ) as H_enqueue_input;
    unfold enqueue_input in H_enqueue_input;
    destruct H_enqueue_input as (_ & _ & _ & _ & _ & _ & Htail & _ & _);
    try lia;
    apply Zlength_nonneg.
Qed.

Lemma proof_of_assume_entail_wit_3 : assume_entail_wit_3.
Proof.
  Unfold.
  right.
  intros.
  subst s_pre.
  bind_fact ( Zlength assigns = n ) as H_Zlength.
  bind_fact ( Zlength trail = qtail ) as H_Zlength_2.
  unfold assume_post_at.
  Exists lim_cap_prime.
  entailer_with lia.
  unfold enqueue_post_at.
  Intros qtail' assigns' levels' reasons' trail'.
  rename H into Htrans.
  assert (Hret : retval_2 = 1).
  { unfold enqueue_transition in Htrans.
    destruct Htrans as
      [(Hassigned & _)|[(Hnonzero & _)|(Hzero & Hret & _)]];
      try congruence.
    exfalso.
    apply (lit_sig_nonzero l0).
    congruence. }
  subst retval_2.
  Exists qtail' assigns' levels' reasons' trail'.
  rewrite H_Zlength_2 in Htrans.
  rewrite H_Zlength, H_Zlength_2.
  msat_manual_entailer_with lia.
Qed.

(* ===== assume partial_solve wits (2 proofs) ===== *)
Lemma proof_of_assume_partial_solve_wit_3_pure : assume_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process;
    bind_fact ( l_pre = l0 ) as H_l_pre;
    bind_fact ( enqueue_input n l0 qtail assigns levels reasons trail ) as H_enqueue_input;
    unfold enqueue_input in H_enqueue_input;
    pose proof (lit_var_c_in_range n l0 ltac:(tauto)) as Hrange;
    destruct Hrange as [Hlo Hhi];
    rewrite H_l_pre;
    msat_manual_entailer_with lia.
Qed.

Lemma proof_of_assume_partial_solve_wit_4_pure : assume_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process;
    unfold veci_rep, veci_rep_at;
    Intros p;
    msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== enqueue partial_solve wits (3 proofs) ===== *)
Lemma proof_of_enqueue_partial_solve_wit_7_pure : enqueue_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  all: bind_fact ( Znth (lit_var_c l0) (replace_Znth (lit_var_c l0) (Znth (lit_var_c l0) assigns 0) assigns) 0 = 0 )
    as H_Znth;
    bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input;
    bind_fact ( retval = lit_var_c l_pre ) as H_retval;
    bind_fact ( l_pre = l0 ) as H_l_pre.
  assert (Hself :
    replace_Znth (lit_var_c l0) (Znth (lit_var_c l0) assigns 0) assigns =
    assigns) by apply replace_Znth_Znth.
  rewrite Hself in *.
  all: dump_pre_spatial.
  - rewrite H_retval, H_l_pre. exact H_Znth.
  - unfold enqueue_input in H_enqueue_input.
    destruct H_enqueue_input as (_ & _ & _ & _ & _ & _ & _ & Hroom & _).
    assert (Hself2 :
      replace_Znth (lit_var_c l0) (Znth (lit_var_c l0) assigns 0) assigns =
      assigns) by apply replace_Znth_Znth.
    rewrite Hself2 in H_Znth.
    specialize (Hroom H_Znth). lia.
  - rewrite H_l_pre. rewrite replace_Znth_Znth in H_Znth. exact H_Znth.
Qed.

Lemma proof_of_enqueue_partial_solve_wit_8_pure : enqueue_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  entailer_with ltac:(lia); apply replace_Znth_Znth.
Qed.

Lemma proof_of_enqueue_partial_solve_wit_9_pure : enqueue_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  entailer_with ltac:(lia); apply replace_Znth_Znth.
Qed.

(* ===== enqueue which_implies wits (3 proofs) ===== *)
Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  unfold enqueue_state_at.
  Intros rsn trl.
  Exists trl rsn.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_enqueue_which_implies_wit_2 : enqueue_which_implies_wit_2.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n).
  { apply lit_var_c_in_range. exact Hlit. }
  sep_apply_l_atomic
    (CharArray.seg_split_to_missing_i asg 0 (lit_var_c l0) n assigns 0).
  - dump_pre_spatial. exact Hrange.
  - replace (lit_var_c l0 - 0) with (lit_var_c l0) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_enqueue_which_implies_wit_3 : enqueue_which_implies_wit_3.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( Znth (lit_var_c l0) assigns 0 = 0 ) as H_Znth.
  bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as (Hlit & Htwice & Hassigns & Hlevels & Hreasons &
    Htrail & Hqtail & Hroom & Hvals).
  assert (Hrange : 0 <= lit_var_c l0 < n).
  { apply lit_var_c_in_range. exact Hlit. }
  assert (Htail : qtail < n).
  { apply Hroom. exact H_Znth. }
  sep_apply_l_atomic
    (IntArray.seg_split_to_missing_i lvl 0 (lit_var_c l0) n levels0 0).
  - dump_pre_spatial. exact Hrange.
  - sep_apply_l_atomic
      (PtrArray.seg_split_to_missing_i rsn 0 (lit_var_c l0) n reasons0 0).
    + dump_pre_spatial. exact Hrange.
    + replace (lit_var_c l0 - 0) with (lit_var_c l0) by lia.
      msat_manual_entailer_with ltac:(int_auto).
Qed.

(* ===== selectionsort entail wits (5 proofs) ===== *)
Lemma proof_of_selectionsort_entail_wit_1 : selectionsort_entail_wit_1.
Proof.
  aggressive_pre_process.
  unfold selectionsort_outer_inv in *.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_selectionsort_entail_wit_2 : selectionsort_entail_wit_2.
Proof.
  aggressive_pre_process.
  unfold selectionsort_outer_inv, selectionsort_inner_inv in *.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_selectionsort_entail_wit_3_1 : selectionsort_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  unfold selectionsort_inner_inv, learnt_cmp_result in *; msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_selectionsort_entail_wit_3_2 : selectionsort_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  unfold selectionsort_inner_inv, learnt_cmp_result in *; msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_selectionsort_entail_wit_4 : selectionsort_entail_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact ( selectionsort_inner_inv db activities origin current_2 size_pre i j best_i ) as H_selectionsort_inner_inv.
  unfold selectionsort_inner_inv in H_selectionsort_inner_inv.
  destruct H_selectionsort_inner_inv as
    (Hcontext & Hdomain & Hperm & Hlen & Hi & Hbest & Hj).
  replace (i - 0) with i by lia.
  replace (best_i - 0) with best_i by lia.
  set (swapped :=
    replace_Znth best_i (Znth i current_2 0)
      (replace_Znth i (Znth best_i current_2 0) current_2)).
  assert (Hswap : Permutation current_2 swapped).
  { subst swapped.
    apply selectionsort_swap_perm__solve; lia. }
  assert (Horigin : Permutation origin swapped).
  { eapply Permutation_trans; eauto. }
  assert (Hswapped_len : Zlength swapped = size_pre).
  { subst swapped. rewrite !Zlength_replace_Znth. exact Hlen. }
  Exists swapped.
  unfold selectionsort_outer_inv.
  unfold PtrArray.full, PtrArray.seg, store_array.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== selectionsort partial_solve wits (1 proofs) ===== *)
Lemma proof_of_selectionsort_partial_solve_wit_3_pure : selectionsort_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  all: bind_fact ( selectionsort_inner_inv db activities origin current size_pre i j best_i ) as
    H_selectionsort_inner_inv;
    unfold selectionsort_inner_inv in H_selectionsort_inner_inv;
    destruct H_selectionsort_inner_inv as (_ & Hdomain & Hperm & _);
    eapply sort_Znth_in_sep__solve;
    [exact Hdomain | exact Hperm | lia].
Qed.

(* ===== selectionsort return wits (1 proofs) ===== *)
Lemma proof_of_selectionsort_return_wit_1 : selectionsort_return_wit_1.
Proof.
  aggressive_pre_process.
  unfold selectionsort_outer_inv in *.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

(* ===== solver_analyze partial_solve wits (12 proofs) ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_118_learnt_pure : solver_analyze_partial_solve_wit_118_learnt_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R0 learnt0 x
    Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  prop_apply (DoubleArray.seg_Zlength activity_ptr_scan 0 anz_n
    (ms_activity Mscan)).
  Intros.
  split_pures.
  - dump_pre_spatial.
    unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
    destruct H_analyze_clause_scan_inv as [Hready _].
    unfold analysis_cancel_ready in Hready.
    destruct Hready as [Mready [_ [_ [Hheap _]]]].
    exact Hheap.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_119_learnt_pure : solver_analyze_partial_solve_wit_119_learnt_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia).
  subst Mact.
  subst j.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mscan Mscan anz_focus phase Ccur 0 ind S0 R0 learnt0 x
    Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  prop_apply (DoubleArray.seg_Zlength activity_ptr_scan 0 anz_n
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

Lemma proof_of_solver_analyze_partial_solve_wit_120_learnt_pure : solver_analyze_partial_solve_wit_120_learnt_pure.
Proof.
  Unfold; right; (LLM_pre_process ltac:(lia)); dump_pre_spatial.
  msat_analyze_close_clause_word_lower_bound Hall Hj0 Hj1 clause_words2 anz_n j Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_121_learnt_pure : solver_analyze_partial_solve_wit_121_learnt_pure.
Proof.
  Unfold.
  right.
  LLM_pre_process ltac:(lia).
  bind_fact ( j = 1 ) as H_j.
  split_pures;
    dump_pre_spatial;
    rewrite <- H_j;
    msat_analyze_close_clause_word_lower_bound Hall Hj0 Hj1 clause_words2 anz_n j Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_122_learnt_pure : solver_analyze_partial_solve_wit_122_learnt_pure.
Proof.
  Unfold; right; (LLM_pre_process ltac:(lia)); dump_pre_spatial.
  msat_analyze_close_clause_word_lower_bound Hall Hj0 Hj1 clause_words2 anz_n j Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_123_learnt_pure : solver_analyze_partial_solve_wit_123_learnt_pure.
Proof.
  Unfold.
  right.
  LLM_pre_process ltac:(lia).
  split_pures;
    dump_pre_spatial;
    replace (0 - 0) with (j - 0) by lia;
    msat_analyze_close_clause_word_lower_bound Hall Hj0 Hj1 clause_words2 anz_n j Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_132_learnt_pure : solver_analyze_partial_solve_wit_132_learnt_pure.
Proof.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_analyze_close_veci_bounds learnt_pre words_scan cap_scan.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_133_learnt_pure : solver_analyze_partial_solve_wit_133_learnt_pure.
Proof.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_analyze_close_veci_bounds learnt_pre words_scan cap_scan.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_134_learnt_pure : solver_analyze_partial_solve_wit_134_learnt_pure.
Proof.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_analyze_close_veci_bounds learnt_pre words_scan cap_scan.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_135_learnt_pure : solver_analyze_partial_solve_wit_135_learnt_pure.
Proof.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_analyze_close_veci_bounds learnt_pre words_scan cap_scan.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_144_pure : solver_analyze_partial_solve_wit_144_pure.
Proof.
  right. LLM_pre_process ltac:(lia). dump_pre_spatial.
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

Lemma proof_of_solver_analyze_partial_solve_wit_146_pure : solver_analyze_partial_solve_wit_146_pure.
Proof.
  right. LLM_pre_process ltac:(lia).
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

(* ===== solver_lit_removable entail wits (4 proofs) ===== *)
Lemma proof_of_solver_lit_removable_entail_wit_13_2 : solver_lit_removable_entail_wit_13_2.
Proof.
  aggressive_pre_process.
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
  bind_fact ( Zlength stack_now_2 <= stack_cap_now_2 ) as H_Zlength.
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
    assert (Hstack_after_cap : Zlength stack_after <= stack_cap_now_2) by
      (rewrite H_stack_now_2, Zlength_app, Zlength_cons, Zlength_nil in H_Zlength;
       lia).
    rewrite H_retval_4, <- H_stack_after.
    Exists tagged_cap_now_2 (v :: done_2) stack_after tags_now_2 tagged_now_2.
    try change (sizeof (PTR)) with ptr_size_Z.
    fold_arch.
    sep_apply (PtrArray.missing_i_merge_to_full reasons_ptr
      (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n
      (Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0)))
         (ms_reason_words M0) 0) (ms_reason_words M0)).
    sep_apply (IntArray.missing_i_merge_to_full levels_ptr
      (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n
      (Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0)))
         (mt_levels (ms_core M0)) 0) (mt_levels (ms_core M0))).
    sep_apply (CharArray.missing_i_merge_to_full tags_ptr
      (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n
      (Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0)))
         tags_now_2 0) tags_now_2).
    rewrite ?replace_Znth_Znth.
    sep_apply PtrArray.full_to_seg.
    sep_apply IntArray.full_to_seg.
    sep_apply CharArray.full_to_seg.
    all: msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_13_3 : solver_lit_removable_entail_wit_13_3.
Proof.
  aggressive_pre_process.
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
  bind_fact ( Zlength stack_now_2 <= stack_cap_now_2 ) as H_Zlength.
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
    assert (Hstack_after_cap : Zlength stack_after <= stack_cap_now_2) by
      (rewrite H_stack_now_2, Zlength_app, Zlength_cons, Zlength_nil in H_Zlength;
       lia).
    rewrite H_retval_4, <- H_stack_after.
    Exists tagged_cap_now_2 (v :: done_2) stack_after tags_now_2 tagged_now_2.
    try change (sizeof (PTR)) with ptr_size_Z.
    fold_arch.
    sep_apply (PtrArray.missing_i_merge_to_full reasons_ptr
      (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n
      (Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0)))
         (ms_reason_words M0) 0) (ms_reason_words M0)).
    sep_apply (IntArray.missing_i_merge_to_full levels_ptr
      (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n
      (Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0)))
         (mt_levels (ms_core M0)) 0) (mt_levels (ms_core M0))).
    sep_apply (CharArray.missing_i_merge_to_full tags_ptr
      (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0))) lrm_n
      (Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M0) 0)))
         tags_now_2 0) tags_now_2).
    rewrite ?replace_Znth_Znth.
    sep_apply PtrArray.full_to_seg.
    sep_apply IntArray.full_to_seg.
    sep_apply CharArray.full_to_seg.
    all: msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_13_4 : solver_lit_removable_entail_wit_13_4.
Proof.
  aggressive_pre_process.
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
  Exists stack_cap_scan tagged_cap_scan (v :: done_scan)
    stack_scan tagged_scan. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_14 : solver_lit_removable_entail_wit_14.
Proof.
  aggressive_pre_process.
  bind_fact ( stack_cap_now <= 2147483647 ) as H_stack_cap_now.
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
  prop_apply
    (CharArray.seg_Zlength tags_ptr 0 lrm_n tags_now);
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
    M0 tags_now tagged_now tagged_cap_now stack_now stack_cap_now
    Hshape ltac:(lia)) as Hshapeout.
  sep_apply
    (solver_nested_veci_from_cells__canceluntil_cap
      s_pre "stack" p stack_now stack_cap_now ltac:(lia) ltac:(lia)).
  sep_apply
    (solver_removable_scratch_refold_general__lit_removable
      s_pre M0 lrm_n reasons_ptr levels_ptr trail_ptr tags_ptr
      tags_now tagged_now tagged_cap_now stack_now stack_cap_now
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
  match goal with
  | Hready : analysis_cancel_ready ?lrm_n ?lrm_F ?lrm_A_arr ?lrm_K ?M0 ?lrm_focus |- _ =>
      assert (Hreadyout : analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K
        (msolver_scratch_update M0 tags_now tagged_now
           tagged_cap_now stack_now stack_cap_now) lrm_focus)
        by (change (analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus);
            exact Hready)
  end.
  match goal with
  | Hseed : msolver_seed_shadow ?M0 |- _ =>
      assert (Hseedout : msolver_seed_shadow
        (msolver_scratch_update M0 tags_now tagged_now
           tagged_cap_now stack_now stack_cap_now))
        by (change (msolver_seed_shadow M0); exact Hseed)
  end.
  assert (Hequivout : analysis_core_equiv M0
    (msolver_scratch_update M0 tags_now tagged_now
       tagged_cap_now stack_now stack_cap_now)) by
    (unfold analysis_core_equiv; repeat split; reflexivity).
  pose proof
    (removable_success_post_pure__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus tags_now tagged_now tagged_cap_now
      stack_now stack_cap_now l_pre fresh Hreadyout Hseedout Hequivout
      ltac:(lia) ltac:(lia) Hstack_nil Htagged_fresh Htags_exact_out
      Hremovable Hassigned_out) as Hpostpure.
  unfold solver_lit_removable_post.
  Exists (msolver_scratch_update M0 tags_now tagged_now
    tagged_cap_now stack_now stack_cap_now).
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_lit_removable partial_solve wits ===== *)


Lemma proof_of_solver_lit_removable_partial_solve_wit_3_pure : solver_lit_removable_partial_solve_wit_3_pure.
Proof.
  msat_lit_var_parity_bounds_p3 l_pre.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_4_pure : solver_lit_removable_partial_solve_wit_4_pure.
Proof.
  msat_lit_var_parity_bounds_p3 l_pre.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_7_pure : solver_lit_removable_partial_solve_wit_7_pure.
Proof.
  msat_lit_var_parity_bounds_p3 l_pre.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_10_pure : solver_lit_removable_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process;
    unfold veci_rep at 1; Intros stack_data_ptr;
    unfold veci_rep_at at 1; Intros;
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_11_pure : solver_lit_removable_partial_solve_wit_11_pure.
Proof.
  msat_lit_var_parity_bounds_p3 l_pre.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_72_pure : solver_lit_removable_partial_solve_wit_72_pure.
Proof.
  aggressive_pre_process.
  all: (match goal with
  | Hinv : removable_rollback_inv _ ?top0 ?j0 ?base0 _ _ ?tagged0 _ |- _ =>
      pose proof (Zlength_nonneg base0);
      unfold removable_rollback_inv in Hinv;
      assert (Htop_nonneg : 0 <= top0) by tauto;
      assert (Htopj : top0 <= j0) by tauto;
      assert (Hjlen : j0 <= Zlength tagged0) by tauto;
      assert (Htopbase : top0 = Zlength base0) by tauto
  end);
    (dump_pre_spatial);
    (lia).
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_73_pure : solver_lit_removable_partial_solve_wit_73_pure.
Proof.
  pre_process_default.
  msat_lit_removable_lits_pointer_even_p3 lrm_n M0 c is_learnt_now clause_words.
Qed.

Lemma proof_of_solver_lit_removable_partial_solve_wit_74_pure : solver_lit_removable_partial_solve_wit_74_pure.
Proof.
  pre_process_default.
  msat_lit_removable_lits_pointer_even_p3 lrm_n M0 c is_learnt_now clause_words.
Qed.

(* ===== solver_lit_removable return wits (2 proofs) ===== *)
Lemma proof_of_solver_lit_removable_return_wit_2 : solver_lit_removable_return_wit_2.
Proof.
  aggressive_pre_process.
  bind_fact ( 0 <= Zlength tagged_scan ) as H_Zlength.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  sep_apply
    (solver_removable_frame_lengths_keep__lit_removable
      s_pre M0 trail_ptr lrm_wl);
    Intros_p Hframe_lengths;
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
  prop_apply
    (CharArray.seg_Zlength tags_ptr 0 lrm_n tags_rollback);
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
  sep_apply (tagged_open_refold__lit_removable
    s_pre tagged
    (ms_tagged M0) tagged_cap_scan ltac:(lia) ltac:(lia)).
  prop_apply_p (veci_rep_bounds__canceluntil_cap
    &(s_pre # "solver_t" ->ₛ "stack") stack_scan stack_cap_scan);
    Intros_p Hstack_bounds;
    destruct Hstack_bounds as (Hstack_len & Hstack_cap).
  sep_apply (solver_removable_scratch_refold_residual__lit_removable
    s_pre M0 reasons_ptr levels_ptr trail_ptr tags_ptr tagged
    tagged_cap_scan stack_scan stack_cap_scan lrm_wl Hshape).
  match goal with
  | Hready : analysis_cancel_ready ?lrm_n ?lrm_F ?lrm_A_arr ?lrm_K ?M0 ?lrm_focus |- _ =>
      assert (Hreadyout : analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K
        (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
           tagged_cap_scan stack_scan stack_cap_scan) lrm_focus)
        by (change (analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus);
            exact Hready)
  end.
  match goal with
  | Hseed : msolver_seed_shadow ?M0 |- _ =>
      assert (Hseedout : msolver_seed_shadow
        (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
           tagged_cap_scan stack_scan stack_cap_scan))
        by (change (msolver_seed_shadow M0); exact Hseed)
  end.
  assert (Hequivout : analysis_core_equiv M0
    (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
       tagged_cap_scan stack_scan stack_cap_scan)) by
    (unfold analysis_core_equiv; repeat split; reflexivity).
  pose proof
    (removable_failure_post_pure__lit_removable
      (ms_size M0) lrm_F lrm_A_arr lrm_K M0 lrm_focus (ms_tags M0) (ms_tagged M0)
      tagged_cap_scan stack_scan stack_cap_scan Hreadyout Hseedout Hequivout
      eq_refl eq_refl ltac:(lia) ltac:(lia)) as Hpostpure.
  unfold solver_lit_removable_post.
  Exists (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
    tagged_cap_scan stack_scan stack_cap_scan).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_return_wit_3 : solver_lit_removable_return_wit_3.
Proof.
  aggressive_pre_process.
  bind_fact ( 0 <= Zlength tagged_now ) as H_Zlength.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  sep_apply
    (solver_removable_frame_lengths_keep__lit_removable
      s_pre M0 trail_ptr lrm_wl);
    Intros_p Hframe_lengths;
    destruct Hframe_lengths as
      (Hactivity_len & Horder_len & Hstats_len).
  prop_apply
    (CharArray.seg_Zlength tags_ptr 0 lrm_n tags_rollback);
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
  sep_apply (tagged_open_refold__lit_removable
    s_pre tagged
    (ms_tagged M0) tagged_cap_now ltac:(lia) ltac:(lia)).
  sep_apply (veci_rep_bounds_keep__lit_removable
    &(s_pre # "solver_t" ->ₛ "stack") stack_after stack_cap_now);
    Intros_p Hstack_bounds;
    destruct Hstack_bounds as (Hstack_len & Hstack_cap).
  sep_apply (solver_removable_scratch_refold_return3__lit_removable
    s_pre M0 reasons_ptr levels_ptr trail_ptr tags_ptr tagged
    tagged_cap_now stack_after stack_cap_now lrm_wl Hshape).
  match goal with
  | Hready : analysis_cancel_ready ?lrm_n ?lrm_F ?lrm_A_arr ?lrm_K ?M0 ?lrm_focus |- _ =>
      assert (Hreadyout : analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K
        (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
           tagged_cap_now stack_after stack_cap_now) lrm_focus)
        by (change (analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus);
            exact Hready)
  end.
  match goal with
  | Hseed : msolver_seed_shadow ?M0 |- _ =>
      assert (Hseedout : msolver_seed_shadow
        (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
           tagged_cap_now stack_after stack_cap_now))
        by (change (msolver_seed_shadow M0); exact Hseed)
  end.
  assert (Hequivout : analysis_core_equiv M0
    (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
       tagged_cap_now stack_after stack_cap_now)) by
    (unfold analysis_core_equiv; repeat split; reflexivity).
  pose proof
    (removable_failure_post_pure__lit_removable
      (ms_size M0) lrm_F lrm_A_arr lrm_K M0 lrm_focus (ms_tags M0) (ms_tagged M0)
      tagged_cap_now stack_after stack_cap_now Hreadyout Hseedout Hequivout
      eq_refl eq_refl ltac:(lia) ltac:(lia)) as Hpostpure.
  unfold solver_lit_removable_post.
  Exists (msolver_scratch_update M0 (ms_tags M0) (ms_tagged M0)
    tagged_cap_now stack_after stack_cap_now).
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_lit_removable which_implies witnesses ===== *)
Lemma proof_of_solver_lit_removable_which_implies_wit_1 : solver_lit_removable_which_implies_wit_1.
Proof.
  unfold solver_lit_removable_which_implies_wit_1.
  right.
  intros lrm_focus M0 lrm_K lrm_A_arr lrm_F lrm_n lrm_wl
    tags_ptr trail_ptr l minl s Hshape Hready Hseed
    Hvlo Hvhi Hminlo Hminhi Hassigned Hreason Htags
    Htagcaplo Htagcaphi Hstackcaplo Hstackcaphi Htwon.
  destruct (analysis_cancel_ready_reason_target__lit_removable
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus (lit_var_c l)
    Hready ltac:(lia) Hreason) as [Croot Htarget].
  destruct (analysis_cancel_ready_reason_core
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus Hready) as [Hsize _].
  Exists Croot.
  unfold solver_reason_levels_frame_at.
  subst lrm_n.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_2 : solver_lit_removable_which_implies_wit_2.
Proof.
  aggressive_pre_process;
    try solve [entailer_with ltac:(lia)].
  unfold removable_reason_array_hole.
  try entailer_with ltac:(lia).
  replace (lit_var_c l - 0) with (lit_var_c l) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_3 : solver_lit_removable_which_implies_wit_3.
Proof.
  aggressive_pre_process.
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

Lemma proof_of_solver_lit_removable_which_implies_wit_4 : solver_lit_removable_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact ( 0 < Zlength stack_now ) as H_Zlength.
  bind_fact ( v = Znth (Zlength stack_now - 1) stack_now 0 ) as H_v.
  pose proof
    (list_last_sublist__lit_removable
      stack_now v H_Zlength H_v) as Hlast.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_5 : solver_lit_removable_which_implies_wit_5.
Proof.
  aggressive_pre_process;
    try solve [entailer_with ltac:(lia)].
  unfold removable_reason_array_hole.
  try entailer_with ltac:(lia).
  replace (v - 0) with v by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_6 : solver_lit_removable_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  unfold removable_reason_array_hole, StorePtrAsElement.storeA.
  change (sizeof (PTR)) with ptr_size_Z. fold_arch.
  prop_apply_p
    (ptrarray_missing_i_index_range__lit_removable
      reasons_ptr v 0 lrm_n (ms_reason_words M0)).
  Intros_p Hrange. destruct Hrange as [Hv0 Hvn].
  (* The goal carries the unfolded Arch32.ptr_size_Z while
     PtrArray's lemmas are stated over the derived ptr_size_Z; move any
     sizeof(PTR) to the Arch alias then fold it back to the derived name. *)
  try change (sizeof (PTR)) with ptr_size_Z. fold_arch.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_seg reasons_ptr 0 v lrm_n
      (Znth v (ms_reason_words M0) 0) (ms_reason_words M0)).
  - dump_pre_spatial. lia.
  - replace (v - 0) with v by lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_7 : solver_lit_removable_which_implies_wit_7.
Proof.
  aggressive_pre_process;
    bind_fact ( removable_reason_focus lrm_n M0 v c Cnext ) as H_removable_reason_focus;
    bind_fact ( is_tag c = msat_true ) as H_is_tag;
    pose proof
    (removable_reason_focus_tag_range__lit_removable
      lrm_n M0 v c Cnext H_removable_reason_focus H_is_tag) as Hrange;
    destruct Hrange as [Hlo Hhi];
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_8 : solver_lit_removable_which_implies_wit_8.
Proof.
  aggressive_pre_process;
    try solve [entailer_with lia].
  unfold removable_reason_array_hole.
  try entailer_with lia.
  replace (v - 0) with v by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_9 : solver_lit_removable_which_implies_wit_9.
Proof.
  Unfold; right; intros.
  replace (v - 0) with v by lia; msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_10 : solver_lit_removable_which_implies_wit_10.
Proof.
  Unfold; right; intros.
  replace (v - 0) with v by lia; msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_11 : solver_lit_removable_which_implies_wit_11.
Proof.
  aggressive_pre_process.
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

(* ===== solver_propagate entail wits (12 proofs) ===== *)
Lemma proof_of_solver_propagate_entail_wit_22_10_real_satisfied : solver_propagate_entail_wit_22_10_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_10_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_11_real_satisfied : solver_propagate_entail_wit_22_11_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_11_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_12_real_satisfied : solver_propagate_entail_wit_22_12_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_12_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_13_real_satisfied : solver_propagate_entail_wit_22_13_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_13_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_14_real_satisfied : solver_propagate_entail_wit_22_14_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_14_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_15_real_satisfied : solver_propagate_entail_wit_22_15_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_15_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_16_real_satisfied : solver_propagate_entail_wit_22_16_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_16_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_17_real_satisfied : solver_propagate_entail_wit_22_17_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_17_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_18_real_satisfied : solver_propagate_entail_wit_22_18_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_18_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_19_real_satisfied : solver_propagate_entail_wit_22_19_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_19_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_20_real_satisfied : solver_propagate_entail_wit_22_20_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_20_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_21_real_satisfied : solver_propagate_entail_wit_22_21_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_21_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

(* ===== solver_propagate partial_solve wits (24 proofs) ===== *)
Lemma proof_of_solver_propagate_partial_solve_wit_33_scan_same_pure :
  solver_propagate_partial_solve_wit_33_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_33_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right; intros.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( jj = ii ) as H_jj.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength.
  (* The only conjunct left on the second disjunct is the read-back of the cell just
          written at jj; because jj = ii on this `same` site it collapses to scan_current,
          which is why the shared scan closer does not apply here. *)
  assert (Hcur : Znth ii tagged_memory 0 = scan_current).
  { rewrite H_tagged_memory, H_jj.
    apply Znth_replace_Znth_Same.
    rewrite H_Zlength. lia. }
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_34_scan_move_pure :
  solver_propagate_partial_solve_wit_34_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_34_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  left; intros.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  (* This scan site leaves a single residual conjunct, the tagged-memory read-back at ii,
          which lies outside the cell written at jj -- so the shared closer's `first [...]`
          chain has no branch for it and the conjunct is discharged in place. *)
  entailer_with ltac:(lia).
  rewrite H_tagged_memory.
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite H_watch_memory.
  rewrite app_Znth2 by lia.
  rewrite H_Zlength.
  replace (ii - ii) with 0 by lia.
  unfold Znth; simpl; reflexivity.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_35_scan_same_pure :
  solver_propagate_partial_solve_wit_35_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_35_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  left; intros.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( jj = ii ) as H_jj.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength.
  (* The residual goal here is the physical read-back of the freshly written watch slot,
          which the shared closer's `first [...]` does not cover.  With jj = ii the read-back
          is exactly the cell just written, so it collapses to scan_current. *)
  entailer_with ltac:(lia).
  rewrite H_tagged_memory, H_jj.
  apply Znth_replace_Znth_Same.
  rewrite H_Zlength. lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_39_scan_same_pure :
  solver_propagate_partial_solve_wit_39_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_39_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  (* Because jj = ii on this `same` site, the read-back conjunct collapses to
          [scan_current], so the single `enqueue_input` argument built below serves both
          `enqueue_input` goals.  The scan-move group closer is not usable here: its
          `first [...]` has no branch for the conjuncts this obligation emits. *)
  pre_process_default.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength_2.
  assert (Hcur : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current).
  { apply Znth_replace_Znth_Same. rewrite H_Zlength_2. lia. }
  assert (Hrest : rest = scan_current :: raw_suffix)
    by (eapply propagation_watch_scan_rest_head__propagate;
        [ eassumption
        | eassumption
        | eassumption ]).
  assert (Henq : enqueue_input (ms_size Mscan) (tag_lit scan_current) (ms_qtail Mscan)
      (mt_assigns (ms_core Mscan)) (mt_levels (ms_core Mscan))
      (ms_reason_words Mscan) (mt_trail (ms_core Mscan)))
    by (eapply propagation_scan_current_enqueue_input__propagate; eassumption).
  split_pures;
    entailer_with ltac:(lia);
    try exact Henq;
    try (rewrite Hcur; exact Henq);
    try (unfold solver_shape in H_solver_shape; tauto);
    try (symmetry; apply Znth_replace_Znth_Same; rewrite Zlength_replace_Znth; lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_108_scan_same_pure :
  solver_propagate_partial_solve_wit_108_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_108_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold. left. intros.
  bind_fact (solver_propagation_scan_semantics n F A_arr K Mscan p
    confl retained rest) as Hscan.
  bind_fact (propagation_watch_scan_physical source_words retained moved
    rest garbage watch_memory ii jj) as Hphysical.
  bind_fact (Zlength scan_wm_pre = p) as Hindex.
  assert (Hconfl : confl = 0).
  { pose proof Hscan as Hcases.
    destruct Hcases as [[Hzero _] | [_ [Hrest _]]]; [exact Hzero |].
    pose proof Hphysical as Hlayout.
    destruct Hlayout as [_ [Hmemory [_ [Hprefix Hlength]]]].
    subst rest. rewrite app_nil_r in Hmemory.
    rewrite Hmemory, Hprefix in Hlength. lia. }
  subst confl. rewrite Hindex.
  entailer_with ltac:(congruence).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_109_scan_move_pure :
  solver_propagate_partial_solve_wit_109_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_109_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold. left. intros.
  bind_fact (solver_propagation_scan_semantics n F A_arr K Mscan p
    confl retained rest) as Hscan.
  bind_fact (propagation_watch_scan_physical source_words retained moved
    rest garbage watch_memory ii jj) as Hphysical.
  bind_fact (Zlength scan_wm_pre = p) as Hindex.
  assert (Hconfl : confl = 0).
  { pose proof Hscan as Hcases.
    destruct Hcases as [[Hzero _] | [_ [Hrest _]]]; [exact Hzero |].
    pose proof Hphysical as Hlayout.
    destruct Hlayout as [_ [Hmemory [_ [Hprefix Hlength]]]].
    subst rest. rewrite app_nil_r in Hmemory.
    rewrite Hmemory, Hprefix in Hlength. lia. }
  subst confl. rewrite Hindex.
  entailer_with ltac:(congruence).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_118_scan_same_pure :
  solver_propagate_partial_solve_wit_118_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_118_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_close_scan_step_leaves Hlt Hphysical Hresult Hzero.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_119_scan_move_pure :
  solver_propagate_partial_solve_wit_119_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_119_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_close_scan_step_leaves Hlt Hphysical Hresult Hzero.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_120_scan_same_pure :
  solver_propagate_partial_solve_wit_120_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_120_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_close_scan_step_leaves Hlt Hphysical Hresult Hzero.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_121_scan_move_pure :
  solver_propagate_partial_solve_wit_121_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_121_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_close_scan_step_leaves Hlt Hphysical Hresult Hzero.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_126_scan_move_pure :
  solver_propagate_partial_solve_wit_126_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_126_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_scan_lit_range_p3 n F A_arr K Mscan p retained rest.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_127_scan_move_pure :
  solver_propagate_partial_solve_wit_127_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_127_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_scan_lit_range_p3 n F A_arr K Mscan p retained rest.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_308_scan_move_pure :
  solver_propagate_partial_solve_wit_308_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_308_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_309_scan_move_pure :
  solver_propagate_partial_solve_wit_309_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_309_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_310_scan_same_pure :
  solver_propagate_partial_solve_wit_310_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_310_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_311_scan_same_pure :
  solver_propagate_partial_solve_wit_311_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_311_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_312_scan_same_pure :
  solver_propagate_partial_solve_wit_312_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_312_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_313_scan_same_pure :
  solver_propagate_partial_solve_wit_313_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_313_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_314_scan_move_pure :
  solver_propagate_partial_solve_wit_314_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_314_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_315_scan_move_pure :
  solver_propagate_partial_solve_wit_315_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_315_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_316_scan_move_pure :
  solver_propagate_partial_solve_wit_316_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_316_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_317_scan_move_pure :
  solver_propagate_partial_solve_wit_317_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_317_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_318_scan_same_pure :
  solver_propagate_partial_solve_wit_318_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_318_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_319_scan_same_pure :
  solver_propagate_partial_solve_wit_319_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_319_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

(* ===== solver_propagate which_implies wits (11 proofs) ===== *)
Lemma proof_of_solver_propagate_which_implies_wit_15 : solver_propagate_which_implies_wit_15.
Proof.
  aggressive_pre_process.
  msat_propagate_ptr_missing_merge_p3 begin ii source_words tagged_memory i;
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_16 : solver_propagate_which_implies_wit_16.
Proof.
  Unfold.
  left.
  intros Mscan confl0 PreH1 PreH2.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  assert (Hlen : Zlength (ms_binary_lits Mscan) = 2).
  { unfold solver_shape in H_solver_shape. tauto. }
  subst confl0.
  Exists (ms_binary Mscan).
  unfold solver_binary_rep, MiniSatClause.rep, activity_state,
    clause_hdr_word, clause_hdr_addr, clause_act_addr.
  rewrite Hlen.
  simpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_17 : solver_propagate_which_implies_wit_17.
Proof.
  aggressive_pre_process.
  subst i.
  (* Keep the pointer size symbolic as ptr_size_Z; hardcoding
     4 would prevent the PtrArray lemma below from matching. *)
  sep_apply_l_atomic
    (PtrArray.full_split_to_missing_i begin ii (Zlength source_words)
      tagged_enqueue_conflict_memory 0);
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_18 : solver_propagate_which_implies_wit_18.
Proof.
  aggressive_pre_process;
    bind_fact ( clause_lits_pointer (ms_binary Mscan) scratch_base0 ) as H_clause_lits_pointer;
  (* The RHS spells the segment base as [clause_lits_addr confl] while the LHS carries the
          binder [scratch_base0].  QCP cancellation is syntactic, so the two spellings must be
          brought together through their defining hypotheses before either arm can close. *)
    unfold clause_lits_pointer in H_clause_lits_pointer;
    subst confl;
    subst scratch_base0.
  - apply IntArray.full_to_seg.
  - entailer_with lia.
  - msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_20 : solver_propagate_which_implies_wit_20.
Proof.
  unfold solver_propagate_which_implies_wit_20.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  bind_fact ( propagation_scan_open n F A_arr K M0 Mentry Mscan p 0 source_words retained moved rest garbage
    watch_memory ii jj scan_current raw_suffix ) as H_propagation_scan_open.
  bind_fact ( propagation_binary_conflict_scan_ready n Mscan p scan_current source_words scan_wcap simp_count
    prop_count ) as H_propagation_binary_conflict_scan_r.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ (retained ++ rest) :: scan_wm_post ) as H_ms_wm.
  bind_fact ( ms_wcaps Mscan = scan_caps_pre ++ scan_wcap :: scan_caps_post ) as H_ms_wcaps.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  bind_fact ( Zlength scan_caps_pre = p ) as H_Zlength_2.
  bind_fact ( ws = vecp_slot wlists_entry p ) as H_ws.
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
  prop_apply
    (valid_store_ptr &( s # "solver_t" ->ₛ "binary") (ms_binary Mscan)).
  Intros.
  (* valid_store_ptr yields valid_ptr_value v, i.e.
     0 <= v <= addr_max_unsigned; micromega cannot see inside that
     definition, so the range side-condition stays open until unfolded. *)
  unfold valid_ptr_value in *.
  match goal with
  | Hbinvalid : isvalidptr _ /\ _ |- _ =>
      destruct Hbinvalid as [_ Hbinrange];
      destruct Hbinrange as [Hbinlo Hbinhi]
  end.
  unfold clause_lits_pointer in H_clause_lits_pointer.
  subst scratch_base.
  unfold propagation_binary_conflict_scan_ready in H_propagation_binary_conflict_scan_r.
  destruct H_propagation_binary_conflict_scan_r as
    (Htagged & Hcovers & Hearliest & Hlevel & Hsimp & Hprop &
     Hsource0 & Hsourcecap & Hcappos & Hcapmax).
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
  pose proof (msat_binary_conflict_route_weak_p3 n F A_arr K Mscan p
    scan_current Hweak) as Hroute_weak.
  pose proof (msat_binary_conflict_route_semantics_p3 n F A_arr K Mscan p
    scan_current retained rest raw_suffix scan_wm_pre scan_wm_post
    Hweak Hroute_weak Hshape Hp_wf Hprocessed Hlivelevel Hproplevel
    Hlivecovers Hliveearliest Hwatch_except Htagged Hrest
    Henq_assigned Henq_notsig H_ms_wm H_Zlength) as Hroute_sem.
  destruct (msat_binary_conflict_exit_package_p3 n F A_arr K M0 Mentry Mscan p
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
  cbn [msolver_propagation_binary_conflict
    msolver_propagation_overlay msolver_propagation_update ] in *.
  clear - Hexit Hiend Hjend H_ms_wm H_ms_wcaps H_Zlength H_Zlength_2 H_ws H_endvar
    Hsource0 Hsourcecap Hcappos Hcapmax Hbinary_pos Hbinary_even Hfr_route Hreuse_route.
  entailer_with ltac:(lia).
  unfold solver_propagation_scan_arrays_noqh_at,
    solver_propagation_scan_core_at, solver_binary_rep,
    stats_propagate_scan, MiniSatClause.rep, activity_state,
    clause_hdr_word, clause_hdr_addr, clause_act_addr, clause_lits_addr.
  rewrite Hfr_route.
  unfold msolver_propagation_binary_conflict,
    msolver_propagation_overlay, msolver_propagation_update.
  cbn.
  entailer_with ltac:(lia).
  all: try assumption.
  unfold PtrArray.seg, IntArray.seg, CharArray.seg.
  cbn.
  entailer_with ltac:(lia).
  csimpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_21 : solver_propagate_which_implies_wit_21.
Proof.
  Unfold; right; intros.
  msat_propagate_ptr_missing_merge_p3 begin ii source_words tagged_memory i;
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_22 : solver_propagate_which_implies_wit_22.
Proof.
  Unfold.
  right.
  intros.
  assert (Hl : enq_l = tag_lit scan_current) by lia.
  assert (Hr : enq_reason = tag_of_lit p_v) by lia.
  subst enq_l enq_reason.
  unfold enqueue_post_at.
  Intros qtail' assigns' levels' reasons' trail'.
  assert (Hret : enq_ret = 1).
  {
    unfold enqueue_transition in H.
    destruct H as [H | [H | H]];
      decompose [and] H; lia.
  }
  subst enq_ret.
  Exists qtail' assigns' levels' reasons' trail'.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_23 : solver_propagate_which_implies_wit_23.
Proof.
  Unfold.
  left.
  intros.
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
  { entailer_with ltac:(lia). }
  pose proof (msat_scan_keep_step_exists_p3 source_words retained moved rest
    garbage watch_memory raw_suffix ii jj scan_current
    H_propagation_watch_scan_physical H_rest) as Hphysical.
  pose proof H_solver_propagation_scan_semantics as Hsemkeep.
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [Hlive | Hconflict].
  2: { decompose [and] Hconflict; lia. }
  destruct Hlive as
    (Hlivezero & Hweak & Hproplevel & Hheapready & Hcovers &
     Hreasonless & Hplevel & Hp_wf & Hprocessed & Hfrontier & Hcarrier).
  destruct (msat_propagate_weak_core_fields_p3 n F A_arr K Mscan Hweak) as
    (Hdbwf & Htwf & Hshape & Hwmexact & Hstable & Hreasonsmem & Hreasonbin &
     Hsize).
  destruct (msat_scan_current_focus_facts_p3 n Mscan p scan_current qtail'
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
    pose proof (msat_enqueue_same_identity_p3 Mscan p scan_current Hqtrue)
      as HMidentity.
    pose proof (msat_scan_step_semantics_keep_p3 n F A_arr K Mscan p
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
    entailer_with ltac:(lia).
  - decompose [and] Hconflict; lia.
  - destruct Hfresh as
      (Hfreshcell & _ & Hassigneq & Hlevelseq & Hreasonseq & Htraileq &
       Hqtaileq).
    pose proof (msat_enqueue_fresh_scan_semantics_p3 n F A_arr K Mscan p
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

Lemma proof_of_solver_propagate_which_implies_wit_24 : solver_propagate_which_implies_wit_24.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan (Zlength scan_wm_pre) 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ logical_words :: scan_wm_post ) as H_ms_wm.
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
  assert (Hcurrent_in :
    In scan_current (Znth (Zlength scan_wm_pre) (ms_wm Mscan) nil)).
  {
    rewrite H_ms_wm.
    unfold Znth.
    rewrite Zlength_correct, Nat2Z.id, app_nth2 by lia.
    replace (length scan_wm_pre - length scan_wm_pre)%nat with 0%nat
      by lia.
    cbn.
    subst logical_words.
    apply in_or_app. right.
    rewrite Hrest. left. reflexivity.
  }
  unfold clause_is_lit_result in H_clause_is_lit_result.
  destruct H_clause_is_lit_result as [[Hret Htag] | [Hret Hreal]]; [lia|].
  destruct (wmap_real_witness n (msolver_db Mscan) (ms_wm Mscan)
    (Zlength scan_wm_pre) scan_current Hdbwf Hwmexact
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
      rewrite clause_db_rep_cons at 1.
      unfold clause_db_pair_focus.
      Exists (co_learnt co).
      unfold clause_db_pair_remainder.
      Left.
      Exists co pre post.
      entailer_with ltac:(int_auto).
    - apply in_split in Hlearnt as [pre [post Hlearnt]].
      rewrite Hlearnt.
      sep_apply (clause_db_rep_app_elim pre
        ((scan_current, co) :: post)).
      rewrite clause_db_rep_cons at 1.
      unfold clause_db_pair_focus.
      Exists (co_learnt co).
      unfold clause_db_pair_remainder.
      Right.
      Exists co pre post.
      entailer_with ltac:(int_auto).
  }
  Exists (co_lits co).
  sep_apply Hfocus.
  unfold lit_wf_c in Hw0, Hw1.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_25 : solver_propagate_which_implies_wit_25.
Proof.
  Unfold.
  right.
  intros.
  unfold clause_db_pair_focus, clause_db_pair_frame,
    MiniSatClause.rep, IntArray.full.
  Intros is_learnt.
  Exists is_learnt.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_26 : solver_propagate_which_implies_wit_26.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( 2 <= Zlength clause_contents ) as H_Zlength.
  destruct clause_contents as [|a0 tail]; [cbn in H_Zlength; lia|].
  destruct tail as [|a1 tail]; [cbn in H_Zlength; lia|].
  cbn [Znth].
  assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail))
    (a0 :: a1 :: tail) = tail).
  {
    replace (a0 :: a1 :: tail) with ((a0 :: a1 :: nil) ++ tail)
      by reflexivity.
    assert (Hrange : 2 <= 2 <=
      Zlength ((a0 :: a1 :: nil) ++ tail)).
    {
      split; [lia|].
      rewrite Zlength_app.
      change (2 <= 2 + Zlength tail).
      pose proof (Zlength_nonneg tail). lia.
    }
    rewrite (sublist_split_app_r 2
      (Zlength ((a0 :: a1 :: nil) ++ tail)) 2
      (a0 :: a1 :: nil) tail
      ltac:(reflexivity) Hrange).
    replace (Zlength ((a0 :: a1 :: nil) ++ tail) - 2)
      with (Zlength tail).
    2: {
      rewrite Zlength_app.
      replace (Zlength (a0 :: a1 :: nil)) with 2 by reflexivity.
      lia.
    }
    apply sublist_self. reflexivity.
  }
  rewrite Htail.
  sep_apply_l_atomic
    (IntArray.missing_i_to_seg_head clause_base 0
      (Zlength (a0 :: a1 :: tail)) a0 (a1 :: tail)).
  rewrite IntArray.seg_unfold.
  csimpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_search partial_solve wits (5 proofs) ===== *)
Lemma proof_of_solver_search_partial_solve_wit_161_pure : solver_search_partial_solve_wit_161_pure.
Proof.
  unfold solver_search_partial_solve_wit_161_pure.
  unfold stats_decisions.
  Unfold; right; intros; aggressive_pre_process.
  msat_search_activity_length_close_p3 n F A_arr A_inst Mdb.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_162_pure : solver_search_partial_solve_wit_162_pure.
Proof.
  unfold solver_search_partial_solve_wit_162_pure.
  unfold stats_decisions.
  Unfold; right; intros; aggressive_pre_process.
  msat_search_activity_length_close_p3 n F A_arr A_inst Mdb.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_163_pure : solver_search_partial_solve_wit_163_pure.
Proof.
  unfold solver_search_partial_solve_wit_163_pure.
  unfold stats_decisions.
  Unfold; right; intros; aggressive_pre_process.
  msat_search_activity_length_close_p3 n F A_arr A_inst Mdb.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_164_pure : solver_search_partial_solve_wit_164_pure.
Proof.
  unfold solver_search_partial_solve_wit_164_pure.
  unfold stats_decisions.
  Unfold; right; intros; aggressive_pre_process.
  msat_search_activity_length_close_p3 n F A_arr A_inst Mdb.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_165_pure : solver_search_partial_solve_wit_165_pure.
Proof.
  unfold solver_search_partial_solve_wit_165_pure.
  unfold stats_decisions.
  Unfold; right; intros; aggressive_pre_process.
  msat_search_activity_length_close_p3 n F A_arr A_inst Mdb.
Qed.

(* ===== solver_search which_implies wits (11 proofs) ===== *)
Lemma proof_of_solver_search_which_implies_wit_42 : solver_search_which_implies_wit_42.
Proof.
  unfold solver_search_which_implies_wit_42.
  unfold stats_decisions.
  Unfold.
  left; intros.
  bind_fact (msolver_seed_shadow Mdb) as Hseed_entry.
  unfold msolver_seed_shadow in Hseed_entry.
  destruct Hseed_entry as [seed_shadow [Hseed Hbounds]].
  assert (Hfp : fp64_eq (ms_random_seed Mdb) (Z_to_fp64 seed_shadow)).
  { rewrite Hseed. unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite.
      unfold seed_ok in Hbounds; lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite.
      unfold seed_ok in Hbounds; lia. }
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hdecaddr :
    &(s # "solver_t" ->ₛ "stats" .ₛ "decisions") =
    &(stats_ptr # "stats_t" ->ₛ "decisions")).
  { unfold stats_ptr. csimpl. reflexivity. }
  pose proof msat_stats_rep_open_decisions as Hstats_split.
  unfold solver_rep_levels_wl_at, solver_cancel_owned.
  Intros act asg opos rsn trl tgs.
  Exists opos asg act seed_shadow.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_search_order_frame_at.
  entailer_with ltac:(lia).
  Exists rsn trl tgs.
  unfold solver_scalars_rep, clause_new_scalars_frame,
    solver_fp_rep, solver_fp_without_seed_rep,
    solver_vecs_rep, solver_vecs_without_order_rep,
    stats_rep, stats_without_decisions_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  fold stats_ptr.
  rewrite Hdecaddr.
  fold (stats_rep stats_ptr (ms_stats Mdb)).
  fold (stats_without_decisions_rep stats_ptr (ms_stats Mdb)).
  apply _derivable1_andp_intros.
  - msat_cancel_sound.
    exact (Hstats_split stats_ptr (ms_stats Mdb)).
  - repeat lazymatch goal with
    | |- _ |-- _ && _ => apply _derivable1_andp_intros
    end.
    all: lazymatch goal with
    | |- _ |-- “ _ ” =>
        apply dump_spatial_left;
        solve [assumption | unfold seed_ok in Hbounds; lia]
    end.
Qed.

Lemma proof_of_solver_search_which_implies_wit_43 : solver_search_which_implies_wit_43.
Proof.
  unfold solver_search_which_implies_wit_43.
  Unfold.
  right; intros.
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
    entailer_with ltac:(lia).
  - split_pures; dump_pre_spatial;
      try exact Hreuse_selected; try exact Htransition;
      try exact Hdecay_selected; lia.
Qed.

Lemma proof_of_solver_search_which_implies_wit_44 : solver_search_which_implies_wit_44.
Proof.
  Unfold.
  right; intros.
  bind_fact ( solver_search_select_transition n F A_arr A_inst Mdb next orderpos_after order_after seed_after
    stats_after Mselected ) as H_solver_search_select_transition.
  unfold solver_search_select_transition in H_solver_search_select_transition.
  destruct H_solver_search_select_transition as (_ & _ & _ & _ & _ & [[Hret Hready] | Hselected]).
  - entailer_with ltac:(lia).
  - unfold solver_search_selection_state in Hselected. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_45 : solver_search_which_implies_wit_45.
Proof.
  Unfold.
  left; intros.
  bind_fact ( ms_size Mselected = n ) as H_ms_size.
  bind_fact ( ms_model Mselected = nil ) as H_ms_model.
  unfold solver_rep_levels_wl_at, solver_cancel_owned,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_model_copy_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at, solver_scalars_rep,
    solver_scalars_without_size_rep, clause_new_scalars_frame, solver_vecs_rep,
    solver_vecs_without_model_rep, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  Exists (ms_model_cap Mselected) asg act opos rsn trl tgs.
  rewrite <- H_ms_size, H_ms_model.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_46 : solver_search_which_implies_wit_46.
Proof.
  Unfold.
  right; intros.
  bind_fact ( model_copy_progress n Mselected model_words i ) as H_model_copy_progress.
  sep_apply_l_atomic
    (CharArray.seg_split_to_missing_i values 0 i n
      (mt_assigns (ms_core Mselected)) 0).
  - dump_pre_spatial. unfold model_copy_progress in H_model_copy_progress. lia.
  - replace (i - 0) with i by lia. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_47 : solver_search_which_implies_wit_47.
Proof.
  Unfold.
  right; intros.
  bind_fact ( solver_search_model_ready n F A_arr A_inst Mselected ) as H_solver_search_model_ready.
  bind_fact ( ms_size Mselected = n ) as H_ms_size.
  bind_fact ( model_copy_progress n Mselected model_words_now i ) as H_model_copy_progress.
  unfold solver_search_model_ready in H_solver_search_model_ready.
  destruct H_solver_search_model_ready as (Hinv & Hqhead & Horder & Hpending & Hseed & Hmodel0).
  unfold model_copy_progress in H_model_copy_progress.
  destruct H_model_copy_progress as (Hirange & Hmodellength & Hmodelwords).
  assert (Hi : i = n) by lia. subst i.
  set (Mdone := msolver_with_model Mselected model_words_now model_cap_now).
  assert (Hseed_done : msolver_seed_shadow Mdone) by exact Hseed.
  assert (Hcap_done : ms_cap Mdone = ms_cap Mselected) by reflexivity.
  lazymatch goal with
  | Hreuse : solver_search_reuse ?entry Mselected |- _ =>
      assert (Hreuse_done : solver_search_reuse entry Mdone) by exact Hreuse
  end.
  assert (Hweakdone : msolver_inv_weak n F A_arr A_inst Mdone).
  { unfold Mdone, msolver_with_model.
    destruct (msi_weak Hinv). constructor; assumption. }
  assert (Hinvdone : msolver_inv n F A_arr A_inst Mdone).
  { unfold Mdone, msolver_with_model.
    destruct Hinv as [Hweak Hprop Hwatch Hheap Hreason].
    constructor; [exact Hweakdone | exact Hprop | exact Hwatch |
      exact Hheap | exact Hreason]. }
  assert (Hcopy : model_copies n Mdone).
  { unfold model_copies, Mdone, msolver_with_model. simpl.
    split; [lia|]. intros v Hv.
    rewrite Hmodelwords, Znth_sublist by lia.
    replace (v + 0) with v by lia. reflexivity. }
  assert (Hfix : mt_qhead (ms_core Mdone) =
      Zlength (mt_trail (ms_core Mdone))).
  { unfold Mdone, msolver_with_model. simpl.
    pose proof (msi_shape Hinv) as Hshape.
    unfold solver_shape in Hshape. rewrite Hqhead. lia. }
  assert (Hsaved : model_saved n F A_arr Mdone).
  { eapply sat_endgame_model with (A_inst := A_inst).
    - exact Hweakdone.
    - exact (msi_watch_frontier Hinvdone).
    - exact (msi_heap_covers Hinvdone).
    - exact Hfix.
    - unfold Mdone, msolver_with_model. exact Horder.
    - exact Hcopy. }
  Exists model_words_now model_cap_now Mdone.
  split_pure_spatial.
  - unfold model_copy_finish. entailer_with ltac:(first [assumption | lia]).
    unfold solver_model_copy_frame_at, solver_without_assigns_frame_wl_at,
      solver_without_assigns_cells_at, solver_rep_assigns_levels_at,
      solver_rep_at, solver_nonlevel_rep_at,
      solver_nonlevel_rep_nostats_at, solver_scalars_without_size_rep,
      solver_vecs_without_model_rep, solver_scalars_rep, solver_vecs_rep,
      clause_new_scalars_frame, solver_fp_rep, solver_levels_slice_at,
      solver_trail_array_rep.
    Intros act opos rsn trl tgs.
    Exists act opos rsn trl tgs.
    unfold Mdone, msolver_with_model. simpl.
    apply _derivable1_andp_intros.
    + apply dump_spatial_left. exact (msi_shape Hinvdone).
    + rewrite H_ms_size.
      msat_cancel_sound. change (emp |-- emp). reflexivity.
  - unfold model_copy_finish. msat_manual_entailer_with ltac:(first [assumption | lia]).
Qed.

Lemma proof_of_solver_search_which_implies_wit_49 : solver_search_which_implies_wit_49.
Proof.
  Unfold.
  right. intros.
  bind_fact ( model_copy_finish n F A_arr A_inst Mselected model_words model_cap_done Mdone ) as H_model_copy_finish.
  unfold model_copy_finish in H_model_copy_finish.
  destruct H_model_copy_finish as (_ & Hinv & Hqtail & _ & _ & _).
  assert (Hshape : solver_shape Mdone).
  { exact (msi_shape Hinv). }
  pose proof (msi_size Hinv) as Hsize.
  assert (Htrail : mtrail_wf (ms_size Mdone) (ms_core Mdone)).
  { rewrite <- Hsize. exact (msi_trail_wf Hinv). }
  assert (Hheap : heap_wf (ms_size Mdone) (msolver_heap Mdone)).
  { rewrite <- Hsize. exact (msi_heap_wf Hinv). }
  assert (Hrange :
      0 <= ms_root_level Mdone <= Zlength (mt_lim (ms_core Mdone))).
  { exact (msi_root_range Hinv). }
  assert (Htrail_len :
      Zlength (mt_trail (ms_core Mdone)) = ms_qtail Mdone).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hcancel : cancel_bound_ready Mdone (ms_root_level Mdone)).
  { unfold cancel_bound_ready.
    destruct (Z_lt_le_dec (ms_root_level Mdone)
      (Zlength (mt_lim (ms_core Mdone)))) as [Hlt | Hge].
    - right.
      pose proof (lim_lt_trail (ms_size Mdone) (ms_core Mdone)
        (ms_root_level Mdone) Htrail (conj (proj1 Hrange) Hlt)) as Hlim.
      rewrite Htrail_len in Hlim. rewrite <- Hqtail in Hlim. lia.
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

Lemma proof_of_solver_search_which_implies_wit_50 : solver_search_which_implies_wit_50.
Proof.
  Unfold.
  right; intros.
  bind_fact ( model_copy_finish n F A_arr A_inst Mselected model_words model_cap_done Mdone ) as H_model_copy_finish.
  unfold model_copy_finish in H_model_copy_finish.
  destruct H_model_copy_finish as (_ & Hinv & Hqtail & Horder & Hpending & Hseed & Hsaved).
  unfold solver_cancel_post.
  Split.
  - Intros.
    Exists Mdone.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep_levels_at s Mdone levels search_wl).
      entailer_with ltac:(lia).
    + pose proof (msw_root_range (msi_weak Hinv)) as Hr.
      assert (Hroot : solver_at_root Mdone).
      { unfold solver_at_root. lia. }
      entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hre).
    set (Mrestart := msolver_cancel_project Mdone
      (ms_root_level Mdone) orderpos order order_cap
      (ms_root_level Mdone)).
    assert (Hweak : msolver_inv_weak n F A_arr A_inst Mrestart).
    { unfold Mrestart. apply msolver_inv_weak_cancel__search
        with (M := Mdone) (level := ms_root_level Mdone)
             (orderpos := orderpos) (order := order) (order_cap := order_cap).
      - exact (msi_weak Hinv).
      - exact Hlevel.
      - reflexivity.
      - exact Hcap.
      - exact Hheap.
      - exact Hincl.
      - exact Hre. }
    assert (Hseed_restart : msolver_seed_shadow Mrestart) by exact Hseed.
    Exists Mrestart.
    split_pure_spatial.
    + unfold Mrestart.
      sep_apply (solver_cancel_project_join_rep_levels_at s Mdone levels
        (ms_root_level Mdone) orderpos order order_cap (ms_root_level Mdone) search_wl).
      entailer_with ltac:(lia).
    + pose proof (msi_trail_wf Hinv) as Htrail.
      assert (Hbound : Znth (ms_root_level Mdone)
          (mt_lim (ms_core Mdone)) 0 <= mt_qhead (ms_core Mdone)).
      { apply Forall_Znth_elim; [exact (msi_prop_level Hinv)|lia]. }
      lazymatch goal with
      | Hreuse : solver_search_reuse ?entry Mdone |- _ =>
          assert (Hreuse_restart : solver_search_reuse entry Mrestart)
            by (intro Hbase; unfold Mrestart;
                exact (minisat_base_completion_cancel__api_reentry
                  n Mdone (ms_root_level Mdone) orderpos order order_cap
                  (ms_root_level Mdone) Htrail (msw_db_wf (msi_weak Hinv))
                  Hlevel Hbound (Hreuse Hbase)))
      end.
      assert (Hprop : prop_level (ms_core Mrestart)).
      { unfold Mrestart. apply (prop_level_cancel n (ms_core Mdone)
          (ms_root_level Mdone)).
        - exact Htrail.
        - exact Hlevel. }
      assert (Hwatch : minisat_watch_frontier n (msolver_db Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply minisat_watch_frontier_cancel__search
          with (M := Mdone) (level := ms_root_level Mdone)
               (orderpos := orderpos) (order := order) (order_cap := order_cap)
               (root := ms_root_level Mdone).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_watch_frontier Hinv). }
      assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
      { rewrite (msi_size Hinv). exact Hheap. }
      assert (Hheapcov : heap_covers n (msolver_heap Mrestart)
          (mt_assigns (ms_core Mrestart)) (mt_trail (ms_core Mrestart))
          (mt_qhead (ms_core Mrestart))).
      { unfold Mrestart. apply heap_covers_cancel_project__canceluntil_cap
          with (M := Mdone) (level := ms_root_level Mdone)
               (orderpos := orderpos) (order := order).
        - exact Htrail.
        - exact Hlevel.
        - exact Hbound.
        - exact (msi_heap_wf Hinv).
        - exact Hheap_n.
        - exact Hincl.
        - exact (msi_heap_covers Hinv).
        - exact Hre. }
      assert (Hreasonless : current_reasonless_earliest n Mrestart).
      { unfold current_reasonless_earliest.
        intros d Hd v Hlev Hword.
        unfold Mrestart, msolver_cancel_project, msolver_core_heap_update in Hd.
        simpl in Hd. rewrite Zlength_ztake in Hd by lia. lia. }
      assert (Hinv_restart : msolver_inv n F A_arr A_inst Mrestart).
      { refine {| msi_weak := Hweak; msi_prop_level := Hprop;
                 msi_watch_frontier := Hwatch; msi_heap_covers := Hheapcov;
                 msi_reasonless_current := Hreasonless |}. }
      assert (HrootM : solver_at_root Mrestart).
      { unfold solver_at_root, Mrestart, msolver_cancel_project,
          msolver_core_heap_update. simpl. rewrite Zlength_ztake by lia.
        lia. }
      assert (Hqtail_restart : mt_qhead (ms_core Mrestart) = ms_qtail Mrestart).
      { unfold Mrestart, msolver_cancel_project, msolver_core_heap_update.
        reflexivity. }
      assert (Hsaved_restart : model_saved n F A_arr Mrestart).
      { unfold model_saved in *.
        unfold Mrestart, msolver_cancel_project, msolver_core_heap_update.
        simpl. exact Hsaved. }
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_51 : solver_search_which_implies_wit_51.
Proof.
  Unfold.
  right; intros.
  bind_fact ( solver_search_select_transition n F A_arr A_inst Mdb next orderpos_after order_after seed_after
    stats_after Mselected ) as H_solver_search_select_transition.
  bind_fact ( next <> -1 ) as H_next.
  unfold solver_search_select_transition in H_solver_search_select_transition.
  destruct H_solver_search_select_transition as (_ & _ & _ & _ & _ & [[Hret Hready] | Hselected]).
  - exfalso. apply H_next. exact Hret.
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_52 : solver_search_which_implies_wit_52.
Proof.
  Unfold. right; intros.
  bind_fact ( solver_search_selection_state n F A_arr A_inst next Mselected ) as H_solver_search_selection_state.
  pose proof (solver_search_selection_pure__search
    n F A_arr A_inst next Mselected H_solver_search_selection_state) as [Hlim Henqueue].
  pose proof H_solver_search_selection_state as Hsel.
  unfold solver_search_selection_state in Hsel.
  destruct Hsel as (Hweak & _ & _ & _ & _ & Hdrain & _).
  pose proof (msw_size Hweak) as Hsize.
  sep_apply (solver_rep_levels_at_assume_focus__search
    s Mselected levels search_wl).
  Intros decision_asg. Exists decision_asg.
  rewrite <- Hsize, Hdrain.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_53 : solver_search_which_implies_wit_53.
Proof.
  Unfold. right; intros.
  bind_fact ( solver_search_selection_state n F A_arr A_inst next Mselected ) as H_solver_search_selection_state.
  bind_fact ( enqueue_input n (lit_neg_c (next + next)) (ms_qtail Mselected) (mt_assigns (ms_core Mselected))
    (mt_levels (ms_core Mselected)) (ms_reason_words Mselected) (mt_trail (ms_core Mselected)) ) as H_enqueue_input.
  assert (Hdecision : decision_lit = lit_neg_c (next + next)) by lia.
  subst decision_lit.
  pose proof H_solver_search_selection_state as Hsel.
  unfold solver_search_selection_state in Hsel.
  destruct Hsel as
    (Hweak & Hprop & Hwatch & Hreasonless & Hpending & Hdrain &
     Hseed & Hmodel & Hdecay & Htwice & Hnext & Hfresh & Hheap).
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_size Hweak) as Hsize.
  pose proof H_enqueue_input as Henq.
  unfold enqueue_input in Henq.
  destruct Henq as [Hlit [Htwice' [Haslen [Hlvlen [Hrslen
    [Htrlen [Hqrange [Hroom Hcells]]]]]]]].
  assert (Hvar : lit_var_c (lit_neg_c (next + next)) = next).
  { rewrite lit_var_c_neg. unfold lit_var_c.
    replace (next + next) with (next * 2) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hfreshl :
      Znth (lit_var_c (lit_neg_c (next + next)))
        (mt_assigns (ms_core Mselected)) 0 = 0).
  { rewrite Hvar. exact Hfresh. }
  assert (Hroomcap : ms_qtail Mselected < ms_cap Mselected).
  { specialize (Hroom Hfreshl). unfold solver_shape in Hshape. lia. }
  sep_apply (assume_post_refold__search
    search_wl s decision_asg levels (lit_neg_c (next + next))
    n (ms_cap Mselected) (ms_qtail Mselected)
    (mt_assigns (ms_core Mselected)) (mt_levels (ms_core Mselected))
    (ms_reason_words Mselected) (mt_trail (ms_core Mselected))
    (mt_lim (ms_core Mselected)) (ms_lim_cap Mselected) Mselected
    Hsize ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity)
    Hshape Hroomcap Hpending Hdrain Hfreshl).
  Intros lim_cap_after.
  assert (Hcap_decision : ms_cap
    (msolver_assume Mselected (lit_neg_c (next + next)) lim_cap_after) =
    ms_cap Mselected) by reflexivity.
  lazymatch goal with
  | Hreuse : solver_search_reuse ?entry Mselected |- _ =>
      assert (Hreuse_decision : solver_search_reuse entry
        (msolver_assume Mselected (lit_neg_c (next + next)) lim_cap_after))
      by (intro Hbase;
          apply (minisat_base_watch_completed_assume__api_reentry
            n Mselected (lit_neg_c (next + next)) lim_cap_after
            (msw_db_wf Hweak) (msw_trail_wf Hweak) Hlit Hfreshl);
          exact (Hreuse Hbase))
  end.
  Exists lim_cap_after
    (msolver_assume Mselected (lit_neg_c (next + next)) lim_cap_after).
  entailer_with ltac:(first [assumption | lia]).
  eapply solver_search_decision_pure__search; eauto.
Qed.

(* ===== solver_simplify entail wits (10 proofs) ===== *)
Lemma proof_of_solver_simplify_entail_wit_1 : solver_simplify_entail_wit_1.
Proof.
  Unfold.
  right.
  intros.
  match goal with
  | Hnormalize : M_solver_simplify_spec =
      msolver_resume_pending smp_physical_entry_solver_simplify_spec |- _ =>
      rewrite <- Hnormalize in *
  end.
  bind_fact (msolver_inv_assuming_strong smp_n_solver_simplify_spec
    smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec M_solver_simplify_spec) as Hentry.
  bind_fact (Zlength (mt_lim (ms_core M_solver_simplify_spec)) = 0) as Hdepth.
  unfold solver_propagate_post.
  unfold solver_simplify_post_at.
  Split.
  - Split.
    + Intros M1. LLM_pre_process ltac:(lia).
    + Intros M0 p focus C. LLM_pre_process ltac:(lia).
  - unfold solver_propagation_capacity_raw.
    Intros Mnext.
    LLM_pre_process ltac:(lia).
    match goal with Hpost : solver_propagation_inv _ _ _ _ Mnext /\ _ |- _ =>
      destruct Hpost as [Hprop [Hframe [Hreuse [Hseed Hrest]]]]
    end.
    pose proof Hprop as Hprop_copy.
    cbn in Hprop_copy. destruct Hprop_copy as [Hpending Hprop_inv].
    pose proof (msap_weak smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec smp_A_arr_solver_simplify_spec Mnext Hprop_inv) as Hweak.
    destruct Hframe as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
    assert (Hlim0 : Zlength (mt_lim (ms_core Mnext)) = 0).
    { rewrite Hlim. exact Hdepth. }
    assert (Hcomplete : minisat_watch_completed M_solver_simplify_spec ->
      minisat_watch_completed Mnext).
    { intro Hcompleted.
      apply (minisat_base_completion_at_depth_zero__api_reentry
        smp_n_solver_simplify_spec Mnext
        (msa_trail_wf Hweak) (msa_db_wf Hweak) Hlim0).
      apply (proj1 Hreuse).
      eapply minisat_full_completion_implies_base__api_reentry;
        [exact (msa_trail_wf (msas_weak Hentry))|
         exact (msa_db_wf (msas_weak Hentry))|exact Hcompleted]. }
    sep_apply_l_atomic
      (solver_propagation_capacity_rep_at_refold
         s_pre Mnext assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec).
    sep_apply_l_atomic
      (solver_rep_assigns_levels_at_levels_at
         s_pre Mnext assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec).
    Exists 0.
    Right.
    Exists Mnext.
    entailer_with ltac:(int_auto).
    intro Hempty.
    rewrite Hmodel. exact Hempty.
Qed.

Lemma proof_of_solver_simplify_entail_wit_2 : solver_simplify_entail_wit_2.
Proof.
  Unfold.
  right.
  intros.
  match goal with
  | Hnormalize : M_solver_simplify_spec =
      msolver_resume_pending smp_physical_entry_solver_simplify_spec |- _ =>
      rewrite <- Hnormalize in *
  end.
  bind_fact ( Zlength (mt_lim (ms_core M_solver_simplify_spec)) = 0 ) as H_Zlength.
  bind_fact (msolver_inv_assuming_strong smp_n_solver_simplify_spec
    smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec M_solver_simplify_spec) as Hentry.
  unfold solver_propagate_post.
  unfold solver_simplify_post_at.
  Split.
  - Split.
    + Intros M1. LLM_pre_process ltac:(lia).
    + Intros Mnext p focus C. LLM_pre_process ltac:(lia).
      destruct H0 as [Hready [Hframe [Hreuse [Hresident [Hseed [Hcert Hptr]]]]]].
      pose proof Hready as Hcancel.
      destruct Hready as [[Hcap Hweak] Hready_tail].
      cbn in Hweak.
      assert (Hlen : Zlength (mt_lim
        (ms_core Mnext)) = 0).
      { rewrite (proj1 Hframe). exact H_Zlength. }
      destruct Hframe as [_ [Hroot [_ [_ Hcapacity]]]].
      assert (Hrecovery : minisat_watch_completed M_solver_simplify_spec ->
        solver_base_recovery smp_n_solver_simplify_spec smp_F_solver_simplify_spec Mnext /\
        msolver_seed_shadow Mnext).
      { intro Hcompleted. split; [|exact Hseed].
        eapply solver_propagation_conflict_base_recovery__api_reentry;
          [exact Hcancel| |exact Hresident|exact Hlen].
        apply Hreuse.
        eapply minisat_full_completion_implies_base__api_reentry;
          [exact (msa_trail_wf (msas_weak Hentry))|
           exact (msa_db_wf (msas_weak Hentry))|exact Hcompleted]. }
      destruct Hcert as [Hent [Hfalse [Hwf Hcert_tail]]].
      assert (Hunsat : sat_shared_lib.cnf_unsat smp_n_solver_simplify_spec
        (sat_shared_lib.cnf_with_units smp_F_solver_simplify_spec
           smp_A_arr_solver_simplify_spec)).
      { eapply assuming_conflict_unsat; eauto. }
      sep_apply_l_atomic
        (solver_rep_assigns_levels_at_levels_at
           s_pre Mnext assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec).
      Exists p.
      Left. Right.
      Exists Mnext.
      entailer_with ltac:(lia).
      unfold cancel_bound_ready. left. lia.
  - LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_entail_wit_3_1 : solver_simplify_entail_wit_3_1.
Proof.
  Unfold; right; intros.
  match goal with
  | Hnormalize : M_solver_simplify_spec =
      msolver_resume_pending smp_physical_entry_solver_simplify_spec |- _ =>
      rewrite <- Hnormalize in *
  end.
  msat_simplify_propagation_frame_p3 M_solver_simplify_spec Mprop s_pre assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec.
Qed.

Lemma proof_of_solver_simplify_entail_wit_3_2 : solver_simplify_entail_wit_3_2.
Proof.
  Unfold; right; intros.
  match goal with
  | Hnormalize : M_solver_simplify_spec =
      msolver_resume_pending smp_physical_entry_solver_simplify_spec |- _ =>
      rewrite <- Hnormalize in *
  end.
  msat_simplify_propagation_frame_p3 M_solver_simplify_spec Mprop s_pre assigns_prop levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec.
Qed.

Lemma proof_of_solver_simplify_entail_wit_4 : solver_simplify_entail_wit_4.
Proof.
  Unfold.
  right.
  intros.
  match goal with
  | Hnormalize : M_solver_simplify_spec =
      msolver_resume_pending smp_physical_entry_solver_simplify_spec |- _ =>
      rewrite <- Hnormalize in *
  end.
  bind_fact ( ms_model M_solver_simplify_spec = nil -> ms_model Mprop = nil ) as H_model_empty.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
    msat_fp32_positive_finite (ms_cla_decay Mprop) ) as H_decay_positive.
  unfold solver_simplify_outer_loop.
  Exists Mprop.
  entailer_with ltac:(lia); assumption.
Qed.

Lemma proof_of_solver_simplify_entail_wit_5_1 : solver_simplify_entail_wit_5_1.
Proof.
  Unfold; right; intros; LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_entail_wit_5_2 : solver_simplify_entail_wit_5_2.
Proof.
  Unfold; right; intros; LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_entail_wit_6_1 : solver_simplify_entail_wit_6_1.
Proof.
  Unfold.
  right; intros; (LLM_pre_process ltac:(lia)); entailer_with ltac:(lia).
  subst type.
  bind_fact ( words_type = db_words (solver_selected_db 1 Mtype) ) as H_words_type.
  unfold solver_simplify_db_compaction_inv.
  unfold db_words.
  unfold db_words in H_words_type.
  rewrite <- H_words_type.
  repeat split; try lia.
  rewrite Zsublist_nil by lia.
  simpl.
  unfold sublist.
  simpl.
  rewrite Zlength_correct, Nat2Z.id.
  symmetry.
  apply List.firstn_all.
Qed.

Lemma proof_of_solver_simplify_entail_wit_6_2 : solver_simplify_entail_wit_6_2.
Proof.
  Unfold.
  right; intros; (LLM_pre_process ltac:(lia)); entailer_with ltac:(lia).
  bind_fact ( type = 0 ) as H_type.
  bind_fact ( words_type = db_words (solver_selected_db type Mtype) ) as H_words_type.
  rewrite H_type in H_words_type.
  rewrite <- H_words_type.
  subst type.
  all: (unfold solver_simplify_db_compaction_inv);
    (repeat split; try lia).
  all: (unfold db_words in H_words_type);
    (rewrite <- H_words_type);
    (rewrite Zsublist_nil by lia);
    (simpl);
    (unfold sublist);
    (simpl);
    (rewrite Zlength_correct, Nat2Z.id);
    (symmetry);
    (apply List.firstn_all).
Qed.

Lemma proof_of_solver_simplify_entail_wit_7_1 : solver_simplify_entail_wit_7_1.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_simplify_compaction_step smp_n_solver_simplify_spec smp_F_solver_simplify_spec
    smp_A_arr_solver_simplify_spec type Mcur words i jcur Mnext_2 words jcur ) as
      H_solver_simplify_compaction_step.
  bind_fact ( ms_model M_solver_simplify_spec = nil -> ms_model Mcur = nil ) as H_model_empty.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
    msat_fp32_positive_finite (ms_cla_decay Mcur) ) as H_decay_positive.
  bind_fact (solver_simplify_reuse M_solver_simplify_spec Mcur) as Hreuse_current.
  assert (Htransport : ms_cap Mnext_2 = ms_cap Mcur /\
    ms_root_level Mnext_2 = ms_root_level Mcur /\
    solver_simplify_reuse M_solver_simplify_spec Mnext_2).
  { destruct (proj1 H_solver_simplify_compaction_step) as
      [[Hkeep [Heq Hwords]]|[Hdrop [Hwords [wm [stats [Heq Hdelete]]]]]].
    - rewrite Heq. split; [reflexivity|split; [reflexivity|exact Hreuse_current]].
    - rewrite Heq. split; [reflexivity|split; [reflexivity|]].
      unfold solver_simplify_reuse in *. intro Hentry.
      apply minisat_watch_completed_remove_clause__api_reentry.
      exact (Hreuse_current Hentry). }
  destruct Htransport as [Hcap_next [Hroot_next Hreuse_next]].
  unfold solver_simplify_compaction_step in H_solver_simplify_compaction_step.
  destruct H_solver_simplify_compaction_step as
    [Htransition [Hinv [Hlen [Hqhead [Hcap [Hseed
      [Hmodel [Hdecay Hcomp]]]]]]]].
  LLM_pre_process ltac:(lia).
  entailer_with ltac:(lia).
  - intro Hempty. rewrite Hmodel. exact (H_model_empty Hempty).
  - intro Hpositive. rewrite Hdecay. exact (H_decay_positive Hpositive).
Qed.

(* ===== solver_simplify safety wits (2 proofs) ===== *)
Lemma proof_of_solver_simplify_safety_wit_22 : solver_simplify_safety_wit_22.
Proof.
  Unfold.
  left.
  intros.
  unfold vecp_rep_at.
  LLM_pre_process ltac:(lia).
  entailer_with ltac:(lia);
    unfold solver_simplify_compaction_step in *;
    unfold solver_simplify_db_compaction_inv in *;
    lia.
Qed.

Lemma proof_of_solver_simplify_safety_wit_23 : solver_simplify_safety_wit_23.
Proof.
  Unfold.
  right.
  intros.
  unfold solver_simplify_outer_loop.
  Intros Mnext.
  LLM_pre_process ltac:(lia).
Qed.

(* ===== solver_solve which_implies wits (2 proofs) ===== *)
Lemma proof_of_solver_solve_which_implies_wit_35 : solver_solve_which_implies_wit_35.
Proof.
  Unfold. right; intros M A_arr F n solve_wl Mterminal terminal_levels status s; intros.
  bind_fact (status = 1) as Hstatus.
  bind_fact (status = 1 -> model_saved n F A_arr Mterminal /\
    solver_sat_cancel_ready n F A_arr Mterminal) as Hsat.
  bind_fact (solver_terminal_reuse n F A_arr M Mterminal status) as Hreuse.
  destruct (Hsat Hstatus) as [Hmodel Hready].
  pose proof Hready as Hready_copy.
  destruct Hready_copy as [A_inst [Hinv [Hdrain [Hpending Hseed_old]]]].
  assert (Hbase : solver_query_reuse_guard M -> minisat_base_watch_completed Mterminal).
  { intro Hentry. exact (proj1 (Hreuse Hentry) Hstatus). }
  unfold solver_cancel_post.
  Split.
  - Intros.
    assert (Hlen : Zlength (mt_lim (ms_core Mterminal)) <= 0) by assumption.
    assert (Hdepth : Zlength (mt_lim (ms_core Mterminal)) = 0).
    { pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia. }
    destruct (solver_sat_query_ready_empty__solve n F A_arr Mterminal Hready Hlen)
      as [Hquery Hseed].
    assert (Hwatch : solver_query_reuse_guard M -> minisat_watch_completed Mterminal).
    { intro Hentry.
      exact (minisat_base_completion_at_depth_zero__api_reentry n Mterminal
        (msi_trail_wf Hinv) (msi_db_wf Hinv) Hdepth (Hbase Hentry)). }
    Exists Mterminal. unfold solver_sat_arm_at.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep s Mterminal terminal_levels solve_wl).
      entailer_with ltac:(lia).
    + entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hreinserted).
    set (Mpost := msolver_cancel_project Mterminal 0 orderpos order order_cap
      (ms_root_level Mterminal)).
    assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mterminal))) by lia.
    destruct (solver_sat_query_ready_cancel__solve n F A_arr Mterminal
      orderpos order order_cap Hready Hpositive Hcap Hheap Hincl Hreinserted)
      as [Hquery Hseed].
    assert (Hbound : Znth 0 (mt_lim (ms_core Mterminal)) 0 <=
      mt_qhead (ms_core Mterminal)).
    { exact (Forall_Znth_elim _ _ _ 0 0 (msi_prop_level Hinv) Hlevel). }
    assert (Hwatch : solver_query_reuse_guard M -> minisat_watch_completed Mpost).
    { intro Hentry.
      exact (minisat_base_completion_cancel_zero__api_reentry n Mterminal
        orderpos order order_cap (ms_root_level Mterminal)
        (msi_trail_wf Hinv) (msi_db_wf Hinv) Hpositive Hbound (Hbase Hentry)). }
    Exists Mpost. unfold solver_sat_arm_at.
    split_pure_spatial.
    + unfold Mpost.
      sep_apply (solver_cancel_project_join_rep s Mterminal terminal_levels 0
        orderpos order order_cap (ms_root_level Mterminal) solve_wl).
      entailer_with ltac:(lia).
    + unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
      cbn. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_36 : solver_solve_which_implies_wit_36.
Proof.
  Unfold. right; intros M A_arr F n solve_wl Mterminal terminal_levels status s; intros.
  bind_fact (status = -1) as Hstatus.
  bind_fact (status = -1 -> cnf_unsat n (cnf_with_units F A_arr)) as Hverdict.
  bind_fact (solver_terminal_reuse n F A_arr M Mterminal status) as Hreuse.
  bind_fact (ms_size Mterminal = n) as Hsize.
  assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)) by
    (apply Hverdict; exact Hstatus).
  unfold solver_cancel_post.
  Split.
  - Intros.
    assert (Hdepth : Zlength (mt_lim (ms_core Mterminal)) = 0).
    { pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mterminal /\ solver_query_reentry n F Mterminal /\ msolver_seed_shadow Mterminal).
    { intro Hentry.
      destruct (proj2 (Hreuse Hentry) Hstatus)
        as [A_inst [Hseed [Hconflict|Hbase]]].
      - destruct Hconflict as [focus [Hready [Hwatch Hfalse]]].
        pose proof (solver_propagation_conflict_base_recovery__api_reentry
          n F A_arr (PropagationStable A_inst) Mterminal focus
          Hready Hwatch Hfalse Hdepth) as Hbase_post.
        split; [exact Hbase_post|]. split; [|exact Hseed].
        exact (solver_base_recovery_false_reentry__api_reentry
          n F Mterminal Hbase_post Hfalse).
      - destruct Hbase as [Hbase_post Hfalse].
        split; [exact Hbase_post|]. split; [|exact Hseed].
        exact (solver_base_recovery_false_reentry__api_reentry
          n F Mterminal Hbase_post Hfalse). }
    Exists Mterminal. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep s Mterminal terminal_levels solve_wl).
      entailer_with ltac:(lia).
    + entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hreinserted).
    set (Mpost := msolver_cancel_project Mterminal 0 orderpos order order_cap
      (ms_root_level Mterminal)).
    assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mterminal))) by lia.
    assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
    { rewrite <- Hsize. exact Hheap. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mpost /\ solver_query_reentry n F Mpost /\ msolver_seed_shadow Mpost).
    { intro Hentry.
      destruct (proj2 (Hreuse Hentry) Hstatus)
        as [A_inst [Hseed [Hconflict|Hbase]]].
      - destruct Hconflict as [focus [Hready [Hwatch Hfalse]]].
        destruct (solver_conflict_cancel_zero_base_recovery__api_reentry
          n F A_arr (PropagationStable A_inst) Mterminal focus
          orderpos order order_cap Hready Hwatch Hseed Hpositive Hcap
          Hheap_n Hincl Hreinserted) as [Hbase_post [_ Hseed_post]].
        split; [exact Hbase_post|]. split; [|exact Hseed_post].
        exact (solver_cancel_project_reentry__api_reentry
          n F Mterminal orderpos order order_cap (ms_root_level Mterminal) Hbase_post).
      - destruct Hbase as [[[ _ [Hdepth _]] _] _]. lia. }
    Exists Mpost. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + unfold Mpost.
      sep_apply (solver_cancel_project_join_rep s Mterminal terminal_levels 0
        orderpos order order_cap (ms_root_level Mterminal) solve_wl).
      entailer_with ltac:(lia).
    + unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
      cbn. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== sortrnd entail wits (9 proofs) ===== *)
Lemma proof_of_sortrnd_entail_wit_1 : sortrnd_entail_wit_1.
Proof.
  aggressive_pre_process.
  assert (Hfp : fp64_eq (Z_to_fp64 z2) (Z_to_fp64 z2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  assert (Hinv : sortrnd_partition_inv srt_db srt_activities srt_origin srt_origin
                   (Zlength srt_origin) (Znth (retval - 0) srt_origin 0)
                   (-1) (Zlength srt_origin)).
  { replace (retval - 0) with retval by lia.
    eapply sortrnd_initial_partition__solve; eauto.
    lia. }
  Exists z2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_2 : sortrnd_entail_wit_2.
Proof.
  right. intros.
  bind_fact ( retval < 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities (Znth (i - 0) current_2 0) pivot retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_left_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot (i - 1) j ) as
    H_sortrnd_left_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < size_pre ) as H_i_2.
  bind_fact ( 0 < j ) as H_j.
  bind_fact ( j <= size_pre ) as H_j_2.
  bind_fact ( fp64_eq seed_value_now_2 (Z_to_fp64 seed_shadow_now_2) ) as H_fp64_eq.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_left_scan_inv in *.
  pose proof
    (sortrnd_left_scan_step__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_left_scan_inv H_learnt_cmp_result H_retval H_Zlength
       H_i H_i_2 H_j H_j_2) as [Hb Hinv].
  replace (i + 1 - 1) with i by lia.
  assert (Hseedok : seed_ok seed_shadow_now_2) by (unfold seed_ok; lia).
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow_now_2)
                          (Z_to_fp64 seed_shadow_now_2)).
  { rewrite <- (fp64_eq_seed_exact__search _ _ Hseedok H_fp64_eq) at 1.
    exact H_fp64_eq. }
  entailer_with ltac:(lia).
  Exists seed_shadow_now_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_3 : sortrnd_entail_wit_3.
Proof.
  right. intros.
  bind_fact ( sortrnd_partition_inv srt_db srt_activities srt_origin current_2 size_pre pivot i j ) as
    H_sortrnd_partition_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  unfold sortrnd_left_scan_inv.
  pose proof
    (sortrnd_left_scan_entry__sortrnd
       _ _ _ _ _ _ _ _ H_sortrnd_partition_inv H_Zlength) as [Hb Hinv].
  replace (i + 1 - 1) with i by lia.
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow_now_2)
                          (Z_to_fp64 seed_shadow_now_2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite; lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  entailer_with ltac:(lia).
  Exists seed_shadow_now_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_4 : sortrnd_entail_wit_4.
Proof.
  right. intros.
  bind_fact ( retval < 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities pivot (Znth (j - 0) current_2 0) retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < size_pre ) as H_j_2.
  rewrite ?Z.sub_0_r in *.
  pose proof
    (sortrnd_right_scan_step__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_right_scan_inv H_learnt_cmp_result H_retval H_Zlength
       H_j H_j_2) as [Hb Hinv].
  replace (j - 1 + 1) with j by lia.
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow_now_2)
                          (Z_to_fp64 seed_shadow_now_2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite; lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists seed_shadow_now_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_5 : sortrnd_entail_wit_5.
Proof.
  right. intros.
  bind_fact ( retval >= 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities (Znth (i - 0) current_2 0) pivot retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_left_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot (i - 1) j ) as
    H_sortrnd_left_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < size_pre ) as H_i_2.
  bind_fact ( 0 < j ) as H_j.
  bind_fact ( j <= size_pre ) as H_j_2.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_left_scan_inv in H_sortrnd_left_scan_inv.
  pose proof
    (sortrnd_right_scan_entry__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_left_scan_inv H_learnt_cmp_result H_retval H_Zlength
       H_i H_i_2 H_j H_j_2) as Hinv.
  replace (j - 1 + 1) with j by lia.
  assert (Hrefl :
      fp64_eq (Z_to_fp64 seed_shadow_now_2) (Z_to_fp64 seed_shadow_now_2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite; lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite; lia. }
  Exists seed_shadow_now_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_6 : sortrnd_entail_wit_6.
Proof.
  right. intros.
  bind_fact ( i < j ) as H_i.
  bind_fact ( retval >= 0 ) as H_retval.
  bind_fact ( learnt_cmp_result srt_db srt_activities pivot (Znth (j - 0) current_2 0) retval ) as H_learnt_cmp_result.
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current_2 size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  bind_fact ( Zlength current_2 = size_pre ) as H_Zlength.
  bind_fact ( 0 <= i ) as H_i_2.
  bind_fact ( i < size_pre ) as H_i_3.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j < size_pre ) as H_j_2.
  rewrite ?Z.sub_0_r in *.
  pose proof
    (sortrnd_swap_preserves_partition_inv__sortrnd
       _ _ _ _ _ _ _ _ _ H_sortrnd_right_scan_inv H_learnt_cmp_result H_retval H_i H_Zlength
       H_i_2 H_i_3 H_j H_j_2) as Hinv.
  sep_apply_l_atomic
    (PtrArray.full_to_seg array_pre size_pre
       (replace_Znth j (Znth i current_2 0)
          (replace_Znth i (Znth j current_2 0) current_2))).
  Exists seed_shadow_now_2
    (replace_Znth j (Znth i current_2 0)
       (replace_Znth i (Znth j current_2 0) current_2)).
  entailer_with ltac:(lia); try lia.
  rewrite Zlength_replace_Znth, Zlength_replace_Znth. exact H_Zlength.
Qed.

Lemma proof_of_sortrnd_entail_wit_7 : sortrnd_entail_wit_7.
Proof.
  right. intros.
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  unfold sortrnd_right_scan_inv in H_sortrnd_right_scan_inv.
  destruct H_sortrnd_right_scan_inv as [Hdom [Hctx [Hpiv [Hperm Hrest]]]].
  pose proof
    (learnt_sort_segment_domain_perm__sortrnd
       _ _ _ Hperm Hdom) as Hdom'.
  assert (Hfp : fp64_eq (Z_to_fp64 seed_shadow_now) (Z_to_fp64 seed_shadow_now)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  Exists seed_shadow_now.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_8 : sortrnd_entail_wit_8.
Proof.
  pre_process_default.
  Exists seed_shadow1 seed_value1 current_3.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_entail_wit_9 : sortrnd_entail_wit_9.
Proof.
  right. intros.
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow1_2) (Z_to_fp64 seed_shadow1_2)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  pose proof (Zlength_nonneg left_after) as Hnn.
  Exists seed_shadow1_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== sortrnd partial_solve wits (4 proofs) ===== *)
Lemma proof_of_sortrnd_partial_solve_wit_5_pure : sortrnd_partial_solve_wit_5_pure.
Proof.
  right. intros.
  bind_fact ( sortrnd_left_scan_inv srt_db srt_activities srt_origin current size_pre pivot (i - 1) j ) as
    H_sortrnd_left_scan_inv.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_left_scan_inv, sortrnd_partition_inv in H_sortrnd_left_scan_inv.
  destruct H_sortrnd_left_scan_inv as [Hdom [Hctx [Hpiv [Hperm Hrest]]]].
  pose proof
    (learnt_sort_segment_domain_Znth__sortrnd _ _ i
       (learnt_sort_segment_domain_perm__sortrnd
          _ _ _ Hperm Hdom) ltac:(lia)) as Hin.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_partial_solve_wit_7_pure : sortrnd_partial_solve_wit_7_pure.
Proof.
  right. intros.
  bind_fact ( sortrnd_right_scan_inv srt_db srt_activities srt_origin current size_pre pivot i (j + 1) ) as
    H_sortrnd_right_scan_inv.
  rewrite ?Z.sub_0_r in *.
  unfold sortrnd_right_scan_inv in H_sortrnd_right_scan_inv.
  destruct H_sortrnd_right_scan_inv as [Hdom [Hctx [Hpiv [Hperm Hrest]]]].
  pose proof
    (learnt_sort_segment_domain_Znth__sortrnd _ _ j
       (learnt_sort_segment_domain_perm__sortrnd
          _ _ _ Hperm Hdom) ltac:(lia)) as Hin.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_partial_solve_wit_13_pure : sortrnd_partial_solve_wit_13_pure.
Proof.
  right. intros.
  bind_fact ( sortrnd_split srt_db srt_origin current_2 left right size_pre i ) as H_sortrnd_split.
  unfold sortrnd_split in H_sortrnd_split.
  destruct H_sortrnd_split as [_ [_ [_ [_ [Hll [_ [Hdl _]]]]]]].
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_partial_solve_wit_15_pure : sortrnd_partial_solve_wit_15_pure.
Proof.
  right. intros.
  bind_fact ( sortrnd_split srt_db srt_origin current_2 left right size_pre i ) as H_sortrnd_split.
  unfold sortrnd_split in H_sortrnd_split.
  destruct H_sortrnd_split as [_ [Hlc [_ [_ [_ [Hlr [_ Hdr]]]]]]].
  assert (Hg : Zlength right =
               Zlength current - Zlength left_after) by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== sortrnd which_implies wits (2 proofs) ===== *)
Lemma proof_of_sortrnd_which_implies_wit_1 : sortrnd_which_implies_wit_1.
Proof.
  left. intros.
  bind_fact ( Permutation srt_origin current ) as H_Permutation.
  bind_fact ( Zlength current = size ) as H_Zlength.
  bind_fact ( learnt_sort_segment_domain srt_db current ) as H_learnt_sort_segment_domain.
  assert (Hsplit :
    current = sublist 0 i current ++ sublist i size current).
  { rewrite <- (sublist_split 0 size i current) by lia.
    rewrite sublist_self by lia. reflexivity. }
  assert (Hll : Zlength (sublist 0 i current) = i)
    by (apply Zlength_sublist0; lia).
  assert (Hlr : Zlength (sublist i size current) = size - i)
    by (apply Zlength_sublist; lia).
  assert (Hdoms :
    learnt_sort_segment_domain srt_db (sublist 0 i current) /\
    learnt_sort_segment_domain srt_db (sublist i size current)).
  { unfold learnt_sort_segment_domain in *.
    rewrite Hsplit in H_learnt_sort_segment_domain.
    apply Forall_app in H_learnt_sort_segment_domain. exact H_learnt_sort_segment_domain. }
  destruct Hdoms as [Hdl Hdr].
  assert (Hsp : sortrnd_split srt_db srt_origin current
    (sublist 0 i current) (sublist i size current) size i).
  { unfold sortrnd_split.
    split; [exact H_Permutation |].
    split; [exact H_Zlength |].
    split; [lia |].
    split; [exact Hsplit |].
    split; [exact Hll |].
    split; [exact Hlr |].
    split; assumption. }
  sep_apply_l_atomic
    (PtrArray.seg_split_to_seg array 0 i size current ltac:(lia)).
  replace (i - 0) with i by lia.
  replace (size - 0) with size by lia.
  Exists (sublist 0 i current) (sublist i size current).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_which_implies_wit_2 : sortrnd_which_implies_wit_2.
Proof.
  right. intros.
  rewrite PtrArray.seg_0_shift.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== sortrnd return wits (2 proofs) ===== *)
Lemma proof_of_sortrnd_return_wit_1 : sortrnd_return_wit_1.
Proof.
  right. intros.
  assert (Hrefl : fp64_eq (Z_to_fp64 seed_shadow) (Z_to_fp64 seed_shadow)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  Exists seed_shadow.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_return_wit_2 : sortrnd_return_wit_2.
Proof.
  right. intros.
  assert (Hrefl : fp64_eq (Z_to_fp64 shadow_after_right) (Z_to_fp64 shadow_after_right)).
  { unfold fp64_eq, fp64_compare.
    rewrite Binary.Bcompare_correct.
    - rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia.
    - apply MSatFloatFacts.Z_to_fp64_i32_finite. lia. }
  Exists shadow_after_right.
  msat_manual_entailer_with ltac:(lia).
Qed.
