From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_support_lib.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ===== group: solver_propagate ===== *)
Lemma stats_propagate_scan_refold__propagate :
  forall s prop st,
    (&(s # "solver_t" ->ₛ "stats" .ₛ "propagations") # UInt64 |-> prop **
     &(s # "solver_t" ->ₛ "stats" .ₛ "inspects")
       # UInt64 |-> stats_inspects st) |--
    stats_propagate_scan &(s # "solver_t" ->ₛ "stats")
      prop (stats_inspects st).
Proof.
  intros. unfold stats_propagate_scan, Znth. cbn. csimpl.
  cancel.
Qed.

Lemma z_le_add_one__propagate : forall x : Z, x <= x + 1.
Proof. intros. lia. Qed.

Lemma solver_propagate_frame_overlay__propagate :
  forall s M core qtail reason_words reason_of prob learnt binary_lits
    wm stats,
    map fst prob = map fst (ms_prob M) ->
    map fst learnt = map fst (ms_learnt M) ->
    stats = ms_stats M ->
    solver_propagate_frame s
      (msolver_propagation_overlay M core qtail reason_words reason_of
        prob learnt binary_lits wm stats) =
    solver_propagate_frame s M.
Proof.
  intros.
  unfold solver_propagate_frame, solver_fp_rep,
    msolver_propagation_overlay, msolver_propagation_update.
  cbn.
  rewrite H, H0, H1. reflexivity.
Qed.

Lemma solver_propagate_frame_db_wmap_update__propagate :
  forall s M prob learnt wm,
    map fst prob = map fst (ms_prob M) ->
    map fst learnt = map fst (ms_learnt M) ->
    solver_propagate_frame s
      (msolver_propagation_db_wmap_update M prob learnt wm) =
    solver_propagate_frame s M.
Proof.
  intros. unfold msolver_propagation_db_wmap_update.
  apply solver_propagate_frame_overlay__propagate;
    [ assumption | assumption | reflexivity ].
Qed.

Lemma solver_propagate_frame_enqueue_success__propagate :
  forall (s : Z) (Ms : msolver) (l reason_word : Z)
    (reason_clause : clause),
    solver_propagate_frame s
      (msolver_propagation_enqueue_success Ms l reason_word reason_clause) =
    solver_propagate_frame s Ms.
Proof.
  intros. unfold msolver_propagation_enqueue_success.
  destruct (Znth (lit_var_c l) (mt_assigns (ms_core Ms)) 0 =? 0)%Z.
  - apply solver_propagate_frame_overlay__propagate;
      reflexivity.
  - reflexivity.
Qed.

Lemma solver_propagate_frame_db_enqueue__propagate :
  forall (s : Z) (Ms : msolver) (l reason_word : Z)
    (reason_clause : clause) prob learnt wm,
    map fst prob = map fst (ms_prob Ms) ->
    map fst learnt = map fst (ms_learnt Ms) ->
    solver_propagate_frame s
      (msolver_propagation_enqueue_success
        (msolver_propagation_db_wmap_update Ms prob learnt wm)
        l reason_word reason_clause) =
    solver_propagate_frame s Ms.
Proof.
  intros.
  rewrite solver_propagate_frame_enqueue_success__propagate.
  apply solver_propagate_frame_db_wmap_update__propagate;
    assumption.
Qed.

Lemma solver_shape_scan_finish__propagate :
  forall M inspect_delta,
    solver_shape M ->
    solver_shape (msolver_propagation_scan_finish M inspect_delta).
Proof.
  intros M inspect_delta Hshape.
  unfold solver_shape, msolver_propagation_scan_finish,
    msolver_propagation_overlay, msolver_propagation_update in *.
  cbn in *. unfold stats_set_inspects.
  repeat split; try tauto.
  rewrite Zlength_replace_Znth. tauto.
Qed.

Lemma msolver_inv_ctx_scan_finish__propagate :
  forall n F A_arr K M inspect_delta,
    msolver_inv_ctx n F A_arr K M ->
    msolver_inv_ctx n F A_arr K
      (msolver_propagation_scan_finish M inspect_delta).
Proof.
  intros n F A_arr K M inspect_delta Hweak.
  destruct K as [A_inst|A_proc]; cbn in Hweak |- *; destruct Hweak;
    constructor; cbn [msolver_propagation_scan_finish
      msolver_propagation_overlay msolver_propagation_update] in *; try assumption;
    apply solver_shape_scan_finish__propagate; assumption.
Qed.

Lemma solver_propagation_scan_finish_loop__propagate :
  forall n F A_arr K entry M p confl retained inspect_delta,
    propagation_caller_frame entry M ->
    solver_propagation_scan_semantics
      n F A_arr K M p confl retained nil ->
    solver_propagation_loop_inv n F A_arr K entry
      (msolver_propagation_scan_finish M inspect_delta) confl.
Proof.
  intros n F A_arr K entry M p confl retained inspect_delta
    Hcaller Hscan.
  unfold solver_propagation_scan_semantics in Hscan.
  destruct Hscan as
    [[Hconfl [Hweak [Hlevel [Hheap_ready [Hcovers
      [Hreasonless [Hfocus [Hp_wf [Hprocessed [Hfrontier Hcarrier]]]]]]]]]]
    |[Hconfl [Hrest [Hcancel [C [Hcert Hdenotes]]]]]].
  - assert (Hfrontier_full :
      minisat_watch_frontier n (msolver_db M)
        (mt_assigns (ms_core M)) (mt_trail (ms_core M))
        (mt_qhead (ms_core M))).
    { destruct K as [A_inst | A_proc];
        unfold solver_propagation_weak in Hweak; cbn in Hweak;
        destruct Hweak as [_ Hweak].
      - eapply minisat_watch_frontier_close_scan;
          [exact (msw_db_wf Hweak) | exact Hp_wf | exact Hfrontier
          | exact Hcarrier].
      - eapply minisat_watch_frontier_close_scan;
          [exact (msa_db_wf Hweak) | exact Hp_wf | exact Hfrontier
          | exact Hcarrier]. }
    unfold solver_propagation_loop_inv.
    split.
    + change (propagation_caller_frame entry M). exact Hcaller.
    + left. split; [exact Hconfl|].
      unfold solver_propagation_inv.
      destruct K as [A_inst | A_proc];
        unfold solver_propagation_weak in Hweak; cbn in Hweak;
        destruct Hweak as [Hpending Hweak]; split.
      * change (ms_capacity_root_propagation_pending M = 0).
        exact Hpending.
      * constructor.
        -- exact (msolver_inv_ctx_scan_finish__propagate n F A_arr
             (PropagationStable A_inst) M inspect_delta Hweak).
        -- change (prop_level (ms_core M)). exact Hlevel.
        -- change (minisat_watch_frontier n (msolver_db M)
             (mt_assigns (ms_core M)) (mt_trail (ms_core M))
             (mt_qhead (ms_core M))). exact Hfrontier_full.
        -- change (propagation_heap_ready n M). exact Hheap_ready.
        -- change (current_reasonless_earliest n M). exact Hreasonless.
      * change (ms_capacity_root_propagation_pending M = 0).
        exact Hpending.
      * constructor.
        -- exact (msolver_inv_ctx_scan_finish__propagate n F A_arr
             (PropagationAssuming A_proc) M inspect_delta Hweak).
        -- change (prop_level (ms_core M)). exact Hlevel.
        -- change (minisat_watch_frontier n (msolver_db M)
             (mt_assigns (ms_core M)) (mt_trail (ms_core M))
             (mt_qhead (ms_core M))). exact Hfrontier_full.
        -- change (propagation_heap_ready n M). exact Hheap_ready.
        -- change (current_reasonless_earliest n M). exact Hreasonless.
  - assert (Hcancel_finish : propagation_cancel_ready n F A_arr K
      (msolver_propagation_scan_finish M inspect_delta) p).
    { unfold propagation_cancel_ready in Hcancel |- *.
      destruct Hcancel as [Hweak [Hlevel [Hp_wf [Hprocessed
        [Hfocus [Hfrontier [Hheap_wf [Hcovers Hreasonless]]]]]]]].
      split.
      - destruct Hweak as [Hpending Hweak]. split.
        + exact Hpending.
        + exact (msolver_inv_ctx_scan_finish__propagate n F A_arr K M
            inspect_delta Hweak).
      - split.
        + change (prop_level (ms_core M)). exact Hlevel.
        + split; [exact Hp_wf|].
          split.
          * change (processed (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) p).
            exact Hprocessed.
          * split.
            -- change (level_of (msolver_view n M) (lit_var_c p) =
                Some (Zlength (mt_lim (ms_core M)))). exact Hfocus.
            -- split.
              ++ change (minisat_watch_frontier_except n (msolver_db M)
                   (mt_assigns (ms_core M)) (mt_trail (ms_core M))
                   (mt_qhead (ms_core M)) (lit_denote p)). exact Hfrontier.
              ++ split.
                ** change (heap_wf n (msolver_heap M)). exact Hheap_wf.
                ** split.
                   --- change (heap_covers n (msolver_heap M)
                       (mt_assigns (ms_core M)) (mt_trail (ms_core M))
                       (mt_qhead (ms_core M))). exact Hcovers.
                   --- change (current_reasonless_earliest n M).
                       exact Hreasonless. }
    assert (Hcert_finish : propagation_conflict_cert n F
      (msolver_propagation_scan_finish M inspect_delta) C).
    { change (propagation_conflict_cert n F M C). exact Hcert. }
    assert (Hdenotes_finish : conflict_ptr_denotes
      (msolver_propagation_scan_finish M inspect_delta) confl C).
    { change (conflict_ptr_denotes M confl C). exact Hdenotes. }
    unfold solver_propagation_loop_inv.
    split.
    + change (propagation_caller_frame entry M). exact Hcaller.
    + right. split; [exact Hconfl|].
      exists p, C. split; [exact Hcancel_finish|].
      split; [exact Hcert_finish|exact Hdenotes_finish].
Qed.

(** Put watch list [p] back with new contents: the framework's [missing_i_merge_to_full]. *)
Lemma missing_i_merge_to_wlists_rep :
  forall wl n p wm words,
    0 <= p < 2 * n ->
    Vecp.rep (Vecp.slot wl p) words ** VecpArray.missing_i wl p 0 (2 * n) wm
    |-- wlists_rep wl n (replace_Znth p words wm).
Proof.
  intros wl n p wm words Hp.
  prop_apply_p (VecpArray.missing_i_Zlength wl p 0 (2 * n) wm). Intros.
  change (Vecp.rep (Vecp.slot wl p) words) with (VecpArray.vec_store wl p words).
  sep_apply (VecpArray.missing_i_merge_to_full wl p (2 * n) words wm Hp).
  unfold wlists_rep.
  rewrite Zlength_replace_Znth.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [reflexivity | lia] ..].
Qed.

(** The table as [VecpArray.full] of 2n vectors refolds to [wlists_rep]. *)
Lemma full_to_wlists_rep :
  forall wl n wm,
    VecpArray.full wl (2 * n) wm |-- wlists_rep wl n wm.
Proof.
  intros wl n wm.
  prop_apply_p (VecpArray.full_Zlength wl (2 * n) wm). Intros.
  unfold wlists_rep.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [reflexivity | lia] ..].
Qed.

Lemma solver_propagate_frame_scan_finish__propagate :
  forall s M inspect_delta,
    solver_shape M ->
    solver_propagate_frame s M |--
    solver_propagate_frame s
      (msolver_propagation_scan_finish M inspect_delta).
Proof.
  intros s M inspect_delta Hshape.
  unfold solver_shape in Hshape.
  assert (Hstats : stats_propagate_frame &(s # "solver_t" ->ₛ "stats")
      (ms_stats (msolver_propagation_scan_finish M inspect_delta)) =
      stats_propagate_frame &(s # "solver_t" ->ₛ "stats") (ms_stats M)).
  { change (stats_propagate_frame &(s # "solver_t" ->ₛ "stats")
      (stats_set_inspects (MiniSatTarget.lo64 (stats_inspects (ms_stats M) + inspect_delta)) (ms_stats M)) =
      stats_propagate_frame &(s # "solver_t" ->ₛ "stats") (ms_stats M)).
    unfold stats_propagate_frame, stats_set_inspects, stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals.
    rewrite Zlength_replace_Znth.
    rewrite !Znth_replace_Znth_Diff by lia.
    reflexivity. }
  assert (Heq : solver_propagate_frame s
      (msolver_propagation_scan_finish M inspect_delta) =
      solver_propagate_frame s M).
  { unfold solver_propagate_frame. rewrite Hstats. reflexivity. }
  rewrite Heq. msat_entailer_with lia.
Qed.

Lemma scan_finish_stats2__propagate :
  forall M inspect_delta,
    solver_shape M ->
    stats_propagations (ms_stats (msolver_propagation_scan_finish M inspect_delta)) =
    stats_propagations (ms_stats M).
Proof.
  intros M inspect_delta Hshape.
  unfold solver_shape in Hshape.
  change (stats_propagations (stats_set_inspects (MiniSatTarget.lo64 (stats_inspects (ms_stats M) + inspect_delta))
  (ms_stats M)) = stats_propagations (ms_stats M)).
  apply Znth_replace_Znth_Diff; lia.
Qed.

Lemma scan_finish_stats3__propagate :
  forall M inspect_delta,
    solver_shape M -> 0 <= inspect_delta < 2 ^ 64 ->
    stats_inspects (ms_stats (msolver_propagation_scan_finish M inspect_delta)) =
    unsigned_last_nbits
      (stats_inspects (ms_stats M) + unsigned_last_nbits inspect_delta 64) 64.
Proof.
  intros M inspect_delta Hshape Hdelta.
  unfold solver_shape in Hshape.
  change (stats_inspects (stats_set_inspects (MiniSatTarget.lo64 (stats_inspects (ms_stats M) + inspect_delta))
  (ms_stats M)) =
    unsigned_last_nbits
      (stats_inspects (ms_stats M) + unsigned_last_nbits inspect_delta 64) 64).
  unfold stats_inspects, stats_set_inspects.
  rewrite Znth_replace_Znth_Same by lia.
  assert (Hinner : unsigned_last_nbits inspect_delta 64 = inspect_delta).
  { apply unsigned_last_nbits_eq. exact Hdelta. }
  rewrite Hinner.
  unfold MiniSatTarget.lo64, MiniSatTarget.two64, unsigned_last_nbits.
  reflexivity.
Qed.

Lemma solver_binary_rep_scan_finish__propagate :
  forall M inspect_delta,
    solver_binary_rep (msolver_propagation_scan_finish M inspect_delta) =
    solver_binary_rep M.
Proof. reflexivity. Qed.

Lemma propagation_scan_semantics_qtail_size__propagate :
  forall n F A_arr K M p confl retained rest,
    solver_propagation_scan_semantics n F A_arr K M p confl retained rest ->
    ms_qtail M <= ms_size M.
Proof.
  intros n F A_arr K M p confl retained rest Hscan.
  unfold solver_propagation_scan_semantics in Hscan.
  destruct Hscan as
    [[_ [Hweak _]] | [_ [_ [Hcancel _]]]].
  - destruct K as [A_inst | A_proc];
      unfold solver_propagation_weak in Hweak; cbn in Hweak;
      destruct Hweak as [_ Hinv].
    + pose proof (mtw_trail_bound (msw_trail_wf Hinv)) as Hbound.
      pose proof (msw_size Hinv) as Hsize.
      pose proof (msw_shape Hinv) as Hshape.
      unfold solver_shape in Hshape. lia.
    + pose proof (mtw_trail_bound (msa_trail_wf Hinv)) as Hbound.
      pose proof (msa_size Hinv) as Hsize.
      pose proof (msa_shape Hinv) as Hshape.
      unfold solver_shape in Hshape. lia.
  - unfold propagation_cancel_ready in Hcancel.
    destruct Hcancel as [Hweak _].
    destruct K as [A_inst | A_proc];
      unfold solver_propagation_weak in Hweak; cbn in Hweak;
      destruct Hweak as [_ Hinv].
    + pose proof (mtw_trail_bound (msw_trail_wf Hinv)) as Hbound.
      pose proof (msw_size Hinv) as Hsize.
      pose proof (msw_shape Hinv) as Hshape.
      unfold solver_shape in Hshape. lia.
    + pose proof (mtw_trail_bound (msa_trail_wf Hinv)) as Hbound.
      pose proof (msa_size Hinv) as Hsize.
      pose proof (msa_shape Hinv) as Hshape.
      unfold solver_shape in Hshape. lia.
Qed.

Lemma solver_propagation_open_refold__propagate :
  forall s M asg rsn lvl trl wl,
    solver_shape M ->
    (&(s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
     &(s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
     &(s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
     &(s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
     &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
     &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     &(s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
     &(s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
     &(s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
     CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
     solver_char_tail asg (ms_size M) (ms_cap M) **
     PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
     solver_ptr_tail rsn (ms_size M) (ms_cap M) **
     IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
     solver_int_tail lvl (ms_size M) (ms_cap M) **
     IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
     solver_int_tail trl (ms_qtail M) (ms_cap M) **
     Veci.rep &(s # "solver_t" ->ₛ "trail_lim")
       (mt_lim (ms_core M)) **
     wlists_rep wl (ms_size M) (ms_wm M) **
     clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
     solver_binary_rep M **
     &(s # "solver_t" ->ₛ "stats" .ₛ "propagations")
       # UInt64 |-> stats_propagations (ms_stats M) **
     &(s # "solver_t" ->ₛ "stats" .ₛ "inspects")
       # UInt64 |-> stats_inspects (ms_stats M) **
     solver_propagate_frame s M)
    |-- solver_rep_assigns_levels_at s M asg lvl wl.
Proof.
  intros s M asg rsn lvl trl wl Hshape.
  unfold solver_binary_rep, solver_propagate_frame, stats_propagate_frame.
  Intros act opos tgs.
  (* Binders first, leaves after: [Intros]/[Exists]
     are whole-goal traversals and are cheaper before the leaves open. *)
  unfold solver_rep_assigns_levels_at.
  Exists act opos rsn trl tgs.
  unfold solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_trail_array_rep, stats_rep.
  set_String_name.
  split_pure_spatial;
    [ Intros; msat_cancel_sound; cancel
    | (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]) ].
  all: cbn; csimpl; msat_entailer_with lia.
Qed.

Lemma learnt_sort_rep_focus_one__clause_cmp : forall db activities x,
  In x (db_words db) ->
  learnt_sort_rep db activities |--
  EX xlits : list Z, EX xa : fp32,
    learnt_clause_snapshot_raw x xlits xa **
    learnt_sort_alias_remainder db activities x xlits xa.
Proof.
  intros db. induction db as [|[p co] db IH]; intros activities x Hin.
  - unfold db_words in Hin. simpl in Hin. contradiction.
  - destruct activities as [|a activities].
    + cbn [learnt_sort_rep]. apply coq_prop_False_left. tauto.
    + unfold db_words in Hin. simpl in Hin.
      destruct Hin as [Hx | Hin].
      * subst p. cbn [learnt_sort_rep].
        Intros_p Hhead.
        destruct Hhead as [Htag [Hpos [Hmod Hnonneg]]].
        Exists (co_lits co) a.
        unfold learnt_clause_snapshot_raw, learnt_sort_alias_remainder.
        Exists co (@nil (Z * clause_obj)) db (@nil fp32) activities.
        cbn [learnt_sort_rep].
        split_pure_spatial.
        -- cancel.
           cancel.
        -- split_pures; dump_pre_spatial.
           ++ repeat split; auto.
           ++ repeat split; auto.
      * cbn [learnt_sort_rep]. Intros_p Hhead.
        sep_apply (IH activities x Hin).
        Intros xlits xa.
        unfold learnt_sort_alias_remainder at 1.
        Intros co' pre post apre apost.
        destruct H as
          [Hdb [Hactivities [Hlen [Hlits [Htag Hnonneg]]]]].
        Exists xlits xa.
        unfold learnt_sort_alias_remainder.
        Exists co' ((p, co) :: pre) post (a :: apre) apost.
        cbn [learnt_sort_rep].
        split_pure_spatial.
        -- cancel (learnt_sort_rep pre apre).
           cancel.
        -- split_pures; dump_pre_spatial.
           ++ rewrite Hdb, Hactivities, !Zlength_cons, Hlen.
              repeat split; auto.
           ++ exact Hhead.
Qed.

Lemma learnt_sort_rep_focus_two__clause_cmp :
  forall db activities x y,
  In x (db_words db) ->
  In y (db_words db) ->
  x <> y ->
  learnt_sort_rep db activities |--
  EX xlits ylits : list Z, EX xa ya : fp32,
    learnt_clause_snapshot_raw x xlits xa **
    learnt_clause_snapshot_raw y ylits ya **
    learnt_sort_two_remainder db activities x xlits xa y ylits ya.
Proof.
  intros db activities x y Hx Hy Hxy.
  sep_apply (learnt_sort_rep_focus_one__clause_cmp db activities x Hx).
  Intros xlits xa.
  unfold learnt_sort_alias_remainder at 1.
  Intros cox pre post apre apost.
  destruct H as
    [Hdb [Hactivities [Hprelen [Hxlits [Hxtag Hxnonneg]]]]].
  unfold db_words in Hy. rewrite Hdb in Hy.
  rewrite map_app in Hy. simpl in Hy. rewrite in_app_iff in Hy.
  destruct Hy as [Hypre | [Hyx | Hypost]].
  - change (In y (db_words pre)) in Hypre.
    sep_apply
      (learnt_sort_rep_focus_one__clause_cmp pre apre y Hypre).
    Intros ylits ya.
    unfold learnt_sort_alias_remainder at 1.
    Intros coy pre' mid aprep amid.
    destruct H as
      [Hpre [Hapre [Hprelen' [Hylits [Hytag Hynonneg]]]]].
    Exists xlits ylits xa ya.
    unfold learnt_sort_two_remainder.
    Right.
    Exists cox coy pre' mid post aprep amid apost.
    split_pure_spatial.
    + cancel (learnt_sort_rep pre' aprep).
      cancel.
    + split_pures; dump_pre_spatial.
      rewrite Hpre, Hapre, !Zlength_app, !Zlength_cons in Hprelen.
      rewrite Hdb, Hactivities, Hpre, Hapre, <- !app_assoc.
      repeat split; auto.
      lia.
  - contradiction.
  - change (In y (db_words post)) in Hypost.
    sep_apply
      (learnt_sort_rep_focus_one__clause_cmp post apost y Hypost).
    Intros ylits ya.
    unfold learnt_sort_alias_remainder at 1.
    Intros coy mid post' amid apost'.
    destruct H as
      [Hpost [Hapost [Hmidlen [Hylits [Hytag Hynonneg]]]]].
    Exists xlits ylits xa ya.
    unfold learnt_sort_two_remainder.
    Left.
    Exists cox coy pre mid post' apre amid apost'.
    split_pure_spatial.
    + cancel (learnt_sort_rep mid amid).
      cancel.
    + split_pures; dump_pre_spatial.
      rewrite Hdb, Hactivities, Hpost, Hapost.
      repeat split; auto.
Qed.

Lemma clause_hdr_word_quot2__clause_cmp : forall learnt size,
  0 <= size -> clause_hdr_word learnt size ÷ 2 = size.
Proof.
  intros learnt size Hsize.
  rewrite Z.quot_div_nonneg.
  - apply clause_hdr_word_div2. exact Hsize.
  - apply clause_hdr_word_nonneg. exact Hsize.
  - lia.
Qed.

Lemma learnt_cmp_result_lt_two_yx_headers__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  0 < x -> x mod 2 = 0 -> msat_fp32_nonnegative xa ->
  0 < y -> y mod 2 = 0 -> msat_fp32_nonnegative ya ->
  2 < Zlength xlits ->
  (Zlength ylits = 2 \/ fp32_lt xa ya) ->
  clause_hdr_addr y # Int |-> clause_hdr_word true (Zlength ylits) **
  clause_hdr_addr x # Int |-> clause_hdr_word true (Zlength xlits) **
  clause_act_addr x (Zlength xlits) # Float |-> xa **
  IntArray.seg (clause_lits_addr x) 0 (Zlength xlits) xlits **
  clause_act_addr y (Zlength ylits) # Float |-> ya **
  IntArray.seg (clause_lits_addr y) 0 (Zlength ylits) ylits **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_result db activities x y (-1) ” &&
  learnt_sort_rep db activities.
Proof. msat_learnt_cmp_lt_two_join. Qed.

Lemma learnt_cmp_result_lt_two_activity_first__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  0 < x -> x mod 2 = 0 -> msat_fp32_nonnegative xa ->
  0 < y -> y mod 2 = 0 -> msat_fp32_nonnegative ya ->
  2 < Zlength xlits ->
  (Zlength ylits = 2 \/ fp32_lt xa ya) ->
  clause_act_addr y (Zlength ylits) # Float |-> ya **
  clause_act_addr x (Zlength xlits) # Float |-> xa **
  clause_hdr_addr y # Int |-> clause_hdr_word true (Zlength ylits) **
  clause_hdr_addr x # Int |-> clause_hdr_word true (Zlength xlits) **
  IntArray.seg (clause_lits_addr x) 0 (Zlength xlits) xlits **
  IntArray.seg (clause_lits_addr y) 0 (Zlength ylits) ylits **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_result db activities x y (-1) ” &&
  learnt_sort_rep db activities.
Proof. msat_learnt_cmp_lt_two_join. Qed.

Lemma learnt_cmp_result_stop_two_activity_first__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  0 < x -> x mod 2 = 0 -> msat_fp32_nonnegative xa ->
  0 < y -> y mod 2 = 0 -> msat_fp32_nonnegative ya ->
  (Zlength xlits <= 2 \/
   (Zlength ylits <> 2 /\ fp32_ge xa ya)) ->
  clause_act_addr y (Zlength ylits) # Float |-> ya **
  clause_act_addr x (Zlength xlits) # Float |-> xa **
  clause_hdr_addr y # Int |-> clause_hdr_word true (Zlength ylits) **
  clause_hdr_addr x # Int |-> clause_hdr_word true (Zlength xlits) **
  IntArray.seg (clause_lits_addr x) 0 (Zlength xlits) xlits **
  IntArray.seg (clause_lits_addr y) 0 (Zlength ylits) ylits **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_result db activities x y 1 ” &&
  learnt_sort_rep db activities.
Proof. msat_learnt_cmp_stop_two_join. Qed.

Lemma learnt_cmp_result_stop_alias_header_first__clause_cmp :
  forall db activities x xlits xa,
  0 < x -> x mod 2 = 0 -> msat_fp32_nonnegative xa ->
  clause_hdr_addr x # Int |-> clause_hdr_word true (Zlength xlits) **
  clause_act_addr x (Zlength xlits) # Float |-> xa **
  IntArray.seg (clause_lits_addr x) 0 (Zlength xlits) xlits **
  learnt_sort_alias_remainder db activities x xlits xa |--
  “ learnt_cmp_result db activities x x 1 ” &&
  learnt_sort_rep db activities.
Proof. msat_learnt_cmp_stop_alias_join. Qed.

Lemma learnt_cmp_result_stop_two_xy_headers__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  0 < x -> x mod 2 = 0 -> msat_fp32_nonnegative xa ->
  0 < y -> y mod 2 = 0 -> msat_fp32_nonnegative ya ->
  (Zlength xlits <= 2 \/
   (Zlength ylits <> 2 /\ fp32_ge xa ya)) ->
  clause_hdr_addr x # Int |-> clause_hdr_word true (Zlength xlits) **
  clause_act_addr x (Zlength xlits) # Float |-> xa **
  IntArray.seg (clause_lits_addr x) 0 (Zlength xlits) xlits **
  clause_hdr_addr y # Int |-> clause_hdr_word true (Zlength ylits) **
  clause_act_addr y (Zlength ylits) # Float |-> ya **
  IntArray.seg (clause_lits_addr y) 0 (Zlength ylits) ylits **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_result db activities x y 1 ” &&
  learnt_sort_rep db activities.
Proof. msat_learnt_cmp_stop_two_join. Qed.

Lemma rem_two_mod_two__clause_cmp : forall x : Z,
  Z.rem x 2 = 0 -> x mod 2 = 0.
Proof.
  intros x H.
  apply Z.mod_divide; [lia |].
  apply Z.rem_divide; [lia | exact H].
Qed.

Lemma reason_owner_valid__propagate_dbu :
  forall n M current co v,
    db_wf n (msolver_db M) ->
    mtrail_wf n (ms_core M) ->
    stable_view (msolver_view n M) ->
    reasons_match n (ms_core M) (msolver_db M)
      (ms_reason_words M) (ms_reason_of M) ->
    In (current, co) (msolver_db M) ->
    0 <= v < n ->
    Znth v (ms_reason_words M) 0 = current ->
    exists b,
      mt_pv (ms_core M) v = Some b /\
      reason_valid (msolver_view n M) v (denote_obj co).
Proof.
  intros n M current co v Hdbwf Htrail Hstable Hreasons Hin Hv Heq.
  pose proof (db_wf_ptr_pos n (msolver_db M) current co Hdbwf Hin) as Hpos.
  pose proof (db_wf_even n (msolver_db M) current co Hdbwf Hin) as Heven.
  assert (Hreal : is_tag current = false).
  { apply even_not_tag. exact Heven. }
  specialize (Hreasons v Hv).
  unfold reason_word_ok in Hreasons. rewrite Heq in Hreasons.
  assert (Hnz : (current =? 0)%Z = false) by (apply Z.eqb_neq; lia).
  rewrite Hnz, Hreal in Hreasons.
  destruct Hreasons as [Hvassigned [co' [Hlookup Hr]]].
  assert (Hcoeq : co' = co).
  { unfold db_lookup in Hlookup.
    eapply db_wf_lookup_unique; [exact Hdbwf|exact Hlookup|exact Hin]. }
  subst co'.
  assert (Hpv : exists b, mt_pv (ms_core M) v = Some b).
  { pose proof (Forall_Znth_elim Z lbool_cell
      (mt_assigns (ms_core M)) 0 v (mtw_cells Htrail)
      ltac:(rewrite (mtw_assigns_len Htrail); exact Hv)) as Hcell.
    unfold lbool_cell in Hcell.
    destruct Hcell as [Hcell|[Hcell|Hcell]].
    - exists false. rewrite mt_pv_nonneg by lia. rewrite Hcell. reflexivity.
    - contradiction.
    - exists true. rewrite mt_pv_nonneg by lia. rewrite Hcell. reflexivity. }
  destruct Hpv as [b Hpv].
  assert (Htp : exists pos, trail_pos (ms_core M) v = Some pos).
  { destruct (trail_pos (ms_core M) v) as [pos|] eqn:Htp.
    - exists pos. reflexivity.
    - exfalso. apply trail_pos_none_iff in Htp. apply Htp.
      apply (proj1 (mtw_assigned_iff Htrail v Hv)). exact Hvassigned. }
  destruct Htp as [pos Htp].
  unfold stable_view in Hstable. destruct Hstable as [Hground _].
  specialize (Hground v b Hpv).
  destruct Hground as [d [rx [_ [_ [Hnone|[C [HC Hvalid]]]]]]].
  - unfold msolver_view, view_of in Hnone; cbn in Hnone.
    rewrite Htp, Hr in Hnone. discriminate.
  - unfold msolver_view, view_of in HC; cbn in HC.
    rewrite Htp, Hr in HC. inversion HC; subst C.
    exists b. split; [exact Hpv|exact Hvalid].
Qed.

Lemma no_live_reason_owner_head_false_core : forall n M p co,
  db_wf n (msolver_db M) ->
  mtrail_wf n (ms_core M) ->
  stable_view (msolver_view n M) ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  reason_head_ok M ->
  n = ms_size M ->
  In (p, co) (msolver_db M) ->
  lit_false (mt_assigns (ms_core M)) (co_watch0 co) ->
  forall v, 0 <= v < n -> Znth v (ms_reason_words M) 0 <> p.
Proof.
  intros n M p co Hdbwf Htrailwf Hstable Hreasons Hheadok Hsize
    Hin Hheadfalse v Hv Heq.
  pose proof (db_wf_obj n (msolver_db M) p co Hdbwf Hin) as Hobj.
  pose proof (db_wf_ptr_pos n (msolver_db M) p co Hdbwf Hin) as Hptrpos.
  pose proof (db_wf_even n (msolver_db M) p co Hdbwf Hin) as Hptreven.
  assert (Htag : is_tag p = false).
  { apply even_not_tag. exact Hptreven. }
  destruct (reason_owner_valid__propagate_dbu n M p co v
    Hdbwf Htrailwf Hstable Hreasons Hin Hv Heq) as [b [Hpv Hvalid]].
  assert (Hheadvar : lit_var_c (co_watch0 co) = v).
  { apply (Hheadok v co).
    - rewrite <- Hsize. exact Hv.
    - rewrite Heq. exact Htag.
    - rewrite Heq. lia.
    - rewrite Heq. exact Hin. }
  destruct Hvalid as [b' [d' [rx'
    [Hpv' [_ [_ [Hsat _]]]]]]].
  change (mt_pv (ms_core M) v = Some b') in Hpv'.
  rewrite Hpv in Hpv'. inversion Hpv'; subst b'.
  assert (Hwatchin :
      In (lit_denote (co_watch0 co)) (denote_obj co)).
  { unfold denote_obj. apply lits_denote_in.
    apply obj_wf_watch0_in with (n := n). exact Hobj. }
  assert (Hlit_eq :
      satisfying_literal v b = lit_denote (co_watch0 co)).
  { apply (NoDup_map_var_injective (denote_obj co)).
    - apply obj_wf_nodup_vars with (n := n). exact Hobj.
    - exact Hsat.
    - exact Hwatchin.
    - rewrite satisfying_literal_var, lit_var_c_denote, Hheadvar.
      reflexivity. }
  pose proof (eval_satisfying_literal_true
    (mt_pv (ms_core M)) v b Hpv) as Htrue.
  rewrite Hlit_eq in Htrue.
  assert (Hheadnonneg : 0 <= co_watch0 co).
  { pose proof (obj_wf_watch0 n co Hobj). destruct H. lia. }
  pose proof (proj1 (lit_false_iff
    (mt_assigns (ms_core M)) (co_watch0 co) Hheadnonneg)
    Hheadfalse) as Hfalse.
  unfold eval_partial_literal in Htrue, Hfalse.
  rewrite lit_var_c_denote in Htrue, Hfalse.
  rewrite mt_pv_nonneg in Htrue by
    (apply lit_var_c_nonneg with (n := n);
     apply obj_wf_watch0; exact Hobj).
  unfold assigns_pv, assigns_val in Hfalse.
  congruence.
Qed.

Lemma ctx_no_live_reason_owner_head_false__propagate_dbu :
  forall n F A_arr K M p co,
    msolver_inv_ctx n F A_arr K M ->
    In (p, co) (msolver_db M) ->
    lit_false (mt_assigns (ms_core M)) (co_watch0 co) ->
    forall v, 0 <= v < n -> Znth v (ms_reason_words M) 0 <> p.
Proof.
  intros n F A_arr K M p co Hweak Hin Hheadfalse.
  destruct K as [A_inst|A_proc]; cbn in Hweak; destruct Hweak;
    apply (no_live_reason_owner_head_false_core n M p co); assumption.
Qed.

Lemma ctx_db_pair_lits_no_owner__propagate_dbu :
  forall n F A_arr K M p old_lits new_lits prob' learnt',
    msolver_inv_ctx n F A_arr K M ->
    db_pair_lits_update (ms_prob M) (ms_learnt M)
      p old_lits new_lits prob' learnt' ->
    Permutation new_lits old_lits ->
    (forall l,
      Permutation (expected_watchers (msolver_db M) l)
        (expected_watchers (prob' ++ learnt') l)) ->
    (forall v, 0 <= v < n -> Znth v (ms_reason_words M) 0 <> p) ->
    msolver_inv_ctx n F A_arr K
      (msolver_propagation_db_wmap_update
        M prob' learnt' (ms_wm M)).
Proof.
  intros n F A_arr K; destruct K as [A_x|A_x]; cbn [msolver_inv_ctx];
    revert n F A_arr A_x.
  - msat_inv_db_pair_lits_no_owner msw_db_wf msw_db_matches msw_db_implied
      msw_db_complete msw_prob_db msw_learnt_db msw_binary_out msw_reasons_mem
      msw_reason_head msw_size msw_wmap_exact.
  - msat_inv_db_pair_lits_no_owner msa_db_wf msa_db_matches msa_db_implied
      msa_db_complete msa_prob_db msa_learnt_db msa_binary_out msa_reasons_mem
      msa_reason_head msa_size msa_wmap_exact.
Qed.

Lemma minisat_focus_real_word_owner__propagate_dbu :
  forall n db p o w,
    db_wf n db ->
    In (o, w) (minisat_focus_contributions db p) ->
    is_tag w = false ->
    exists co, In (w, co) db /\
      o = minisat_occurrence_of_entry (w, co).
Proof.
  intros n db p o w Hdb Hin Hreal.
  unfold minisat_focus_contributions in Hin.
  apply in_flat_map in Hin as [[q co] [Hentry Hin]].
  unfold minisat_entry_focus_contributions in Hin.
  apply in_map_iff in Hin as [w0 [Hpair Hinw]].
  inversion Hpair; subst o w.
  assert (Hqe : Z.even q = true).
  { eapply db_wf_even; eassumption. }
  unfold entry_watchers in Hinw; cbn in Hinw.
  apply in_app_or in Hinw.
  destruct (3 <=? Zlength (co_lits co)) eqn:Hbig.
  - destruct Hinw as [Hinw | Hinw].
    + destruct (lit_neg_c (co_watch0 co) =? p);
        cbn in Hinw; try contradiction.
      destruct Hinw as [Heq | []]. subst w0.
      exists co. split; [exact Hentry|reflexivity].
    + destruct (lit_neg_c (co_watch1 co) =? p);
        cbn in Hinw; try contradiction.
      destruct Hinw as [Heq | []]. subst w0.
      exists co. split; [exact Hentry|reflexivity].
  - exfalso. destruct Hinw as [Hinw | Hinw].
    + destruct (lit_neg_c (co_watch0 co) =? p);
        cbn in Hinw; try contradiction.
      destruct Hinw as [Heq | []]. subst w0.
      rewrite is_tag_of in Hreal. discriminate.
    + destruct (lit_neg_c (co_watch1 co) =? p);
        cbn in Hinw; try contradiction.
      destruct Hinw as [Heq | []]. subst w0.
      rewrite is_tag_of in Hreal. discriminate.
Qed.

Lemma minisat_focus_contributions_app__propagate_dbu :
  forall db1 db2 p,
    minisat_focus_contributions (db1 ++ db2) p =
      minisat_focus_contributions db1 p ++
      minisat_focus_contributions db2 p.
Proof.
  intros. unfold minisat_focus_contributions. apply flat_map_app.
Qed.

Lemma minisat_focus_contributions_cons__propagate_dbu :
  forall e db p,
    minisat_focus_contributions (e :: db) p =
      minisat_entry_focus_contributions p e ++
      minisat_focus_contributions db p.
Proof. reflexivity. Qed.

Lemma db_pair_lits_update_splice__propagate_dbu :
  forall prob learnt current old_lits new_lits prob' learnt',
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    exists co pre post,
      prob ++ learnt = pre ++ (current, co) :: post /\
      prob' ++ learnt' = pre ++ (current, clause_obj_with_lits co new_lits) :: post /\
      co_lits co = old_lits.
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' Hupdate.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hlits [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hlits [Hprob' Hlearnt']]]]]]].
  - subst prob prob' learnt'. exists co, pre, (post ++ learnt).
    split; [rewrite <- app_assoc; reflexivity|].
    split; [rewrite <- app_assoc; reflexivity|exact Hlits].
  - subst learnt prob' learnt'. exists co, (prob ++ pre), post.
    split; [rewrite <- app_assoc; reflexivity|].
    split; [rewrite <- app_assoc; reflexivity|exact Hlits].
Qed.

Lemma db_pair_lits_update_selected_before__propagate_dbu :
  forall prob learnt current old_lits new_lits prob' learnt',
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    exists co, In (current, co) (prob ++ learnt) /\ co_lits co = old_lits.
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' Hupdate.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [co [pre [post [Hold [_ Hlits]]]]].
  exists co. split; [|exact Hlits].
  rewrite Hold. apply in_or_app. right. left. reflexivity.
Qed.

Lemma db_pair_lits_update_forall__propagate_dbu :
  forall prob learnt current old_lits new_lits prob' learnt'
    (P : Z * clause_obj -> Prop),
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    (forall co, In (current, co) (prob ++ learnt) -> co_lits co = old_lits ->
      P (current, co) -> P (current, clause_obj_with_lits co new_lits)) ->
    Forall P (prob ++ learnt) -> Forall P (prob' ++ learnt').
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' P Hupdate Hselected Hall.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [co [pre [post [Hold [Hnew Hlits]]]]].
  assert (Hin : In (current, co) (prob ++ learnt)).
  { rewrite Hold. apply in_or_app. right. left. reflexivity. }
  rewrite Hold, Forall_app in Hall. rewrite Hnew, Forall_app.
  destruct Hall as [Hpre Hrest].
  inversion Hrest as [|entry rest Hco Hpost]; subst.
  split; [exact Hpre|]. constructor; [|exact Hpost].
  apply Hselected; auto.
Qed.

Lemma db_pair_lits_update_flat_map_permutation__propagate_dbu :
  forall (A : Type) (f : Z * clause_obj -> list A)
    prob learnt current old_lits new_lits prob' learnt',
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    (forall co, In (current, co) (prob ++ learnt) -> co_lits co = old_lits ->
      Permutation (f (current, co))
        (f (current, clause_obj_with_lits co new_lits))) ->
    Permutation (flat_map f (prob ++ learnt)) (flat_map f (prob' ++ learnt')).
Proof.
  intros A f prob learnt current old_lits new_lits prob' learnt' Hupdate Hselected.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [co [pre [post [Hold [Hnew Hlits]]]]].
  rewrite Hold, Hnew, !flat_map_app. cbn [flat_map].
  apply Permutation_app_head. apply Permutation_app_tail.
  apply Hselected; [rewrite Hold; apply in_or_app; right; left; reflexivity|exact Hlits].
Qed.

Lemma db_pair_lits_update_identity__propagate_dbu :
  forall prob learnt current lits prob' learnt',
    db_pair_lits_update prob learnt current lits lits prob' learnt' ->
    prob' = prob /\ learnt' = learnt.
Proof.
  intros prob learnt current lits prob' learnt' Hupdate.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hlits [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hlits [Hprob' Hlearnt']]]]]]];
    subst; destruct co; cbn in *; subst; split; reflexivity.
Qed.

Lemma db_pair_lits_update_focus_single__propagate_dbu :
  forall prob learnt current old_lits new_lits prob' learnt' p oold onew,
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    (forall co,
      co_lits co = old_lits ->
      minisat_entry_focus_contributions p (current, co) = [(oold, current)]) ->
    (forall co,
      co_lits co = old_lits ->
      minisat_entry_focus_contributions p
        (current, clause_obj_with_lits co new_lits) = [(onew, current)]) ->
    exists pre post,
      minisat_focus_contributions (prob ++ learnt) p =
        pre ++ (oold, current) :: post /\
      minisat_focus_contributions (prob' ++ learnt') p =
        pre ++ (onew, current) :: post.
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' p oold onew
    Hupdate Hold Hnew.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [co [pre [post [Hbefore [Hafter Hlits]]]]].
  exists (minisat_focus_contributions pre p), (minisat_focus_contributions post p).
  rewrite Hbefore, Hafter, !minisat_focus_contributions_app__propagate_dbu,
    !minisat_focus_contributions_cons__propagate_dbu,
    (Hold co Hlits), (Hnew co Hlits). split; reflexivity.
Qed.

Lemma focus_scan_carrier_pop_real__propagate_dbu :
  forall n olddb p P kept rest current co pre post,
    db_wf n olddb ->
    In (current, co) olddb ->
    is_tag current = false ->
    minisat_focus_contributions olddb p =
      pre ++ (minisat_occurrence_of_entry (current, co), current) :: post ->
    minisat_focus_scan_carrier olddb p P kept (current :: rest) ->
    exists scanned pending,
      Permutation (scanned ++ pending) (pre ++ post) /\
      minisat_focus_words scanned = kept /\
      minisat_focus_words pending = rest /\
      Forall (fun c => minisat_occurrence_safe P (fst c)) scanned.
Proof.
  intros n olddb p P kept rest current co pre post
    Hdb Hselected Hreal Hold Hscan.
  unfold minisat_focus_scan_carrier in Hscan.
  destruct Hscan as [scanned [pending [Hcover [Hkept [Hrest Hsafe]]]]].
  destruct pending as [|[o w] pending]; cbn in Hrest; [discriminate|].
  inversion Hrest; subst w.
  assert (Hinold : In (o, current) (minisat_focus_contributions olddb p)).
  { eapply Permutation_in; [exact Hcover|].
    apply in_or_app. right. cbn. auto. }
  destruct (minisat_focus_real_word_owner__propagate_dbu
    n olddb p o current Hdb Hinold Hreal) as [co' [Hco' Ho]].
  assert (Hco : co' = co).
  { eapply db_wf_lookup_unique; [exact Hdb|exact Hco'|exact Hselected]. }
  subst co'. subst o.
  exists scanned, pending. repeat split; try assumption.
  rewrite Hold in Hcover. eapply Permutation_app_inv; exact Hcover.
Qed.

Lemma focus_scan_carrier_db_pair_token_replace__propagate_dbu :
  forall n olddb newdb p P kept rest current co onew pre post,
    db_wf n olddb ->
    In (current, co) olddb ->
    is_tag current = false ->
    minisat_focus_contributions olddb p =
      pre ++ (minisat_occurrence_of_entry (current, co), current) :: post ->
    minisat_focus_contributions newdb p =
      pre ++ (onew, current) :: post ->
    minisat_occurrence_safe P onew ->
    minisat_focus_scan_carrier olddb p P kept (current :: rest) ->
    minisat_focus_scan_carrier newdb p P (kept ++ (current :: nil)) rest.
Proof.
  intros n olddb newdb p P kept rest current co onew pre post
    Hdb Hselected Hreal Hold Hnew Hnewsafe Hscan.
  destruct (focus_scan_carrier_pop_real__propagate_dbu
    n olddb p P kept rest current co pre post Hdb Hselected Hreal Hold Hscan)
    as [scanned [pending [Hbase [Hkept [Hrest Hsafe]]]]].
  unfold minisat_focus_scan_carrier.
  exists (scanned ++ ((onew, current) :: nil)), pending.
  split.
  - rewrite Hnew, <- app_assoc. cbn.
    apply Permutation_elt. exact Hbase.
  - split.
    + unfold minisat_focus_words in Hkept |- *.
      rewrite map_app. cbn.
      exact (f_equal (fun xs : list Z => xs ++ (current :: nil)) Hkept).
    + split; [exact Hrest|].
      apply Forall_app. split; [exact Hsafe|].
      constructor; [exact Hnewsafe|constructor].
Qed.

Lemma propagation_unit_normalized_clause_db_rebuild__propagate_dbu :
  forall (n : Z) (prob learnt : dbmap)
    (scan_current clause_lits watch0 false_lit : Z)
    (clause_contents : list Z),
    db_wf n (prob ++ learnt) ->
    2 <= Zlength clause_contents ->
    clause_lits_pointer scan_current clause_lits ->
    (clause_db_pair_frame
       prob learnt scan_current clause_contents **
     (clause_lits + 0 * sizeof(INT)) # Int |-> watch0 **
     (clause_lits + 1 * sizeof(INT)) # Int |-> false_lit **
     IntArray.seg clause_lits 2 (Zlength clause_contents)
       (sublist 2 (Zlength clause_contents) clause_contents))
    |-- EX prob_after learnt_after : dbmap,
      “ db_pair_lits_update prob learnt scan_current clause_contents
          (propagation_normalized_clause watch0 false_lit clause_contents)
          prob_after learnt_after ” &&
      (clause_db_rep prob_after ** clause_db_rep learnt_after).
Proof.
  intros n prob learnt scan_current clause_lits watch0 false_lit
    clause_contents Hdbwf Hlen Hlits.
  unfold clause_lits_pointer in Hlits. subst clause_lits.
  assert (Hnewlen :
    Zlength (propagation_normalized_clause watch0 false_lit clause_contents) =
      Zlength clause_contents).
  { apply propagation_normalized_clause_length. exact Hlen. }
  unfold clause_db_pair_frame. Intros is_learnt.
  sep_apply_l_atomic
    (IntArray.seg_single (clause_lits_addr scan_current) 0 watch0).
  sep_apply_l_atomic
    (IntArray.seg_single (clause_lits_addr scan_current) 1 false_lit).
  
  replace (0 + 1) with 1 by lia.
  replace (1 + 1) with 2 by lia.
  sep_apply_l_atomic
    (IntArray.seg_merge_to_seg (clause_lits_addr scan_current)
      0 1 2 (watch0 :: nil) (false_lit :: nil)).
  - dump_pre_spatial. lia.
  - cbn [app].
    sep_apply_l_atomic
      (IntArray.seg_merge_to_seg (clause_lits_addr scan_current)
        0 2 (Zlength clause_contents) (watch0 :: false_lit :: nil)
        (sublist 2 (Zlength clause_contents) clause_contents)).
    + dump_pre_spatial. lia.
    + cbn [app].
      fold (propagation_normalized_clause
        watch0 false_lit clause_contents).
      unfold clause_db_pair_remainder. Split.
      * Intros co pre post. 
        destruct H as [Hprob [Hco_lits Hco_learnt]].
        assert (Hin : In (scan_current, co) (prob ++ learnt)).
        { rewrite Hprob, !in_app_iff. cbn. tauto. }
        assert (Hpos : 0 < scan_current).
        { eapply db_wf_ptr_pos; [exact Hdbwf | exact Hin]. }
        assert (Hmod : scan_current mod 2 = 0).
        { apply clause_ptr_mod2.
          eapply db_wf_even; [exact Hdbwf | exact Hin]. }
        set (new_lits := propagation_normalized_clause
          watch0 false_lit clause_contents).
        set (co_new := clause_obj_with_lits co new_lits).
        set (prob_after := pre ++ (scan_current, co_new) :: post).
        Exists prob_after learnt.
        split_pure_spatial.
        -- unfold prob_after.
           sep_apply_r_atomic (clause_db_rep_app_intro pre ((scan_current, co_new) :: post)).
           rewrite clause_db_rep_cons.
           unfold MiniSatClause.rep, co_new, clause_obj_with_lits,
             new_lits.
           cbn [fst snd co_lits co_learnt].
           rewrite Hco_learnt, Hnewlen. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
        -- apply derivable1s_coq_prop_r. left. exists co, pre, post.
           split; [exact Hprob |]. split; [exact Hco_lits |].
           split; reflexivity.
      * Intros co pre post. 
        destruct H as [Hlearnt [Hco_lits Hco_learnt]].
        assert (Hin : In (scan_current, co) (prob ++ learnt)).
        { rewrite Hlearnt, !in_app_iff. cbn. tauto. }
        assert (Hpos : 0 < scan_current).
        { eapply db_wf_ptr_pos; [exact Hdbwf | exact Hin]. }
        assert (Hmod : scan_current mod 2 = 0).
        { apply clause_ptr_mod2.
          eapply db_wf_even; [exact Hdbwf | exact Hin]. }
        set (new_lits := propagation_normalized_clause
          watch0 false_lit clause_contents).
        set (co_new := clause_obj_with_lits co new_lits).
        set (learnt_after := pre ++ (scan_current, co_new) :: post).
        Exists prob learnt_after.
        split_pure_spatial.
        -- unfold learnt_after.
           sep_apply_r_atomic (clause_db_rep_app_intro pre ((scan_current, co_new) :: post)).
           rewrite clause_db_rep_cons.
           unfold MiniSatClause.rep, co_new, clause_obj_with_lits,
             new_lits.
           cbn [fst snd co_lits co_learnt].
           rewrite Hco_learnt, Hnewlen. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
        -- apply derivable1s_coq_prop_r. right. exists co, pre, post.
           split; [exact Hlearnt |]. split; [exact Hco_lits |].
           split; reflexivity.
Qed.

Lemma focus_scan_current_real_watch_pair__propagate_dbu :
  forall (n : Z) (db : dbmap) (p current : Z) (co : clause_obj)
    (P : literal -> Prop) (kept rest : list Z),
    db_wf n db ->
    In (current, co) db ->
    is_tag current = false ->
    3 <= Zlength (co_lits co) ->
    minisat_focus_scan_carrier db p P kept (current :: rest) ->
    real_watch_pair p (co_lits co).
Proof.
  intros n db p current co P kept rest Hdb Hselected Hreal Hlen Hscan.
  pose proof (db_wf_obj n db current co Hdb Hselected) as Hobj.
  pose proof (obj_wf_watch0 n co Hobj) as Hwatch0wf.
  pose proof (obj_wf_watch1 n co Hobj) as Hwatch1wf.
  unfold minisat_focus_scan_carrier in Hscan.
  destruct Hscan as
    [scanned [pending [Hcover [Hkept [Hwords Hsafe]]]]].
  destruct pending as [|[o w] pending]; cbn in Hwords; [discriminate|].
  inversion Hwords; subst w.
  assert (Hin : In (o, current) (minisat_focus_contributions db p)).
  {
    eapply Permutation_in; [exact Hcover|].
    apply in_or_app. right. cbn. auto.
  }
  unfold minisat_focus_contributions in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [[q co'] [Hentry Hinwatch]].
  unfold minisat_entry_focus_contributions in Hinwatch.
  apply in_map_iff in Hinwatch.
  destruct Hinwatch as [word [Hpair Hinwatch]].
  inversion Hpair; subst word o.
  unfold entry_watchers in Hinwatch; cbn in Hinwatch.
  apply in_app_or in Hinwatch.
  destruct Hinwatch as [Hinwatch | Hinwatch].
  - destruct (lit_neg_c (co_watch0 co') =? p)%Z eqn:Hwatch;
      cbn in Hinwatch; [|contradiction].
    destruct (3 <=? Zlength (co_lits co'))%Z eqn:Hlarge;
      cbn in Hinwatch.
    + destruct Hinwatch as [Hq | []]. subst q.
      assert (Hco : co' = co).
      { eapply db_wf_lookup_unique;
          [exact Hdb | exact Hentry | exact Hselected]. }
      subst co'.
      apply Z.eqb_eq in Hwatch.
      unfold real_watch_pair, co_watch0.
      left. rewrite <- Hwatch.
      rewrite lit_neg_c_involutive.
      reflexivity.
    + destruct Hinwatch as [Htag | []]. subst current.
      rewrite is_tag_of in Hreal. discriminate.
  - destruct (lit_neg_c (co_watch1 co') =? p)%Z eqn:Hwatch;
      cbn in Hinwatch; [|contradiction].
    destruct (3 <=? Zlength (co_lits co'))%Z eqn:Hlarge;
      cbn in Hinwatch.
    + destruct Hinwatch as [Hq | []]. subst q.
      assert (Hco : co' = co).
      { eapply db_wf_lookup_unique;
          [exact Hdb | exact Hentry | exact Hselected]. }
      subst co'.
      apply Z.eqb_eq in Hwatch.
      unfold real_watch_pair, co_watch1.
      right. rewrite <- Hwatch.
      rewrite lit_neg_c_involutive.
      reflexivity.
    + destruct Hinwatch as [Htag | []]. subst current.
      rewrite is_tag_of in Hreal. discriminate.
Qed.

Lemma binary_watch_write_prefix__propagate_dbu :
  forall (xs mem prefix : list Z) (write_at : Z),
    0 <= write_at ->
    write_at + Zlength xs <= Zlength mem ->
    Zlength prefix = write_at ->
    sublist 0 write_at mem = prefix ->
    exists tail,
      binary_watch_write write_at xs mem = prefix ++ xs ++ tail /\
      Zlength tail = Zlength mem - write_at - Zlength xs.
Proof.
  intros xs. induction xs as [|a xs IH];
    intros mem prefix write_at Hwrite0 Hbound Hplen Hprefix.
  - simpl. rewrite Zlength_nil in Hbound.
    exists (sublist write_at (Zlength mem) mem). simpl.
    split.
    + rewrite <- Hprefix.
      rewrite <- (sublist_split 0 (Zlength mem) write_at mem) by lia.
      rewrite sublist_self by reflexivity. reflexivity.
    + rewrite Zlength_nil. rewrite Zlength_sublist by lia. lia.
  - rewrite Zlength_cons in Hbound.
    pose proof (Zlength_nonneg xs).
    assert (Hindex : 0 <= write_at < Zlength mem) by lia.
    simpl.
    destruct (IH (replace_Znth write_at a mem)
      (prefix ++ (a :: nil)%list) (write_at + 1))
      as [tail [Htail Htail_len]].
    + lia.
    + rewrite Zlength_replace_Znth. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hplen. lia.
    + rewrite (replace_Znth_split write_at a mem Hindex).
      rewrite Hprefix.
      replace (prefix ++ a ::
        sublist (write_at + 1) (Zlength mem) mem)
        with ((prefix ++ (a :: nil)%list) ++
          sublist (write_at + 1) (Zlength mem) mem)
        by (rewrite <- app_assoc; reflexivity).
      replace (write_at + 1) with
        (Zlength (prefix ++ (a :: nil)%list)) by
        (rewrite Zlength_app, Zlength_cons, Zlength_nil, Hplen; lia).
      apply sublist_app_exact1.
    + exists tail. split.
      * rewrite Htail. rewrite <- !app_assoc. reflexivity.
      * rewrite Zlength_replace_Znth in Htail_len.
        rewrite Zlength_cons. lia.
Qed.

Lemma propagation_normalized_frontier_transport :
  forall (n : Z) (M : msolver) (p current : Z) (co : clause_obj)
    (a0 a1 watch0 false_lit : Z) (tail : list Z)
    (prob_after learnt_after : dbmap),
    db_wf n (msolver_db M) ->
    In (current, co) (msolver_db M) ->
    co_lits co = a0 :: a1 :: tail ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
      prob_after learnt_after ->
    minisat_watch_frontier_except n (msolver_db M) (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M)) (lit_denote p) ->
    minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M))
      (lit_denote p).
Proof.
  intros n M p current co a0 a1 watch0 false_lit tail prob_after learnt_after
    Hdbwf Hin Hco_lits Hwatchcases Hupdate Hfrontier.
  unfold minisat_watch_frontier_except, minisat_watch_occurrences,
    watch_frontier_except in Hfrontier |- *.
  rewrite Forall_map in Hfrontier |- *.
  eapply db_pair_lits_update_forall__propagate_dbu;
    [exact Hupdate| |exact Hfrontier].
  intros selected Hselected Hlits Hfront.
  assert (Heq : selected = co).
  { eapply db_wf_lookup_unique; [exact Hdbwf|exact Hselected|exact Hin]. }
  subst selected. destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]];
    subst; unfold minisat_occurrence_of_entry, co_watch0, co_watch1,
      clause_obj_with_lits, propagation_normalized_clause in *;
    rewrite Hco_lits in Hfront; cbn in *; tauto.
Qed.

Lemma propagation_norm_clause_watcher_xport__propagate_dbu :
  forall (n : Z) (M : msolver) (P : literal -> Prop)
    (p current : Z) (suffix kept contents : list Z)
    (watch0 false_lit lits stop k offset candidate sig : Z)
    (prob_after learnt_after : dbmap),
    db_wf n (msolver_db M) ->
    propagation_scan_candidate_layout current lits stop k offset false_lit
      p candidate sig contents ->
    watch0 + false_lit = Znth 0 contents 0 + Znth 1 contents 0 ->
    minisat_focus_scan_carrier
      (msolver_db M) p P kept (current :: suffix) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current contents
      (propagation_normalized_clause watch0 false_lit contents)
      prob_after learnt_after ->
    minisat_watch_frontier_except n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    exists (co : clause_obj) (a0 a1 : Z) (tail : list Z),
      contents = a0 :: a1 :: tail /\
      In (current, co) (msolver_db M) /\
      co_lits co = a0 :: a1 :: tail /\
      sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail /\
      ((a0 = false_lit /\ watch0 = a1) \/
       (a1 = false_lit /\ watch0 = a0)) /\
      Permutation
        (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
        (a0 :: a1 :: tail) /\
      (forall l,
        Permutation (expected_watchers (msolver_db M) l)
          (expected_watchers (prob_after ++ learnt_after) l)) /\
      minisat_watch_frontier_except n (prob_after ++ learnt_after)
        (mt_assigns (ms_core M)) (mt_trail (ms_core M))
        (mt_qhead (ms_core M)) (lit_denote p).
Proof.
  intros n M P p current suffix kept contents watch0 false_lit lits stop k
    offset candidate sig prob_after learnt_after Hdbwf Hlayout Hwatchsum
    Hscan Hupdate Hfrontier.
  pose proof Hlayout as Hlayout_fields.
  unfold propagation_scan_candidate_layout in Hlayout_fields.
  destruct Hlayout_fields as
    [Hlits [Hclauselen [Hfalse [Hstop [Hk
    [Hoffset [Hcandidate Hsig]]]]]]].
  destruct (db_pair_lits_update_selected_before__propagate_dbu
    _ _ _ _ _ _ _ Hupdate) as [co [Hin Hco_lits]].
  pose proof (db_wf_obj n (msolver_db M) current co Hdbwf Hin) as Hobj.
  unfold obj_wf in Hobj. rewrite Hco_lits in Hobj.
  destruct Hobj as [Hobjlen [Hall Hnodup]].
  assert (Hcurrentreal : is_tag current = false).
  { apply even_not_tag. eapply db_wf_even; eassumption. }
  assert (Hrealwatch_co : real_watch_pair p (co_lits co)).
  {
    eapply focus_scan_current_real_watch_pair__propagate_dbu
      with (db := msolver_db M) (current := current) (co := co)
        (P := P) (kept := kept) (rest := suffix).
    - exact Hdbwf.
    - exact Hin.
    - exact Hcurrentreal.
    - rewrite Hco_lits. exact Hclauselen.
    - exact Hscan.
  }
  assert (Hrealwatch : real_watch_pair p contents).
  { rewrite <- Hco_lits. exact Hrealwatch_co. }
  destruct contents as [|a0 tail0]; cbn in Hobjlen; [lia|].
  destruct tail0 as [|a1 tail]; cbn in Hobjlen; [lia|].
  assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail))
      (a0 :: a1 :: tail) = tail).
  {
    replace (a0 :: a1 :: tail) with ((a0 :: a1 :: nil) ++ tail)
      by reflexivity.
    assert (Hrange : 2 <= 2 <= Zlength ((a0 :: a1 :: nil) ++ tail)).
    {
      split; [lia|]. rewrite Zlength_app.
      change (2 <= 2 + Zlength tail).
      pose proof (Zlength_nonneg tail). lia.
    }
    rewrite (sublist_split_app_r 2
      (Zlength ((a0 :: a1 :: nil) ++ tail)) 2
      (a0 :: a1 :: nil) tail ltac:(reflexivity) Hrange).
    replace (Zlength ((a0 :: a1 :: nil) ++ tail) - 2)
      with (Zlength tail) by
      (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
    apply sublist_self. reflexivity.
  }
  assert (Hwatchcases :
    (a0 = false_lit /\ watch0 = a1) \/
    (a1 = false_lit /\ watch0 = a0)).
  {
    unfold real_watch_pair in Hrealwatch.
    rewrite !Znth0_cons in Hrealwatch, Hwatchsum.
    rewrite !Znth_cons in Hrealwatch, Hwatchsum by lia.
    replace (1 - 1) with 0 in Hrealwatch, Hwatchsum by lia.
    rewrite !Znth0_cons in Hrealwatch, Hwatchsum.
    destruct Hrealwatch as [Hw | Hw].
    - left. rewrite <- Hfalse in Hw. split; [exact Hw|lia].
    - right. rewrite <- Hfalse in Hw. split; [exact Hw|lia].
  }
  assert (Hperm : Permutation
    (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
    (a0 :: a1 :: tail)).
  {
    unfold propagation_normalized_clause. rewrite Htail.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - subst a0 watch0. apply perm_swap.
    - subst a1 watch0. reflexivity.
  }
  set (new_lits := propagation_normalized_clause
    watch0 false_lit (a0 :: a1 :: tail)).
  set (co_new := clause_obj_with_lits co new_lits).
  assert (Hentryperm : forall l,
    Permutation (entry_watchers (current, co) l)
      (entry_watchers (current, co_new) l)).
  {
    intros l. destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - subst a0 watch0.
      unfold entry_watchers, co_watch0, co_watch1, co_new,
        clause_obj_with_lits, new_lits, propagation_normalized_clause.
      rewrite Hco_lits, Htail. cbn. apply Permutation_app_comm.
    - subst a1 watch0.
      unfold entry_watchers, co_watch0, co_watch1, co_new,
        clause_obj_with_lits, new_lits, propagation_normalized_clause.
      rewrite Hco_lits, Htail. cbn. reflexivity.
  }
  fold new_lits in Hupdate.
  assert (Hexpected : forall l,
    Permutation (expected_watchers (msolver_db M) l)
      (expected_watchers (prob_after ++ learnt_after) l)).
  {
    intros l. unfold expected_watchers.
    eapply db_pair_lits_update_flat_map_permutation__propagate_dbu;
      [exact Hupdate|].
    intros selected Hselected Hselectedlits.
    assert (Heq : selected = co).
    { eapply db_wf_lookup_unique; [exact Hdbwf|exact Hselected|exact Hin]. }
    subst selected. apply Hentryperm.
  }
  assert (Hfrontiernew : minisat_watch_frontier_except n
    (prob_after ++ learnt_after) (mt_assigns (ms_core M))
    (mt_trail (ms_core M)) (mt_qhead (ms_core M)) (lit_denote p))
    by (unfold new_lits in Hupdate;
        eapply propagation_normalized_frontier_transport; eassumption).
  exists co, a0, a1, tail.
  split; [reflexivity |].
  split; [exact Hin |].
  split; [exact Hco_lits |].
  split; [exact Htail |].
  split; [exact Hwatchcases |].
  split; [exact Hperm |].
  split; [exact Hexpected | exact Hfrontiernew].
Qed.

Lemma propagation_normalized_clause_weak_transport__propagate_dbu :
  forall (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p current false_lit watch0 a0 a1 : Z) (tail : list Z)
    (co : clause_obj) (prob_after learnt_after : dbmap),
    solver_propagation_weak n F A_arr K M ->
    processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) p ->
    false_lit = lit_neg_c p ->
    In (current, co) (msolver_db M) ->
    co_lits co = a0 :: a1 :: tail ->
    sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail ->
    ((a0 = false_lit /\ watch0 = a1) \/
     (a1 = false_lit /\ watch0 = a0)) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
      prob_after learnt_after ->
    Permutation
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
      (a0 :: a1 :: tail) ->
    (forall l,
      Permutation (expected_watchers (msolver_db M) l)
        (expected_watchers (prob_after ++ learnt_after) l)) ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update M prob_after learnt_after
        (ms_wm M)).
Proof.
  intros n F A_arr K M p current false_lit watch0 a0 a1 tail co
    prob_after learnt_after Hweak Hprocessed Hfalse Hin Hco_lits Htail
    Hwatchcases Hupdate Hperm Hexpected.
  assert (Hfalsefalse : lit_false (mt_assigns (ms_core M)) false_lit).
  {
    destruct Hprocessed as [Hptrue Hprocessed_rest].
    unfold lit_true in Hptrue. unfold lit_false.
    rewrite Hfalse, lit_var_c_neg, lit_sig_neg. lia.
  }
  set (new_lits := propagation_normalized_clause
    watch0 false_lit (a0 :: a1 :: tail)).
  fold new_lits in Hupdate, Hperm.
  destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
  - assert (Hheadfalse : lit_false (mt_assigns (ms_core M)) (co_watch0 co)).
    { unfold co_watch0. rewrite Hco_lits. subst a0. cbn. exact Hfalsefalse. }
    unfold solver_propagation_weak in Hweak |- *.
    destruct Hweak as [Hroot0 Hctx]. split.
    + unfold msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hroot0.
    + eapply (ctx_db_pair_lits_no_owner__propagate_dbu n F A_arr K M).
      * exact Hctx.
      * exact Hupdate.
      * exact Hperm.
      * exact Hexpected.
      * eapply (ctx_no_live_reason_owner_head_false__propagate_dbu
          n F A_arr K M); eassumption.
  - assert (Hnewid : new_lits = a0 :: a1 :: tail).
    {
      unfold new_lits, propagation_normalized_clause. rewrite Htail.
      subst a1 watch0. reflexivity.
    }
    assert (Hdbid : prob_after = ms_prob M /\ learnt_after = ms_learnt M).
    { rewrite Hnewid in Hupdate.
      eapply db_pair_lits_update_identity__propagate_dbu; exact Hupdate. }
    destruct Hdbid as [Hprobid Hlearntid].
    rewrite Hprobid, Hlearntid.
    unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update. destruct M. exact Hweak.
Qed.

Lemma focus_scan_carrier_words_expected__propagate_dbu :
  forall (db : dbmap) (p : Z) (P : literal -> Prop) (kept rest : list Z),
    minisat_focus_scan_carrier db p P kept rest ->
    Permutation (kept ++ rest) (expected_watchers db p).
Proof.
  intros db p P kept rest Hscan.
  unfold minisat_focus_scan_carrier in Hscan.
  destruct Hscan as [scanned [pending [Hcover [Hkept [Hpending Hsafe]]]]].
  pose proof (Permutation_map snd Hcover) as Hcoverwords.
  change (Permutation
    (minisat_focus_words (scanned ++ pending))
    (minisat_focus_words (minisat_focus_contributions db p)))
    in Hcoverwords.
  unfold minisat_focus_words at 1 in Hcoverwords.
  rewrite map_app in Hcoverwords.
  change (Permutation
    (minisat_focus_words scanned ++ minisat_focus_words pending)
    (minisat_focus_words (minisat_focus_contributions db p)))
    in Hcoverwords.
  rewrite Hkept, Hpending in Hcoverwords.
  rewrite minisat_focus_words_expected in Hcoverwords.
  exact Hcoverwords.
Qed.

(** ===== group: solver_propagate_db_update_unit_arm ===== *)


Lemma propagation_unit_normalized_watcher_transport__propagate_dbu :
  forall (n : Z) (M : msolver) (P : literal -> Prop)
    (p current : Z) (suffix kept contents : list Z)
    (watch0 false_lit clause_lits : Z)
    (prob_after learnt_after : dbmap),
    db_wf n (msolver_db M) ->
    clause_lits_pointer current clause_lits ->
    false_lit = lit_neg_c p ->
    watch0 + false_lit = Znth 0 contents 0 + Znth 1 contents 0 ->
    minisat_focus_scan_carrier
      (msolver_db M) p P kept (current :: suffix) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current contents
      (propagation_normalized_clause watch0 false_lit contents)
      prob_after learnt_after ->
    minisat_watch_frontier_except n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    exists (co : clause_obj) (a0 a1 : Z) (tail : list Z),
      contents = a0 :: a1 :: tail /\
      3 <= Zlength contents /\
      In (current, co) (msolver_db M) /\
      co_lits co = a0 :: a1 :: tail /\
      sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail /\
      ((a0 = false_lit /\ watch0 = a1) \/
       (a1 = false_lit /\ watch0 = a0)) /\
      Permutation
        (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
        (a0 :: a1 :: tail) /\
      (forall l,
        Permutation (expected_watchers (msolver_db M) l)
          (expected_watchers (prob_after ++ learnt_after) l)) /\
      minisat_watch_frontier_except n (prob_after ++ learnt_after)
        (mt_assigns (ms_core M)) (mt_trail (ms_core M))
        (mt_qhead (ms_core M)) (lit_denote p).
Proof.
  intros n M P p current suffix kept contents watch0 false_lit clause_lits
    prob_after learnt_after Hdbwf Hlits Hfalse Hwatchsum
    Hscan Hupdate Hfrontier.
  destruct (db_pair_lits_update_selected_before__propagate_dbu
    _ _ _ _ _ _ _ Hupdate) as [co [Hin Hco_lits]].
  assert (Hcurrentreal : is_tag current = false).
  { apply even_not_tag. eapply db_wf_even; eassumption. }
  assert (Hlong : 3 <= Zlength contents).
  {
    pose proof Hscan as Hscan0.
    unfold minisat_focus_scan_carrier in Hscan0.
    destruct Hscan0 as
      [scanned [pending [Hcover [Hkept [Hpending Hsafe]]]]].
    destruct pending as [|[o w] pending]; cbn in Hpending;
      [discriminate|].
    inversion Hpending; subst w.
    assert (Hinold :
      In (o, current) (minisat_focus_contributions (msolver_db M) p)).
    { eapply Permutation_in; [exact Hcover|].
      apply in_or_app. right. cbn. auto. }
    destruct (minisat_focus_real_word_owner__propagate_dbu
      n (msolver_db M) p o current Hdbwf Hinold Hcurrentreal)
      as [co_owner [Hin_owner Ho]].
    unfold minisat_focus_contributions in Hinold.
    apply in_flat_map in Hinold as [[q co_source] [Hin_source Hentry]].
    unfold minisat_entry_focus_contributions in Hentry.
    apply in_map_iff in Hentry as [w0 [Hpair Hword]].
    injection Hpair as Hocc Hw0. subst w0.
    assert (Hsource_long : 3 <= Zlength (co_lits co_source)).
    {
      unfold entry_watchers in Hword. cbn in Hword.
      apply in_app_or in Hword.
      destruct ((3 <=? Zlength (co_lits co_source))%Z) eqn:Hbig.
      - apply Z.leb_le. exact Hbig.
      - exfalso. destruct Hword as [Hword | Hword].
        + destruct ((lit_neg_c (co_watch0 co_source) =? p)%Z) eqn:Hwatch0;
            cbn in Hword.
          * destruct Hword as [Heq | []]. subst current.
            rewrite is_tag_of in Hcurrentreal. discriminate.
          * contradiction.
        + destruct ((lit_neg_c (co_watch1 co_source) =? p)%Z) eqn:Hwatch1;
            cbn in Hword.
          * destruct Hword as [Heq | []]. subst current.
            rewrite is_tag_of in Hcurrentreal. discriminate.
          * contradiction.
    }
    assert (Hq : q = current).
    {
      rewrite Ho in Hocc.
      pose proof (f_equal watch_owner Hocc) as Howner.
      exact Howner.
    }
    subst q.
    assert (Hsource_owner : co_source = co_owner).
    { eapply db_wf_lookup_unique; eassumption. }
    subst co_source.
    assert (Howner_selected : co_owner = co).
    { eapply db_wf_lookup_unique; eassumption. }
    subst co_owner. rewrite <- Hco_lits. exact Hsource_long.
  }
  assert (Hrealwatchp : real_watch_pair p contents).
  { rewrite <- Hco_lits.
    eapply focus_scan_current_real_watch_pair__propagate_dbu
      with (co := co) (P := P) (kept := kept) (rest := suffix).
    - exact Hdbwf.
    - exact Hin.
    - exact Hcurrentreal.
    - rewrite Hco_lits. exact Hlong.
    - exact Hscan. }
  assert (Hlayout : propagation_scan_candidate_layout current clause_lits
    (clause_lits + Zlength contents * sizeof(INT))
    (clause_lits + 2 * sizeof(INT)) 2 false_lit p
    (Znth 0 (sublist 2 (Zlength contents) contents) 0)
    (2 * lit_sign_c
       (Znth 0 (sublist 2 (Zlength contents) contents) 0) - 1)
    contents).
  {
    unfold propagation_scan_candidate_layout.
    split; [exact Hlits|]. split; [exact Hlong|].
    split; [exact Hfalse|]. split; [reflexivity|].
    split; [reflexivity|]. split; [lia|]. split; reflexivity.
  }
  assert (Htransport :
    exists (co' : clause_obj) (a0 a1 : Z) (tail : list Z),
      contents = a0 :: a1 :: tail /\
      In (current, co') (msolver_db M) /\
      co_lits co' = a0 :: a1 :: tail /\
      sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail /\
      ((a0 = false_lit /\ watch0 = a1) \/
       (a1 = false_lit /\ watch0 = a0)) /\
      Permutation
        (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
        (a0 :: a1 :: tail) /\
      (forall l,
        Permutation (expected_watchers (msolver_db M) l)
          (expected_watchers (prob_after ++ learnt_after) l)) /\
      minisat_watch_frontier_except n (prob_after ++ learnt_after)
        (mt_assigns (ms_core M)) (mt_trail (ms_core M))
        (mt_qhead (ms_core M)) (lit_denote p)).
  {
    eapply propagation_norm_clause_watcher_xport__propagate_dbu
      with (lits := clause_lits)
        (stop := clause_lits + Zlength contents * sizeof(INT))
        (k := clause_lits + 2 * sizeof(INT)) (offset := 2)
        (candidate := Znth 0 (sublist 2 (Zlength contents) contents) 0)
        (sig := 2 * lit_sign_c
          (Znth 0 (sublist 2 (Zlength contents) contents) 0) - 1);
      eassumption.
  }
  destruct Htransport as
    [co' [a0 [a1 [tail [Hcontents' [Hin' [Hco_lits'
    [Htail' [Hwatchcases' [Hperm' [Hexpected' Hfrontier']]]]]]]]]]].
  exists co', a0, a1, tail.
  split; [exact Hcontents'|].
  split; [exact Hlong|].
  split; [exact Hin'|].
  split; [exact Hco_lits'|].
  split; [exact Htail'|].
  split; [exact Hwatchcases'|].
  split; [exact Hperm'|].
  split; [exact Hexpected'|exact Hfrontier'].
Qed.

Lemma propagation_unit_db_weak_transport__propagate_dbu :
  forall (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p current false_lit watch0 a0 a1 : Z) (tail contents : list Z)
    (co : clause_obj) (prob_after learnt_after : dbmap),
    solver_propagation_weak n F A_arr K M ->
    processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) p ->
    false_lit = lit_neg_c p ->
    contents = a0 :: a1 :: tail ->
    In (current, co) (msolver_db M) ->
    co_lits co = a0 :: a1 :: tail ->
    sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail ->
    ((a0 = false_lit /\ watch0 = a1) \/
     (a1 = false_lit /\ watch0 = a0)) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current contents
      (propagation_normalized_clause watch0 false_lit contents)
      prob_after learnt_after ->
    Permutation
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
      (a0 :: a1 :: tail) ->
    (forall l,
      Permutation (expected_watchers (msolver_db M) l)
        (expected_watchers (prob_after ++ learnt_after) l)) ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update M prob_after learnt_after
        (ms_wm M)).
Proof.
  intros n F A_arr K M p current false_lit watch0 a0 a1 tail contents
    co prob_after learnt_after Hweak Hprocessed Hfalse Hcontents Hin
    Hco_lits Htail Hwatchcases Hupdate Hperm Hexpected.
  subst contents.
  eapply propagation_normalized_clause_weak_transport__propagate_dbu
    with (p := p) (current := current) (false_lit := false_lit)
      (watch0 := watch0) (a0 := a0) (a1 := a1) (tail := tail)
      (co := co); eassumption.
Qed.

Lemma enqueue_transition_nonzero_cases__propagate_dbu :
  forall (l reason qtail ret qtail' : Z)
    (assigns levels reasons trail lim
     assigns' levels' reasons' trail' : list Z),
    enqueue_transition l reason qtail ret qtail'
      assigns levels reasons trail lim
      assigns' levels' reasons' trail' ->
    ret <> 0 ->
    ret = 1 /\
    ((Znth (lit_var_c l) assigns 0 = lit_sig l /\
      assigns' = assigns /\ levels' = levels /\ reasons' = reasons /\
      trail' = trail /\ qtail' = qtail) \/
     (Znth (lit_var_c l) assigns 0 = 0 /\
      assigns' = replace_Znth (lit_var_c l) (lit_sig l) assigns /\
      levels' = replace_Znth (lit_var_c l) (Zlength lim) levels /\
      reasons' = replace_Znth (lit_var_c l) reason reasons /\
      trail' = trail ++ (l :: nil) /\ qtail' = qtail + 1)).
Proof.
  intros l reason qtail ret qtail' assigns levels reasons trail lim
    assigns' levels' reasons' trail' Htransition Hnonzero.
  unfold enqueue_transition in Htransition.
  destruct Htransition as [Hsame | [Hconflict | Hfresh]].
  - destruct Hsame as
      [Hcell [Hret [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]].
    split; [exact Hret|]. left.
    repeat split; assumption.
  - destruct Hconflict as [_ [_ [Hret _]]]. contradiction.
  - destruct Hfresh as
      [Hcell [Hret [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]].
    split; [exact Hret|]. right.
    repeat split; assumption.
Qed.

Lemma propagation_unit_focus_keep_transport__propagate_dbu :
  forall (n : Z) (M : msolver) (P : literal -> Prop)
    (p current false_lit watch0 a0 a1 : Z)
    (tail contents kept suffix : list Z) (co : clause_obj)
    (prob_after learnt_after : dbmap),
    db_wf n (msolver_db M) ->
    lit_wf_c n p ->
    false_lit = lit_neg_c p ->
    contents = a0 :: a1 :: tail ->
    3 <= Zlength contents ->
    In (current, co) (msolver_db M) ->
    co_lits co = a0 :: a1 :: tail ->
    sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail ->
    ((a0 = false_lit /\ watch0 = a1) \/
     (a1 = false_lit /\ watch0 = a0)) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current contents
      (propagation_normalized_clause watch0 false_lit contents)
      prob_after learnt_after ->
    minisat_focus_scan_carrier
      (msolver_db M) p P kept (current :: suffix) ->
    ~ P (literal_neg (lit_denote watch0)) ->
    minisat_focus_scan_carrier (prob_after ++ learnt_after) p P
      (kept ++ (current :: nil)) suffix.
Proof.
  intros n M P p current false_lit watch0 a0 a1 tail contents kept suffix
    co prob_after learnt_after Hdb Hp Hfalse Hcontents Hlong Hselected
    Hco_lits Htail Hwatchcases Hupdate Hscan Hwatchsafe.
  subst contents.
  pose proof (db_wf_obj n (msolver_db M) current co Hdb Hselected) as Hobj.
  unfold obj_wf in Hobj. rewrite Hco_lits in Hobj.
  destruct Hobj as [Hobjlen [Hall Hnodup]].
  cbn [map] in Hnodup.
  apply NoDup_cons_iff in Hnodup as [Ha0not Hnodup].
  apply NoDup_cons_iff in Hnodup as [Ha1not Hnodup].
  assert (Hvarneq : lit_var_c a0 <> lit_var_c a1).
  { intro Heq. apply Ha0not. left. symmetry. exact Heq. }
  assert (Hnewlen : 3 <= Zlength
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))).
  {
    rewrite propagation_normalized_clause_length;
      [exact Hlong|lia].
  }
  assert (Hlongb :
    (3 <=? Zlength (a0 :: a1 :: tail))%Z = true).
  { apply Z.leb_le. exact Hlong. }
  assert (Hnewlenb :
    (3 <=? Zlength (propagation_normalized_clause watch0 false_lit
      (a0 :: a1 :: tail)))%Z = true).
  { apply Z.leb_le. exact Hnewlen. }
  unfold propagation_normalized_clause in Hnewlenb.
  rewrite Htail in Hnewlenb.
  set (oold := minisat_occurrence_of_entry (current, co)).
  set (onew := minisat_occurrence_of_entry
    (current, clause_obj_with_lits co
      (propagation_normalized_clause watch0 false_lit
        (a0 :: a1 :: tail)))).
  assert (Hmatch : (lit_neg_c false_lit =? p)%Z = true).
  { apply Z.eqb_eq. rewrite Hfalse.
    apply lit_neg_c_involutive. }
  assert (Hfocus : exists pre post,
      minisat_focus_contributions (msolver_db M) p =
        pre ++ (oold, current) :: post /\
      minisat_focus_contributions (prob_after ++ learnt_after) p =
        pre ++ (onew, current) :: post).
  {
    unfold msolver_db.
    eapply db_pair_lits_update_focus_single__propagate_dbu.
    - exact Hupdate.
    - intros co' Hco_lits'.
      unfold minisat_entry_focus_contributions, entry_watchers.
      destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
      + subst a0 watch0.
        assert (Hmiss : (lit_neg_c a1 =? p)%Z = false).
        { apply Z.eqb_neq. intro Heq. apply Hvarneq.
          rewrite Hfalse, <- Heq, !lit_var_c_neg. reflexivity. }
        unfold oold, minisat_occurrence_of_entry, co_watch0, co_watch1,
          denote_obj. rewrite Hco_lits', Hco_lits.
        rewrite !Znth0_cons.
        rewrite !Znth_cons by lia.
        replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
        rewrite Hmatch, Hmiss.
        rewrite Hlongb. cbn. reflexivity.
      + subst a1 watch0.
        assert (Hmiss : (lit_neg_c a0 =? p)%Z = false).
        { apply Z.eqb_neq. intro Heq. apply Hvarneq.
          rewrite Hfalse, <- Heq, !lit_var_c_neg. reflexivity. }
        unfold oold, minisat_occurrence_of_entry, co_watch0, co_watch1,
          denote_obj. rewrite Hco_lits', Hco_lits.
        rewrite !Znth0_cons.
        rewrite !Znth_cons by lia.
        replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
        rewrite Hmiss, Hmatch.
        rewrite Hlongb. cbn. reflexivity.
    - intros co' Hco_lits'.
      unfold minisat_entry_focus_contributions, entry_watchers.
      destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
      + subst a0 watch0.
        assert (Hmiss : (lit_neg_c a1 =? p)%Z = false).
        { apply Z.eqb_neq. intro Heq. apply Hvarneq.
          rewrite Hfalse, <- Heq, !lit_var_c_neg. reflexivity. }
        unfold onew, minisat_occurrence_of_entry, clause_obj_with_lits,
          propagation_normalized_clause, co_watch0, co_watch1, denote_obj.
        rewrite Htail. cbn [co_lits].
        rewrite !Znth0_cons.
        rewrite !Znth_cons by lia.
        replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
        rewrite Hmiss, Hmatch.
        rewrite Hnewlenb. cbn. reflexivity.
      + subst a1 watch0.
        assert (Hmiss : (lit_neg_c a0 =? p)%Z = false).
        { apply Z.eqb_neq. intro Heq. apply Hvarneq.
          rewrite Hfalse, <- Heq, !lit_var_c_neg. reflexivity. }
        unfold onew, minisat_occurrence_of_entry, clause_obj_with_lits,
          propagation_normalized_clause, co_watch0, co_watch1, denote_obj.
        rewrite Htail. cbn [co_lits].
        rewrite !Znth0_cons.
        rewrite !Znth_cons by lia.
        replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
        rewrite Hmiss, Hmatch.
        rewrite Hnewlenb. cbn. reflexivity.
  }
  destruct Hfocus as [pre [post [Hold Hnew]]].
  assert (Hreal : is_tag current = false).
  { apply even_not_tag. eapply db_wf_even; eassumption. }
  assert (Honesafe : minisat_occurrence_safe P onew).
  {
    unfold minisat_occurrence_safe, onew, minisat_occurrence_of_entry,
      clause_obj_with_lits, propagation_normalized_clause, co_watch0,
      co_watch1. cbn. intro Hboth. apply Hwatchsafe. exact (proj1 Hboth).
  }
  eapply focus_scan_carrier_db_pair_token_replace__propagate_dbu
    with (co := co) (pre := pre) (post := post) (onew := onew).
  - exact Hdb.
  - exact Hselected.
  - exact Hreal.
  - exact Hold.
  - exact Hnew.
  - exact Honesafe.
  - exact Hscan.
Qed.

Lemma propagation_unit_watch0_unprocessed__propagate_dbu :
  forall (n : Z) (assigns trail : list Z) (qhead watch0 : Z),
    lit_wf_c n watch0 ->
    (Znth (lit_var_c watch0) assigns 0 = lit_sig watch0 \/
     Znth (lit_var_c watch0) assigns 0 = 0) ->
    ~ minisat_processed n assigns trail qhead
        (literal_neg (lit_denote watch0)).
Proof.
  intros n assigns trail qhead watch0 Hwf Hcell Hprocessed.
  assert (Hnegwf : lit_wf_c n (lit_neg_c watch0)).
  { apply lit_neg_c_wf. exact Hwf. }
  assert (Hdenote : literal_neg (lit_denote watch0) =
      lit_denote (lit_neg_c watch0)).
  { symmetry. apply lit_denote_neg. destruct Hwf; lia. }
  rewrite Hdenote in Hprocessed.
  apply (proj1 (minisat_processed_denote n assigns trail qhead
    (lit_neg_c watch0) Hnegwf)) in Hprocessed.
  destruct Hprocessed as [Htrue Hposition].
  unfold lit_true in Htrue.
  rewrite lit_var_c_neg, lit_sig_neg in Htrue.
  destruct Hcell as [Hcell | Hcell]; rewrite Hcell in Htrue.
  - destruct (lit_sig_values watch0) as [Hsig | Hsig];
      rewrite Hsig in Htrue; lia.
  - destruct (lit_sig_values watch0) as [Hsig | Hsig];
      rewrite Hsig in Htrue; lia.
Qed.

Lemma propagation_unit_scan_semantics_unchanged__propagate_dbu :
  forall (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p watch0 current : Z) (new_lits kept suffix : list Z)
    (prob_after learnt_after : dbmap),
    solver_propagation_scan_semantics n F A_arr K M p 0
      kept (current :: suffix) ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update M prob_after learnt_after
        (ms_wm M)) ->
    minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    minisat_focus_scan_carrier (prob_after ++ learnt_after) p
      (minisat_processed n (mt_assigns (ms_core M))
        (mt_trail (ms_core M)) (mt_qhead (ms_core M)))
      (kept ++ (current :: nil)) suffix ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core M)) 0 =
      lit_sig watch0 ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_enqueue_success
        (msolver_propagation_db_wmap_update M prob_after learnt_after
          (ms_wm M))
        watch0 current (lits_denote new_lits))
      p 0 (kept ++ (current :: nil)) suffix.
Proof.
  intros n F A_arr K M p watch0 current new_lits kept suffix
    prob_after learnt_after Hsem Hweakdb Hfrontier Hcarrier Hcell.
  destruct Hsem as [Hlive | Hdead].
  2: { destruct Hdead as [Hnz _]. lia. }
  destruct Hlive as
    [Hconfl [Hweak [Hlevel [Hheap [Hcovers [Hreasonless
    [Hp_level [Hp_wf [Hprocessed [Hfrontier_old Hcarrier_old]]]]]]]]]].
  set (Mdb := msolver_propagation_db_wmap_update M prob_after learnt_after
    (ms_wm M)).
  assert (Hpost : msolver_propagation_enqueue_success Mdb watch0 current
      (lits_denote new_lits) = Mdb).
  {
    unfold Mdb, msolver_propagation_db_wmap_update,
      msolver_propagation_enqueue_success, msolver_propagation_overlay, msolver_propagation_update.
    cbn [ms_core mt_assigns].
    rewrite Hcell.
    destruct (lit_sig watch0 =? 0)%Z eqn:Hz; [|reflexivity].
    apply Z.eqb_eq in Hz. exfalso. exact (lit_sig_nonzero watch0 Hz).
  }
  rewrite Hpost.
  left. split; [reflexivity|].
  exact (conj Hweakdb (conj Hlevel (conj Hheap (conj Hcovers (conj Hreasonless
    (conj Hp_level (conj Hp_wf (conj Hprocessed (conj Hfrontier Hcarrier))))))))).
Qed.

(** ===== group: solver_propagate_db_update_enqueue_fresh ===== *)
Lemma propagation_enqueue_success_fresh__propagate_dbu :
  forall M l reason_word reason_clause,
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    msolver_propagation_enqueue_success M l reason_word reason_clause =
      msolver_enqueue_fresh M l reason_word (Some reason_clause).
Proof.
  intros M l reason_word reason_clause Hfresh.
  unfold msolver_propagation_enqueue_success, msolver_enqueue_fresh.
  rewrite Hfresh. reflexivity.
Qed.

Lemma propagation_unit_assigns_one_fresh__propagate_dbu :
  forall n M l reason_word words,
    mtrail_wf n (ms_core M) ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    Forall (lit_wf_c n) words ->
    assigns_one (msolver_view n M)
      (msolver_view n
        (msolver_enqueue_fresh M l reason_word (Some (lits_denote words))))
      (lit_var_c l) (lit_pol l) (Zlength (mt_lim (ms_core M)))
      (Some (lits_denote words)).
Proof.
  intros n M l reason_word words Htrailwf Hl Hfresh Hwords.
  unfold msolver_view, msolver_enqueue_fresh,
    msolver_propagation_overlay, msolver_propagation_update, msolver_db.
  cbn [ms_core ms_reason_of ms_prob ms_learnt].
  eapply view_of_assign.
  - exact Htrailwf.
  - exact Hl.
  - exact Hfresh.
  - intros y Hy. apply sat_function_update_neq.
    intro E. apply Hy. symmetry. exact E.
  - apply sat_function_update_eq.
  - intros C k HC Hk. inversion HC; subst C.
    apply lits_denote_in_inv in Hk.
    destruct Hk as [kw [Hkw <-]].
    apply lit_denote_wf.
    rewrite Forall_forall in Hwords. exact (Hwords kw Hkw).
Qed.

Lemma propagation_unit_reason_valid_fresh__propagate_dbu :
  forall n M l reason_word words,
    stable_view (msolver_view n M) ->
    mtrail_wf n (ms_core M) ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    Forall (lit_wf_c n) words ->
    2 <= Zlength words ->
    Znth 0 words 0 = l ->
    lit_false (mt_assigns (ms_core M)) (Znth 1 words 0) ->
    (forall j, 2 <= j < Zlength words ->
      lit_false (mt_assigns (ms_core M)) (Znth j words 0)) ->
    reason_valid
      (msolver_view n
        (msolver_enqueue_fresh M l reason_word (Some (lits_denote words))))
      (lit_var_c l) (lits_denote words).
Proof.
  intros n M l reason_word words Hstable Htrailwf Hl Hfresh Hwords
    Hlen Hhead Hfalse1 Hfalse_tail.
  pose proof
    (propagation_unit_assigns_one_fresh__propagate_dbu
      n M l reason_word words Htrailwf Hl Hfresh Hwords) as Hassign.
  eapply reason_valid_assigns_one__record.
  - exact Hstable.
  - exact Hassign.
  - reflexivity.
  - rewrite <- lit_denote_satisfying.
    apply lits_denote_in. rewrite <- Hhead. apply Znth_In. lia.
  - intros k Hk Hkne.
    apply lits_denote_in_inv in Hk.
    destruct Hk as [kw [Hkw Hden]]. subst k.
    rewrite lit_var_c_denote in Hkne.
    destruct (In_Znth_index words kw Hkw) as [j [Hj Hjval]].
    rewrite Forall_forall in Hwords.
    pose proof (Hwords kw Hkw) as Hkwf.
    assert (Hkw0 : 0 <= kw) by (destruct Hkwf; lia).
    assert (Hkwfalse : lit_false (mt_assigns (ms_core M)) kw).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - rewrite Hhead in Hjval. subst kw. contradiction.
      - destruct (Z.eq_dec j 1) as [->|Hj1].
        + rewrite Hjval in Hfalse1. exact Hfalse1.
        + pose proof (Hfalse_tail j ltac:(lia)) as Hjfalse.
          rewrite Hjval in Hjfalse. exact Hjfalse. }
    pose proof (proj1 (lit_false_iff
      (mt_assigns (ms_core M)) kw Hkw0) Hkwfalse) as Heval.
    change (eval_partial_literal (mt_pv (ms_core M))
      (lit_denote kw) = Some false).
    unfold eval_partial_literal in Heval |- *.
    rewrite lit_var_c_denote in Heval |- *.
    rewrite mt_pv_nonneg by
      (apply lit_var_c_nonneg with (n := n); exact Hkwf).
    exact Heval.
Qed.

Lemma propagation_unit_normalized_reason_properties__propagate_dbu :
  forall n F co new_words,
    obj_wf n co ->
    entails_clause F (denote_obj co) ->
    Permutation new_words (co_lits co) ->
    entails_clause F (lits_denote new_words) /\
    clause_var_injective (lits_denote new_words).
Proof.
  intros n F co new_words Hobj Hent Hperm.
  assert (Hpermden :
    Permutation (lits_denote new_words) (denote_obj co)).
  { unfold denote_obj. apply lits_denote_perm. exact Hperm. }
  split.
  - eapply entails_clause_perm.
    + apply Permutation_sym. exact Hpermden.
    + exact Hent.
  - apply NoDup_map_var_injective.
    rewrite map_literal_var_lits_denote.
    destruct Hobj as [Hlen [Hwf Hnodup]].
    eapply Permutation_NoDup.
    + apply Permutation_map. apply Permutation_sym. exact Hperm.
    + exact Hnodup.
Qed.

Lemma propagation_unit_trail_implied_fresh__propagate_dbu :
  forall n F t l words,
    mtrail_wf n t ->
    trail_implied F t ->
    entails_clause F (lits_denote words) ->
    Forall (lit_wf_c n) words ->
    2 <= Zlength words ->
    Znth 0 words 0 = l ->
    lit_false (mt_assigns t) (Znth 1 words 0) ->
    (forall j, 2 <= j < Zlength words ->
      lit_false (mt_assigns t) (Znth j words 0)) ->
    trail_implied F (mt_enqueue t l).
Proof.
  intros n F t l words Hwf Htrail Hent Hwords Hlen Hhead
    Hfalse1 Hfalse_tail.
  eapply trail_implied_unit with (rc := lits_denote words).
  - exact Hwf.
  - exact Htrail.
  - exact Hent.
  - apply lits_denote_in. rewrite <- Hhead. apply Znth_In. lia.
  - intros k Hk Hne.
    apply lits_denote_in_inv in Hk.
    destruct Hk as [kw [Hkw Hden]]. subst k.
    destruct (In_Znth_index words kw Hkw) as [j [Hj Hjval]].
    rewrite Forall_forall in Hwords.
    pose proof (Hwords kw Hkw) as Hkwf.
    assert (Hkw0 : 0 <= kw) by (destruct Hkwf; lia).
    assert (Hkwfalse : lit_false (mt_assigns t) kw).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - rewrite Hhead in Hjval. subst kw. contradiction.
      - destruct (Z.eq_dec j 1) as [->|Hj1].
        + rewrite Hjval in Hfalse1. exact Hfalse1.
        + pose proof (Hfalse_tail j ltac:(lia)) as Hjfalse.
          rewrite Hjval in Hjfalse. exact Hjfalse. }
    assert (Heval :
      eval_partial_literal (assigns_pv (mt_assigns t))
        (lit_denote kw) = Some false).
    { apply (proj1 (lit_false_iff (mt_assigns t) kw Hkw0)).
      exact Hkwfalse. }
    assert (Hnegtrue :
      eval_partial_literal (assigns_pv (mt_assigns t))
        (lit_denote (lit_neg_c kw)) = Some true).
    { apply (proj2 (lit_neg_true_iff_false (mt_assigns t) kw Hkw0)).
      exact Heval. }
    pose proof (lit_neg_c_wf n kw Hkwf) as Hnegwf.
    assert (Hlittrue : lit_true (mt_assigns t) (lit_neg_c kw)).
    { assert (Hneg0 : 0 <= lit_neg_c kw) by (destruct Hnegwf; lia).
      apply (proj2 (lit_true_iff
        (mt_assigns t) (lit_neg_c kw) Hneg0)). exact Hnegtrue. }
    destruct (mtrail_wf_trail_covers n t Hwf (lit_neg_c kw)
      Hnegwf Hlittrue) as [j' [Hj' Hjlit]].
    exists j'. split; [exact Hj'|]. rewrite Hjlit.
    apply lit_denote_neg. exact Hkw0.
Qed.

Lemma db_complete_enqueue_fresh_assuming__propagate_dbu :
  forall n F A_arr A_proc M l c reason,
    msolver_inv_assuming n F A_arr A_proc M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    db_complete F (msolver_enqueue_fresh M l c reason).
Proof.
  intros n F A_arr A_proc M l c reason Hinv Hl Hfresh.
  exact (db_complete_enqueue_fresh_core n F M l c reason
    (msa_db_complete Hinv) (msa_trail_wf Hinv) Hl Hfresh).
Qed.

Lemma propagation_unit_ctx_enqueue_fresh__propagate_dbu :
  forall n F A_arr K M l reason_word reason_clause,
    msolver_inv_ctx n F A_arr K M ->
    ms_capacity_root_propagation_pending M = 0 ->
    ms_qtail M < ms_cap M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    assigns_one (msolver_view n M)
      (msolver_view n
        (msolver_enqueue_fresh M l reason_word (Some reason_clause)))
      (lit_var_c l) (lit_pol l) (Zlength (mt_lim (ms_core M)))
      (Some reason_clause) ->
    reason_valid
      (msolver_view n
        (msolver_enqueue_fresh M l reason_word (Some reason_clause)))
      (lit_var_c l) reason_clause ->
    entails_clause F reason_clause ->
    clause_var_injective reason_clause ->
    trail_implied F (mt_enqueue (ms_core M) l) ->
    (exists co,
      reason_word <> 0 /\ Z.even reason_word = true /\
      List.In (reason_word, co) (msolver_db M) /\
      reason_clause = denote_obj co /\
      lit_var_c (co_watch0 co) = lit_var_c l) ->
    msolver_inv_ctx n F A_arr K
      (msolver_enqueue_fresh M l reason_word (Some reason_clause)).
Proof.
  intros n F A_arr K M l reason_word reason_clause Hinv Hpending
    Hroom Hl Hfresh Hassign Hvalid Hreasonent Hreasoninj Htrailimpl Hco.
  destruct Hco as [co [Hnz [Heven [Hin [Hclause Hwatch]]]]].
  assert (Hreasoncases :
    (reason_word = 0 /\ Some reason_clause = None) \/
    exists co', reason_word <> 0 /\ Z.even reason_word = true /\
      List.In (reason_word, co') (msolver_db M) /\
      Some reason_clause = Some (denote_obj co')).
  { right. exists co. split; [exact Hnz|]. split; [exact Heven|].
    split; [exact Hin|]. rewrite Hclause. reflexivity. }
  assert (Hheadcases : reason_word = 0 \/
    exists co', reason_word <> 0 /\ Z.even reason_word = true /\
      List.In (reason_word, co') (msolver_db M) /\
      lit_var_c (co_watch0 co') = lit_var_c l).
  { right. exists co. split; [exact Hnz|]. split; [exact Heven|].
    split; [exact Hin|exact Hwatch]. }
  destruct K as [A_inst|A_proc]; cbn [msolver_inv_ctx] in Hinv |- *;
    destruct Hinv; constructor.
  all: lazymatch goal with
       | |- solver_shape _ =>
           eapply solver_shape_enqueue_fresh__record;
             [assumption|exact Hroom|exact Hpending]
       | |- mtrail_wf _ _ =>
           cbn; eapply (mtrail_wf_enqueue n); [assumption|exact Hl|exact Hfresh]
       | |- trail_implied _ _ => cbn; exact Htrailimpl
       | |- stable_view _ =>
           eapply (stable_view_assigns_one__record (msolver_view n M));
             [assumption|exact Hassign|reflexivity
             |split; [apply Zlength_nonneg|reflexivity]
             |right; exists reason_clause; split; [reflexivity|exact Hvalid]]
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- reasons_entailed _ _ =>
           eapply reasons_entailed_assigns_one__record;
             [exact Hassign|assumption
             |right; exists reason_clause; split; [reflexivity|exact Hreasonent]]
       | |- reasons_var_injective _ =>
           eapply reasons_var_injective_assigns_one__record;
             [exact Hassign|assumption
             |right; exists reason_clause; split; [reflexivity|exact Hreasoninj]]
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- db_complete _ _ =>
           eapply (db_complete_enqueue_fresh_core n);
             [assumption|assumption|exact Hl|exact Hfresh]
       | |- reasons_match _ _ _ _ _ =>
           eapply (reasons_match_enqueue_fresh_core n);
             [assumption|assumption|assumption|exact Hl|exact Hfresh
             |exact Hreasoncases]
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- reason_head_ok _ =>
           eapply (reason_head_ok_enqueue_fresh_core n);
             [assumption|assumption|assumption|assumption|exact Hl
             |exact Hheadcases]
       | |- binary_reason_same_level _ =>
           eapply (binary_reason_same_level_enqueue_fresh_core n);
             [assumption|assumption|assumption|assumption|assumption
             |assumption|exact Hl|exact Hfresh|right; exact Heven]
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- decisions_upto _ _ = _ =>
           cbn; rewrite (decisions_upto_enqueue n (ms_core M) l) by assumption;
           assumption
       | |- (exists _, _) =>
           lazymatch goal with
           | H : (exists _, _) |- _ => destruct H as [A_x [Hdec Hincl]]
           end;
           exists A_x; split; [|exact Hincl];
           cbn; rewrite (decisions_upto_enqueue n (ms_core M) l) by assumption;
           exact Hdec
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- Forall (assump_true_at_root _ _) _ =>
           cbn; rewrite List.Forall_forall; intros a Ha;
           eapply (assump_true_at_root_enqueue__record n);
             [assumption|exact Hl|exact Hfresh|];
           lazymatch goal with
           | H : Forall (assump_true_at_root _ _) _ |- _ =>
               rewrite List.Forall_forall in H; exact (H a Ha)
           end
       | _ => idtac
       end.
  all: cbn; assumption.
Qed.

Lemma processed_enqueue_fresh_equiv__propagate_dbu :
  forall n t q,
    mtrail_wf n t ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
    (forall w, lit_wf_c n w ->
      processed (mt_assigns (mt_enqueue t q))
        (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q)) w ->
      processed (mt_assigns t) (mt_trail t) (mt_qhead t) w) /\
    (forall w, lit_wf_c n w ->
      processed (mt_assigns t) (mt_trail t) (mt_qhead t) w ->
      processed (mt_assigns (mt_enqueue t q))
        (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q)) w).
Proof.
  intros n t q Hwf Hqwf Hfresh.
  assert (Hqrange : 0 <= lit_var_c q < n).
  { apply lit_var_c_in_range. exact Hqwf. }
  split.
  - intros w Hwwf [Hwtrue [i [Hi Hiw]]].
    unfold mt_enqueue, mt_push in Hwtrue, Hi, Hiw.
    cbn [mt_assigns mt_trail mt_qhead] in Hwtrue, Hi, Hiw.
    assert (Hiold : 0 <= i < Zlength (mt_trail t)).
    { split; [exact (proj1 Hi)|].
      eapply Z.lt_le_trans; [exact (proj2 Hi)|].
      exact (proj2 (mtw_qhead_range Hwf)). }
    rewrite app_Znth1 in Hiw by exact Hiold.
    assert (Hwq : lit_var_c w <> lit_var_c q).
    { intro E.
      assert (Hinw : In w (mt_trail t)).
      { rewrite <- Hiw. apply Znth_In. exact Hiold. }
      pose proof (mtw_trail_true Hwf) as Htruecells.
      rewrite List.Forall_forall in Htruecells.
      specialize (Htruecells w Hinw).
      rewrite E, Hfresh in Htruecells.
      apply (lit_sig_nonzero w). symmetry. exact Htruecells. }
    split.
    + unfold lit_true in *.
      rewrite Znth_replace_Znth_Diff in Hwtrue.
      * exact Hwtrue.
      * rewrite (mtw_assigns_len Hwf). exact Hqrange.
      * rewrite (mtw_assigns_len Hwf).
        exact (lit_var_c_in_range n w Hwwf).
      * intro E. apply Hwq. symmetry. exact E.
    + exists i. split; [exact Hi|exact Hiw].
  - intros w Hwwf [Hwtrue [i [Hi Hiw]]].
    assert (Hiold : 0 <= i < Zlength (mt_trail t)).
    { split; [exact (proj1 Hi)|].
      eapply Z.lt_le_trans; [exact (proj2 Hi)|].
      exact (proj2 (mtw_qhead_range Hwf)). }
    assert (Hwq : lit_var_c w <> lit_var_c q).
    { intro E.
      assert (Hinw : In w (mt_trail t)).
      { rewrite <- Hiw. apply Znth_In. exact Hiold. }
      pose proof (mtw_trail_true Hwf) as Htruecells.
      rewrite List.Forall_forall in Htruecells.
      specialize (Htruecells w Hinw).
      rewrite E, Hfresh in Htruecells.
      apply (lit_sig_nonzero w). symmetry. exact Htruecells. }
    unfold mt_enqueue, mt_push.
    cbn [mt_assigns mt_trail mt_qhead].
    split.
    + unfold lit_true in *.
      rewrite Znth_replace_Znth_Diff.
      * exact Hwtrue.
      * rewrite (mtw_assigns_len Hwf). exact Hqrange.
      * rewrite (mtw_assigns_len Hwf).
        exact (lit_var_c_in_range n w Hwwf).
      * intro E. apply Hwq. symmetry. exact E.
    + exists i. split; [exact Hi|].
      rewrite app_Znth1; [exact Hiw|exact Hiold].
Qed.

Lemma minisat_watch_frontier_except_enqueue_fresh__propagate_dbu :
  forall n db t q focus,
    mtrail_wf n t ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
    minisat_watch_frontier_except n db
      (mt_assigns t) (mt_trail t) (mt_qhead t) focus ->
    minisat_watch_frontier_except n db
      (mt_assigns (mt_enqueue t q))
      (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q)) focus.
Proof.
  intros n db t q focus Hwf Hqwf Hfresh Hfrontier.
  destruct (processed_enqueue_fresh_equiv__propagate_dbu
    n t q Hwf Hqwf Hfresh) as [Hreverse Hforward].
  assert (Hmini_reverse : forall l,
    minisat_processed n (mt_assigns (mt_enqueue t q))
      (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q)) l ->
    minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t) l).
  { intros l [w [Hwwf [Hden Hproc]]].
    exists w. split; [exact Hwwf|]. split; [exact Hden|].
    apply Hreverse; assumption. }
  unfold minisat_watch_frontier_except in *.
  unfold watch_frontier_except in *.
  rewrite Forall_forall in Hfrontier |- *.
  intros o Ho. specialize (Hfrontier o Ho).
  destruct Hfrontier as [Hsafe | Hfocus].
  - left. intros [Hleft Hright]. apply Hsafe. split;
      apply Hmini_reverse; assumption.
  - right. exact Hfocus.
Qed.

Lemma minisat_focus_scan_carrier_enqueue_fresh__propagate_dbu :
  forall n db t q p kept suffix,
    mtrail_wf n t ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
    minisat_focus_scan_carrier db p
      (minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t))
      kept suffix ->
    minisat_focus_scan_carrier db p
      (minisat_processed n (mt_assigns (mt_enqueue t q))
        (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q)))
      kept suffix.
Proof.
  intros n db t q p kept suffix Hwf Hqwf Hfresh Hcarrier.
  destruct (processed_enqueue_fresh_equiv__propagate_dbu
    n t q Hwf Hqwf Hfresh) as [Hreverse Hforward].
  assert (Hmini_reverse : forall l,
    minisat_processed n (mt_assigns (mt_enqueue t q))
      (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q)) l ->
    minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t) l).
  { intros l [w [Hwwf [Hden Hproc]]].
    exists w. split; [exact Hwwf|]. split; [exact Hden|].
    apply Hreverse; assumption. }
  unfold minisat_focus_scan_carrier in Hcarrier |- *.
  destruct Hcarrier as [scanned [pending [Hperm [Hscanned [Hpending Hsafe]]]]].
  exists scanned, pending. split; [exact Hperm|].
  split; [exact Hscanned|]. split; [exact Hpending|].
  revert Hsafe. apply Forall_impl.
  intros occurrence Hsafe Hboth. apply Hsafe.
  split.
  - apply Hmini_reverse. exact (proj1 Hboth).
  - apply Hmini_reverse. exact (proj2 Hboth).
Qed.

Lemma current_reasonless_enqueue_fresh__propagate_dbu :
  forall n M l reason_word reason_clause,
    solver_shape M ->
    mtrail_wf n (ms_core M) ->
    lit_wf_c n l ->
    reason_word <> 0 ->
    current_reasonless_earliest n M ->
    assigns_one (msolver_view n M)
      (msolver_view n
        (msolver_enqueue_fresh M l reason_word (Some reason_clause)))
      (lit_var_c l) (lit_pol l) (Zlength (mt_lim (ms_core M)))
      (Some reason_clause) ->
    current_reasonless_earliest n
      (msolver_enqueue_fresh M l reason_word (Some reason_clause)).
Proof.
  intros n M l reason_word reason_clause Hshape Htrailwf Hl Hwordnz Hold
    Hassign.
  unfold current_reasonless_earliest in Hold |- *.
  intros d Hrange v Hlevel Hwordzero.
  destruct Hassign as [_ [_ [_ [_ [_ [Hother _]]]]]].
  pose proof (mtw_assigns_len Htrailwf) as Hassignlen.
  change (ms_root_level M < d <= Zlength (mt_lim (ms_core M))) in Hrange.
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hvne].
  - assert (Htarget :
      0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update in Hwordzero.
    cbn [ms_reason_words] in Hwordzero.
    rewrite Znth_replace_Znth_Same in Hwordzero by exact Htarget.
    contradiction.
  - destruct (Hother v Hvne) as [Ha [Hlev [Hreason Hrankeq]]].
    rewrite Hlev in Hlevel.
    assert (Hv : 0 <= v < n).
    { unfold msolver_view, view_of in Hlevel.
      cbn [level_of] in Hlevel.
      destruct (trail_pos (ms_core M) v) as [k|] eqn:Hpos;
        cbn [option_map] in Hlevel; [|discriminate].
      apply find_var_pos_some_in in Hpos.
      apply trail_var_range with (t := ms_core M); assumption. }
    assert (Htarget :
      0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    assert (Hvr : 0 <= v < Zlength (ms_reason_words M)).
    { unfold solver_shape in Hshape. lia. }
    unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update in Hwordzero.
    cbn [ms_reason_words] in Hwordzero.
    rewrite Znth_replace_Znth_Diff in Hwordzero.
    2: { exact Htarget. } 2: { exact Hvr. } 2: { congruence. }
    destruct (Hold d Hrange v Hlevel Hwordzero) as [Hr Hrank].
    split.
    + unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update.
      cbn [ms_reason_of]. rewrite sat_function_update_neq.
      * exact Hr.
      * intro E. apply Hvne. symmetry. exact E.
    + rewrite Hrankeq. exact Hrank.
Qed.

Lemma propagation_unit_scan_semantics_fresh__propagate_dbu :
  forall n F A_arr K M Mdb Mpost p q current reason_clause
    retained suffix retained_after prob_after learnt_after,
    Mdb = msolver_propagation_db_wmap_update M prob_after learnt_after
      (ms_wm M) ->
    Mpost = msolver_enqueue_fresh Mdb q current (Some reason_clause) ->
    solver_propagation_scan_semantics n F A_arr K M p 0
      retained (current :: suffix) ->
    solver_propagation_weak n F A_arr K Mdb ->
    minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    minisat_focus_scan_carrier (prob_after ++ learnt_after) p
      (minisat_processed n (mt_assigns (ms_core M))
        (mt_trail (ms_core M)) (mt_qhead (ms_core M)))
      retained_after suffix ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 = 0 ->
    assigns_one (msolver_view n Mdb) (msolver_view n Mpost)
      (lit_var_c q) (lit_pol q) (Zlength (mt_lim (ms_core Mdb)))
      (Some reason_clause) ->
    solver_propagation_weak n F A_arr K Mpost ->
    current_reasonless_earliest n Mpost ->
    solver_propagation_scan_semantics n F A_arr K Mpost p 0
      retained_after suffix.
Proof.
  intros n F A_arr K M Mdb Mpost p q current reason_clause retained suffix
    retained_after prob_after learnt_after HMdb HMpost Hsem Hweakdb Hfrontier
    Hcarrier Hqwf Hfresh Hassign Hweakpost Hreasonlesspost.
  destruct Hsem as [Hlive | Hdead].
  2: { destruct Hdead as [Hnz _]. lia. }
  destruct Hlive as
    [Hzero [Hweak [Hlevel [Hheap [Hcovers [Hreasonless
    [Hp_level [Hp_wf [Hprocessed [Hfrontier_old Hcarrier_old]]]]]]]]]].
  assert (Htrailwf : mtrail_wf n (ms_core M)).
  { unfold solver_propagation_weak in Hweak.
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_trail_wf (proj2 Hweak)).
    - exact (msa_trail_wf (proj2 Hweak)). }
  assert (Hprocessed_new : processed
    (mt_assigns (ms_core Mpost)) (mt_trail (ms_core Mpost))
    (mt_qhead (ms_core Mpost)) p).
  { subst Mpost Mdb.
    destruct (processed_enqueue_fresh_equiv__propagate_dbu
      n (ms_core M) q Htrailwf Hqwf Hfresh) as [Hreverse Hforward].
    apply Hforward; [exact Hp_wf|exact Hprocessed]. }
  assert (Hfrontier_new : minisat_watch_frontier_except n
    (msolver_db Mpost) (mt_assigns (ms_core Mpost))
    (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)) (lit_denote p)).
  { subst Mpost Mdb.
    change (minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (mt_enqueue (ms_core M) q))
      (mt_trail (mt_enqueue (ms_core M) q))
      (mt_qhead (mt_enqueue (ms_core M) q)) (lit_denote p)).
    eapply minisat_watch_frontier_except_enqueue_fresh__propagate_dbu;
      eassumption. }
  assert (Hcarrier_new : minisat_focus_scan_carrier
    (msolver_db Mpost) p
    (minisat_processed n (mt_assigns (ms_core Mpost))
      (mt_trail (ms_core Mpost)) (mt_qhead (ms_core Mpost)))
    retained_after suffix).
  { subst Mpost Mdb.
    change (minisat_focus_scan_carrier (prob_after ++ learnt_after) p
      (minisat_processed n (mt_assigns (mt_enqueue (ms_core M) q))
        (mt_trail (mt_enqueue (ms_core M) q))
        (mt_qhead (mt_enqueue (ms_core M) q))) retained_after suffix).
    eapply minisat_focus_scan_carrier_enqueue_fresh__propagate_dbu;
      eassumption. }
  assert (Hcovers_new : heap_covers n (msolver_heap Mpost)
    (mt_assigns (ms_core Mpost)) (mt_trail (ms_core Mpost))
    (mt_qhead (ms_core Mpost))).
  { subst Mpost Mdb.
    change (heap_covers n (msolver_heap M)
      (mt_assigns (mt_enqueue (ms_core M) q))
      (mt_trail (mt_enqueue (ms_core M) q))
      (mt_qhead (mt_enqueue (ms_core M) q))).
    eapply heap_covers_enqueue_fresh__record;
      [exact Htrailwf|exact Hqwf|exact Hcovers]. }
  assert (Hp_level_new : level_of (msolver_view n Mpost) (lit_var_c p) =
    Some (Zlength (mt_lim (ms_core Mpost)))).
  { destruct Hassign as [_ [_ [_ [_ [_ [Hother _]]]]]].
    assert (Hqneq : lit_var_c q <> lit_var_c p).
    { exact (processed_fresh_target_different
        (mt_assigns (ms_core M)) (mt_trail (ms_core M))
        (mt_qhead (ms_core M)) p q Hprocessed Hfresh). }
    destruct (Hother (lit_var_c p) (fun E => Hqneq (eq_sym E)))
      as [_ [Hlevelp _]].
    assert (Hp_level_db : level_of (msolver_view n Mdb) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mdb)))).
    { subst Mdb. exact Hp_level. }
    rewrite Hlevelp, Hp_level_db. subst Mpost. reflexivity. }
  left. split; [reflexivity|].
  split; [exact Hweakpost|].
  split.
  - subst Mpost Mdb. change (prop_level (mt_enqueue (ms_core M) q)).
    apply prop_level_enqueue. exact Hlevel.
  - split.
    + left. exact Hcovers_new.
    + split; [exact Hcovers_new|].
      split; [exact Hreasonlesspost|].
      split; [exact Hp_level_new|].
      split; [exact Hp_wf|].
      split; [exact Hprocessed_new|].
      split; [exact Hfrontier_new|exact Hcarrier_new].
Qed.

Lemma solver_propagation_weak_selected_entailed__propagate_dbu :
  forall n F A_arr K M current co,
    solver_propagation_weak n F A_arr K M ->
    In (current, co) (msolver_db M) ->
    entails_clause F (denote_obj co).
Proof.
  intros n F A_arr K M current co Hweak Hin.
  unfold solver_propagation_weak in Hweak.
  destruct K as [A_inst | A_proc]; destruct Hweak as [Hpending Hinv].
  - eapply (msolver_inv_db_entailed n F A_arr A_inst M Hinv).
    rewrite msolver_view_installed.
    unfold msolver_clauses.
    apply db_clauses_in with (p := current). exact Hin.
  - unfold msolver_db in Hin. apply in_app_or in Hin.
    destruct Hin as [Hprob | Hlearnt].
    + pose proof (msa_db_matches Hinv) as Hmatches.
      unfold db_matches_cnf in Hmatches.
      rewrite Forall_forall in Hmatches.
      assert (Hclause : In (denote_obj co) (db_clauses (ms_prob M))).
      { apply db_clauses_in with (p := current). exact Hprob. }
      destruct (Hmatches (denote_obj co) Hclause) as [c0 [Hin0 Hperm]].
      eapply entails_clause_perm.
      * apply Permutation_sym. exact Hperm.
      * apply entails_clause_in. exact Hin0.
    + pose proof (msa_db_implied Hinv) as Himplied.
      unfold db_implied in Himplied. rewrite Forall_forall in Himplied.
      apply Himplied. apply db_clauses_in with (p := current). exact Hlearnt.
Qed.

Lemma db_pair_lits_update_selected_owner__propagate_dbu :
  forall prob learnt current old_lits new_lits prob_after learnt_after,
    db_pair_lits_update prob learnt current old_lits new_lits
      prob_after learnt_after ->
    exists co_after,
      In (current, co_after) (prob_after ++ learnt_after) /\
      co_lits co_after = new_lits.
Proof.
  intros prob learnt current old_lits new_lits prob_after learnt_after Hupdate.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [co [pre [post [_ [Hafter _]]]]].
  exists (clause_obj_with_lits co new_lits). split; [|reflexivity].
  rewrite Hafter. apply in_or_app. right. left. reflexivity.
Qed.

Lemma propagation_unit_keep_step__propagate_dbu :
  forall source retained moved rest garbage memory ii jj current suffix,
    rest = current :: suffix ->
    propagation_watch_scan_physical source retained moved rest garbage memory
      ii jj ->
    exists garbage_after memory_after,
      propagation_scan_keep_step source retained moved rest memory ii jj current
        (retained ++ current :: nil) suffix garbage_after memory_after.
Proof.
  intros source retained moved rest garbage memory ii jj current suffix Hrest
    Hphysical.
  unfold propagation_watch_scan_physical in Hphysical.
  destruct Hphysical as
    [Hscan [Hmemory [Hretlen [Hprefixlen Hmemorylen]]]].
  subst rest.
  destruct garbage as [|g gs].
  - exists nil, memory.
    unfold propagation_scan_keep_step.
    split; [reflexivity|]. split; [reflexivity|]. split.
    + assert (Hnth : Znth jj memory 0 = current).
      { rewrite Hmemory.
        rewrite app_Znth2 by (rewrite Hretlen; lia).
        replace (jj - Zlength retained) with 0 by lia. reflexivity. }
      rewrite <- Hnth. symmetry. apply replace_Znth_Znth.
    + unfold propagation_watch_scan_physical.
      split; [apply wlist_scan_keep; exact Hscan|]. split.
      * rewrite Hmemory.
        change (retained ++ (current :: suffix) =
          (retained ++ (current :: nil)) ++ suffix).
        rewrite <- app_assoc. reflexivity.
      * split.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil, Hretlen. lia.
        -- split.
           ++ rewrite app_nil_r in Hprefixlen.
              rewrite !Zlength_app. cbn. rewrite Hretlen. lia.
           ++ exact Hmemorylen.
  - exists (gs ++ current :: nil), (replace_Znth jj current memory).
    unfold propagation_scan_keep_step.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold propagation_watch_scan_physical.
    split; [apply wlist_scan_keep; exact Hscan|]. split.
    + rewrite Hmemory.
      rewrite replace_Znth_app_r by (rewrite Hretlen; lia).
      rewrite replace_Znth_nothing by lia.
      replace (jj - Zlength retained) with 0 by lia. cbn.
      rewrite <- !app_assoc. reflexivity.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil, Hretlen. lia.
      * split.
        -- rewrite !Zlength_app in Hprefixlen |- *.
           rewrite !Zlength_app_cons. rewrite Zlength_cons in Hprefixlen. lia.
        -- rewrite Zlength_replace_Znth. exact Hmemorylen.
Qed.

Lemma propagation_unit_fresh_success_semantics__propagate_dbu :
  forall n F A_arr K M Mdb p watch0 current old_lits new_lits retained suffix
    prob_after learnt_after co,
    Mdb = msolver_propagation_db_wmap_update M prob_after learnt_after
      (ms_wm M) ->
    solver_propagation_scan_semantics n F A_arr K M p 0
      retained (current :: suffix) ->
    solver_propagation_weak n F A_arr K M ->
    solver_propagation_weak n F A_arr K Mdb ->
    db_wf n (msolver_db M) ->
    In (current, co) (msolver_db M) ->
    Permutation new_lits (co_lits co) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current old_lits new_lits
      prob_after learnt_after ->
    Forall (lit_wf_c n) new_lits ->
    3 <= Zlength new_lits ->
    Znth 0 new_lits 0 = watch0 ->
    lit_false (mt_assigns (ms_core M)) (Znth 1 new_lits 0) ->
    (forall j, 2 <= j < Zlength new_lits ->
      lit_false (mt_assigns (ms_core M)) (Znth j new_lits 0)) ->
    minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    minisat_focus_scan_carrier (prob_after ++ learnt_after) p
      (minisat_processed n (mt_assigns (ms_core M))
        (mt_trail (ms_core M)) (mt_qhead (ms_core M)))
      (retained ++ current :: nil) suffix ->
    lit_wf_c n watch0 ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core M)) 0 = 0 ->
    ms_qtail Mdb < ms_cap Mdb ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_enqueue_success Mdb watch0 current
        (lits_denote new_lits)) p 0 (retained ++ current :: nil) suffix.
Proof.
  intros n F A_arr K M Mdb p watch0 current old_lits new_lits retained
    suffix prob_after learnt_after co HMdb Hsem Hweak Hweakdb Hdbwf Hin
    Hperm Hupdate Hwords Hlong Hhead Hfalse1 Hfalse_tail Hfrontier Hcarrier
    Hwatchwf Hfresh Hroom.
  pose proof Hsem as Hsem0.
  destruct Hsem0 as [Hlive | Hdead].
  2: { destruct Hdead as [Hnz _]. lia. }
  destruct Hlive as
    [Hzero [Hweak0 [Hlevel [Hheap [Hcovers [Hreasonless
    [Hp_level [Hp_wf [Hprocessed [Hfrontier0 Hcarrier0]]]]]]]]]].
  assert (Hcore : solver_shape Mdb /\ mtrail_wf n (ms_core Mdb) /\
    stable_view (msolver_view n Mdb) /\ trail_implied F (ms_core Mdb)).
  { unfold solver_propagation_weak in Hweakdb.
    destruct K as [A_inst | A_proc]; cbn in Hweakdb.
    - destruct Hweakdb as [_ Hinv].
      split; [exact (msw_shape Hinv)|]. split; [exact (msw_trail_wf Hinv)|].
      split; [exact (msw_stable Hinv)|exact (msw_trail_impl Hinv)].
    - destruct Hweakdb as [_ Hinv].
      split; [exact (msa_shape Hinv)|]. split; [exact (msa_trail_wf Hinv)|].
      split; [exact (msa_stable Hinv)|exact (msa_trail_impl Hinv)]. }
  destruct Hcore as [Hshape [Htrailwf [Hstable Htrailimpl]]].
  assert (Hdbwfdb : db_wf n (msolver_db Mdb)).
  { unfold solver_propagation_weak in Hweakdb.
    destruct K as [A_inst | A_proc]; cbn in Hweakdb.
    - exact (msw_db_wf (proj2 Hweakdb)).
    - exact (msa_db_wf (proj2 Hweakdb)). }
  set (Mpost := msolver_enqueue_fresh Mdb watch0 current
    (Some (lits_denote new_lits))).
  assert (Hfreshdb :
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mdb)) 0 = 0).
  { rewrite HMdb. unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hfresh. }
  assert (Hassign : assigns_one (msolver_view n Mdb) (msolver_view n Mpost)
    (lit_var_c watch0) (lit_pol watch0) (Zlength (mt_lim (ms_core Mdb)))
    (Some (lits_denote new_lits))).
  { unfold Mpost. eapply propagation_unit_assigns_one_fresh__propagate_dbu;
      [exact Htrailwf|exact Hwatchwf|exact Hfreshdb|exact Hwords]. }
  assert (Hselectedent : entails_clause F (denote_obj co)).
  { eapply solver_propagation_weak_selected_entailed__propagate_dbu;
      [exact Hweak|exact Hin]. }
  destruct (propagation_unit_normalized_reason_properties__propagate_dbu
    n F co new_lits (db_wf_obj n (msolver_db M) current co Hdbwf Hin)
    Hselectedent Hperm) as [Hreasonent Hreasoninj].
  assert (Hfalse1db :
    lit_false (mt_assigns (ms_core Mdb)) (Znth 1 new_lits 0)).
  { rewrite HMdb. unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hfalse1. }
  assert (Hfalse_taildb : forall j, 2 <= j < Zlength new_lits ->
    lit_false (mt_assigns (ms_core Mdb)) (Znth j new_lits 0)).
  { intros j Hj. rewrite HMdb. unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update. cbn. apply Hfalse_tail. exact Hj. }
  assert (Hvalid : reason_valid (msolver_view n Mpost)
    (lit_var_c watch0) (lits_denote new_lits)).
  { unfold Mpost. eapply propagation_unit_reason_valid_fresh__propagate_dbu;
      [exact Hstable|exact Htrailwf|exact Hwatchwf|exact Hfreshdb|exact Hwords|
       lia|exact Hhead|exact Hfalse1db|exact Hfalse_taildb]. }
  assert (Htrailimpl' : trail_implied F (mt_enqueue (ms_core Mdb) watch0)).
  { eapply propagation_unit_trail_implied_fresh__propagate_dbu;
      [exact Htrailwf|exact Htrailimpl|exact Hreasonent|exact Hwords|lia|
       exact Hhead|exact Hfalse1db|exact Hfalse_taildb]. }
  destruct (db_pair_lits_update_selected_owner__propagate_dbu
    _ _ _ _ _ _ _ Hupdate) as [co_after [Hin_after Hco_after]].
  assert (Hin_after_db : In (current, co_after) (msolver_db Mdb)).
  { rewrite HMdb. unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update, msolver_db. cbn. exact Hin_after. }
  assert (Hcurrentpos : 0 < current).
  { eapply db_wf_ptr_pos; [exact Hdbwfdb|exact Hin_after_db]. }
  assert (Hcurrenteven : Z.even current = true).
  { eapply db_wf_even; [exact Hdbwfdb|exact Hin_after_db]. }
  assert (Howner : exists co', current <> 0 /\ Z.even current = true /\
    In (current, co') (msolver_db Mdb) /\ lits_denote new_lits = denote_obj co' /\
    lit_var_c (co_watch0 co') = lit_var_c watch0).
  { exists co_after. split; [lia|].
    split; [exact Hcurrenteven|]. split.
    - exact Hin_after_db.
    - split.
      + unfold denote_obj. rewrite Hco_after. reflexivity.
      + unfold co_watch0. rewrite Hco_after, Hhead. reflexivity. }
  assert (Hweakpost : solver_propagation_weak n F A_arr K Mpost).
  { unfold solver_propagation_weak in Hweakdb |- *.
    split; [unfold Mpost, msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update;
      cbn; exact (proj1 Hweakdb)|].
    eapply (propagation_unit_ctx_enqueue_fresh__propagate_dbu n F A_arr K Mdb);
      [exact (proj2 Hweakdb)|exact (proj1 Hweakdb)|exact Hroom|exact Hwatchwf|
       exact Hfreshdb|exact Hassign|exact Hvalid|exact Hreasonent|exact Hreasoninj|
       exact Htrailimpl'|exact Howner]. }
  assert (Hreasonlessdb : current_reasonless_earliest n Mdb).
  { subst Mdb. exact Hreasonless. }
  assert (Hreasonlesspost : current_reasonless_earliest n Mpost).
  { unfold Mpost. eapply current_reasonless_enqueue_fresh__propagate_dbu;
      [exact Hshape|exact Htrailwf|exact Hwatchwf|
       lia|exact Hreasonlessdb|exact Hassign]. }
  assert (Hfreshsem : solver_propagation_scan_semantics n F A_arr K Mpost p 0
    (retained ++ current :: nil) suffix).
  { eapply propagation_unit_scan_semantics_fresh__propagate_dbu
      with (M := M) (Mdb := Mdb) (q := watch0) (current := current)
        (reason_clause := lits_denote new_lits) (retained := retained)
        (prob_after := prob_after) (learnt_after := learnt_after).
    - exact HMdb.
    - reflexivity.
    - exact Hsem.
    - exact Hweakdb.
    - exact Hfrontier.
    - exact Hcarrier.
    - exact Hwatchwf.
    - exact Hfresh.
    - exact Hassign.
    - exact Hweakpost.
    - exact Hreasonlesspost. }
  unfold Mpost in Hfreshsem.
  rewrite <- propagation_enqueue_success_fresh__propagate_dbu
    in Hfreshsem by exact Hfreshdb. exact Hfreshsem.
Qed.

(** ===== group: solver_propagate_db_update_migrated_arm ===== *)
(** The MIGRATED arm.  The scan found a new literal to watch, so the entry
    leaves this watch list for another one. *)
Lemma focus_scan_carrier_db_pair_token_remove__propagate_dbu :
  forall n olddb newdb p P kept rest current co pre post,
    db_wf n olddb ->
    In (current, co) olddb ->
    is_tag current = false ->
    minisat_focus_contributions olddb p =
      pre ++ (minisat_occurrence_of_entry (current, co), current) :: post ->
    minisat_focus_contributions newdb p = pre ++ post ->
    minisat_focus_scan_carrier olddb p P kept (current :: rest) ->
    minisat_focus_scan_carrier newdb p P kept rest.
Proof.
  intros n olddb newdb p P kept rest current co pre post
    Hdb Hselected Hreal Hold Hnew Hscan.
  destruct (focus_scan_carrier_pop_real__propagate_dbu
    n olddb p P kept rest current co pre post Hdb Hselected Hreal Hold Hscan)
    as [scanned [pending [Hbase [Hkept [Hrest Hsafe]]]]].
  unfold minisat_focus_scan_carrier. exists scanned, pending. rewrite Hnew.
  repeat split; assumption.
Qed.

Lemma propagation_real_migrated_exit_intro__propagate_dbu :
  forall n F A_arr K M0 Mentry M Mroute p prob learnt wm
    candidate current source
    retained moved rest memory ii jj moved' rest' garbage' memory'
    simp_count prop_count,
    Mroute = msolver_propagation_db_wmap_update M prob learnt
      (propagation_move_wmap p (lit_neg_c candidate) wm
        (retained ++ rest') current) ->
    propagation_scan_move_step source retained moved rest memory ii jj current
      moved' rest' garbage' ->
    solver_shape Mroute ->
    msolver_seed_shadow Mroute ->
    propagation_caller_frame M0 Mroute ->
    propagation_scan_frontier Mentry Mroute p ->
    solver_propagation_scan_semantics n F A_arr K Mroute p 0 retained rest' ->
    simp_count = ms_simpdb_props Mroute ->
    prop_count = stats_propagations (ms_stats Mroute) ->
    memory' = memory ->
    propagation_watch_scan_physical source retained moved' rest' garbage'
      memory' (ii + 1) jj ->
    ms_wm Mroute =
      replace_Znth p (retained ++ rest')
        (replace_Znth (lit_neg_c candidate)
           (Znth (lit_neg_c candidate) wm nil ++ [current]) wm) ->
    propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry M Mroute p
      prob learnt wm
      candidate current source retained moved rest memory ii jj moved' rest'
      garbage' memory' simp_count prop_count.
Proof.
  intros n F A_arr K M0 Mentry M Mroute p prob learnt wm
    candidate current source
    retained moved rest memory ii jj moved' rest' garbage' memory'
    simp_count prop_count HMroute Hstep Hshape Hseed Hcaller Hfrontier Hsem
    Hsimp Hprop Hmemory Hphysical Hwm.
  unfold propagation_real_migrated_exit_carrier.
  split; [exact HMroute|]. split.
  - unfold propagation_real_migrated_transition. split; assumption.
  - split; [exact Hstep|]. split; [exact Hshape|]. split; [exact Hseed|].
    split; [exact Hcaller|]. split; [exact Hfrontier|]. split; [exact Hsem|].
    split; [exact Hsimp|]. split; [exact Hprop|]. split; [exact Hmemory|].
    split; [exact Hphysical|]. exact Hwm.
Qed.

Lemma propagation_migrated_physical_step__propagate_dbu :
  forall source retained moved rest garbage memory candidate_memory
    migration_memory raw ii jj current,
    rest = current :: raw ->
    propagation_watch_scan_physical source retained moved rest garbage
      memory ii jj ->
    candidate_memory = memory ->
    Znth ii candidate_memory 0 = current ->
    migration_memory = replace_Znth ii (Znth ii candidate_memory 0)
      candidate_memory ->
    migration_memory = memory /\
    propagation_scan_move_step source retained moved rest memory ii jj current
      (moved ++ [current]) raw (garbage ++ [current]) /\
    propagation_watch_scan_physical source retained (moved ++ [current]) raw
      (garbage ++ [current]) migration_memory (ii + 1) jj.
Proof.
  intros source retained moved rest garbage memory candidate_memory
    migration_memory raw ii jj current Hrest Hphysical Hcandidate Hnth
    Hmigration.
  assert (Hmemory : migration_memory = memory).
  { subst candidate_memory. rewrite Hnth in Hmigration.
    rewrite <- Hnth in Hmigration.
    rewrite replace_Znth_Znth in Hmigration. exact Hmigration. }
  assert (Hstep : propagation_scan_move_step source retained moved rest memory
      ii jj current (moved ++ [current]) raw (garbage ++ [current])).
  { unfold propagation_scan_move_step. split; [exact Hrest|].
    split; [reflexivity|]. subst rest.
    unfold propagation_watch_scan_physical in Hphysical |- *.
    destruct Hphysical as [Hscan [Hmem [Hkept [Hgap Hlen]]]].
    split; [eapply wlist_scan_move; exact Hscan|].
    split.
    - rewrite Hmem. rewrite <- !app_assoc. reflexivity.
    - split; [exact Hkept|]. split.
      + assert (Hsum : Zlength retained + Zlength garbage = ii).
        { rewrite <- Zlength_app. exact Hgap. }
        rewrite !Zlength_app. cbn. lia.
      + exact Hlen. }
  split; [exact Hmemory|]. split; [exact Hstep|].
  rewrite Hmemory. exact (proj2 (proj2 Hstep)).
Qed.

Lemma candidate_not_processed_neg__propagate_dbu :
  forall n assigns trail qhead candidate,
    lit_wf_c n candidate ->
    Znth (lit_var_c candidate) assigns 0 <>
      2 * lit_sign_c candidate - 1 ->
    ~ minisat_processed n assigns trail qhead
        (literal_neg (lit_denote candidate)).
Proof.
  intros n assigns trail qhead candidate Hwf Hcell Hprocessed.
  assert (Hnegwf : lit_wf_c n (lit_neg_c candidate)).
  { apply lit_neg_c_wf. exact Hwf. }
  assert (Hdenote : literal_neg (lit_denote candidate) =
      lit_denote (lit_neg_c candidate)).
  { symmetry. apply lit_denote_neg. destruct Hwf. lia. }
  rewrite Hdenote in Hprocessed.
  apply (proj1 (minisat_processed_denote n assigns trail qhead
    (lit_neg_c candidate) Hnegwf)) in Hprocessed.
  destruct Hprocessed as [Htrue Hposition]. unfold lit_true in Htrue.
  rewrite lit_var_c_neg, lit_sig_neg in Htrue.
  apply Hcell. rewrite Htrue. unfold lit_sig, lit_sign_c.
  destruct (Z.odd candidate); lia.
Qed.

Lemma propagation_migrated_frontier_transport__propagate_dbu :
  forall n M p current co a0 a1 tail watch0 false_lit candidate offset
    prob_after learnt_after,
    db_wf n (msolver_db M) ->
    In (current, co) (msolver_db M) ->
    co_lits co = a0 :: a1 :: tail ->
    2 <= offset < Zlength (a0 :: a1 :: tail) ->
    lit_wf_c n candidate ->
    Znth (lit_var_c candidate) (mt_assigns (ms_core M)) 0 <>
      2 * lit_sign_c candidate - 1 ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_migrated_clause watch0 candidate false_lit offset
        (a0 :: a1 :: tail)) prob_after learnt_after ->
    minisat_watch_frontier_except n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p).
Proof.
  intros n M p current co a0 a1 tail watch0 false_lit candidate offset
    prob_after learnt_after Hdb Hin Hco Hoffset Hcandwf Hcandidate Hupdate
    Hfrontier.
  assert (Hnotprocessed : ~ minisat_processed n (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M))
      (literal_neg (lit_denote candidate))).
  { eapply candidate_not_processed_neg__propagate_dbu; eassumption. }
  unfold minisat_watch_frontier_except, minisat_watch_occurrences,
    watch_frontier_except in Hfrontier |- *.
  rewrite Forall_map in Hfrontier |- *.
  eapply db_pair_lits_update_forall__propagate_dbu;
    [exact Hupdate| |exact Hfrontier].
  intros selected Hselected Hlits Hfront. left. intro Hboth.
  unfold minisat_occurrence_of_entry, clause_obj_with_lits,
    co_watch0, co_watch1, propagation_migrated_clause in Hboth.
  rewrite !replace_Znth_cons in Hboth by lia. cbn in Hboth.
  apply Hnotprocessed. exact (proj2 Hboth).
Qed.

Lemma db_pair_lits_update_focus_remove__propagate_dbu :
  forall prob learnt current old_lits new_lits prob_after learnt_after p oold,
    db_pair_lits_update prob learnt current old_lits new_lits
      prob_after learnt_after ->
    (forall co, co_lits co = old_lits ->
      minisat_entry_focus_contributions p (current, co) = [(oold, current)]) ->
    (forall co, co_lits co = old_lits ->
      minisat_entry_focus_contributions p
        (current, clause_obj_with_lits co new_lits) = []) ->
    exists pre post,
      minisat_focus_contributions (prob ++ learnt) p =
        pre ++ (oold, current) :: post /\
      minisat_focus_contributions (prob_after ++ learnt_after) p = pre ++ post.
Proof.
  intros prob learnt current old_lits new_lits prob_after learnt_after p
    oold Hupdate Hold Hnew.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [co [pre [post [Hbefore [Hafter Hlits]]]]].
  exists (minisat_focus_contributions pre p), (minisat_focus_contributions post p).
  rewrite Hbefore, Hafter, !minisat_focus_contributions_app__propagate_dbu,
    !minisat_focus_contributions_cons__propagate_dbu,
    (Hold co Hlits), (Hnew co Hlits). split; reflexivity.
Qed.

Lemma propagation_migrated_focus_transport__propagate_dbu :
  forall n M p current co a0 a1 tail watch0 false_lit candidate offset
    prob_after learnt_after P kept rest,
    db_wf n (msolver_db M) ->
    In (current, co) (msolver_db M) ->
    co_lits co = a0 :: a1 :: tail ->
    ((a0 = false_lit /\ watch0 = a1) \/
     (a1 = false_lit /\ watch0 = a0)) ->
    lit_wf_c n p ->
    false_lit = lit_neg_c p ->
    2 <= offset < Zlength (a0 :: a1 :: tail) ->
    lit_neg_c watch0 <> p ->
    lit_neg_c candidate <> p ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_migrated_clause watch0 candidate false_lit offset
        (a0 :: a1 :: tail)) prob_after learnt_after ->
    minisat_focus_scan_carrier (msolver_db M) p P kept (current :: rest) ->
    minisat_focus_scan_carrier (prob_after ++ learnt_after) p P kept rest.
Proof.
  intros n M p current co a0 a1 tail watch0 false_lit candidate offset
    prob_after learnt_after P kept rest Hdb Hin Hco Hcases Hp Hfalse Hoffset
    Hwatchneq Hcandneq Hupdate Hscan.
  assert (Hnegfalse : lit_neg_c false_lit = p).
  { rewrite Hfalse. apply lit_neg_c_involutive. }
  assert (Holdlen : (3 <=? Zlength (a0 :: a1 :: tail))%Z = true).
  { apply Z.leb_le. lia. }
  assert (Hnewlen :
      (3 <=? Zlength (propagation_migrated_clause watch0 candidate false_lit
        offset (a0 :: a1 :: tail)))%Z = true).
  { apply Z.leb_le. rewrite propagation_migrated_clause_length by lia. lia. }
  set (oold := minisat_occurrence_of_entry (current, co)).
  assert (Hold : forall co', co_lits co' = a0 :: a1 :: tail ->
      minisat_entry_focus_contributions p (current, co') = [(oold, current)]).
  { intros co' Hco'. unfold minisat_entry_focus_contributions, entry_watchers.
    unfold oold, minisat_occurrence_of_entry, denote_obj, co_watch0, co_watch1.
    rewrite Hco', Hco, Holdlen.
    rewrite !Znth0_cons.
    rewrite !Znth_cons by lia.
    replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
    cbn [fst snd].
    destruct Hcases as [[Ha0 Hw]|[Ha1 Hw]]; subst.
    - cbn. rewrite Hnegfalse.
      destruct (lit_neg_c a1 =? p)%Z eqn:Hb; cbn.
      + apply Z.eqb_eq in Hb. contradiction.
      + rewrite Z.eqb_refl. reflexivity.
    - cbn. rewrite Hnegfalse.
      destruct (lit_neg_c a0 =? p)%Z eqn:Hb; cbn.
      + apply Z.eqb_eq in Hb. contradiction.
      + rewrite Z.eqb_refl. reflexivity. }
  assert (Hnew : forall co', co_lits co' = a0 :: a1 :: tail ->
      minisat_entry_focus_contributions p
        (current, clause_obj_with_lits co'
          (propagation_migrated_clause watch0 candidate false_lit offset
            (a0 :: a1 :: tail))) = []).
  { intros co' Hco'.
    set (new_lits := propagation_migrated_clause watch0 candidate false_lit
      offset (a0 :: a1 :: tail)).
    assert (Hwatch0new :
      co_watch0 (clause_obj_with_lits co' new_lits) = watch0).
    { unfold co_watch0, clause_obj_with_lits, new_lits,
        propagation_migrated_clause.
      rewrite replace_Znth_cons by lia. reflexivity. }
    assert (Hwatch1new :
      co_watch1 (clause_obj_with_lits co' new_lits) = candidate).
    { unfold co_watch1, clause_obj_with_lits, new_lits,
        propagation_migrated_clause.
      rewrite !replace_Znth_cons by lia. cbn [Pos.to_nat]. reflexivity. }
    change (minisat_entry_focus_contributions p
      (current, clause_obj_with_lits co' new_lits) = []).
    unfold minisat_entry_focus_contributions, entry_watchers. cbn [fst snd].
    rewrite Hwatch0new, Hwatch1new.
    destruct (lit_neg_c watch0 =? p)%Z eqn:Hwb; cbn.
    - apply Z.eqb_eq in Hwb. contradiction.
    - destruct (lit_neg_c candidate =? p)%Z eqn:Hcb; cbn.
      + apply Z.eqb_eq in Hcb. contradiction.
      + reflexivity. }
  destruct (db_pair_lits_update_focus_remove__propagate_dbu
    (ms_prob M) (ms_learnt M) current (a0 :: a1 :: tail)
    (propagation_migrated_clause watch0 candidate false_lit offset
      (a0 :: a1 :: tail)) prob_after learnt_after p oold Hupdate Hold Hnew)
    as [pre [post [Hfocusold Hfocusnew]]].
  eapply focus_scan_carrier_db_pair_token_remove__propagate_dbu
    with (current := current) (co := co) (pre := pre) (post := post).
  - exact Hdb.
  - exact Hin.
  - apply even_not_tag. eapply db_wf_even; eassumption.
  - exact Hfocusold.
  - exact Hfocusnew.
  - exact Hscan.
Qed.

Lemma propagation_migrated_scan_semantics__propagate_dbu :
  forall n F A_arr K M p kept current rest prob_after learnt_after wm_after
    ,
    solver_propagation_scan_semantics n F A_arr K M p 0 kept (current :: rest) ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update
        M prob_after learnt_after wm_after) ->
    minisat_watch_frontier_except n (prob_after ++ learnt_after)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote p) ->
    minisat_focus_scan_carrier (prob_after ++ learnt_after) p
      (minisat_processed n (mt_assigns (ms_core M))
        (mt_trail (ms_core M)) (mt_qhead (ms_core M))) kept rest ->
    solver_propagation_scan_semantics n F A_arr K
      (msolver_propagation_db_wmap_update
        M prob_after learnt_after wm_after) p 0 kept rest.
Proof.
  intros n F A_arr K M p kept current rest prob_after learnt_after wm_after
    Hsem Hweak Hfrontier Hcarrier.
  destruct Hsem as [Hlive|Hdead].
  2: { destruct Hdead as [Hnz Hnil]. lia. }
  destruct Hlive as [Hzero [Hweakold [Hlevel [Hheap [Hcovers [Hreasonless
    [Hlevelp [Hpwf [Hprocessed [Hfrontierold Hcarrierold]]]]]]]]]].
  left. split; [reflexivity|].
  exact (conj Hweak (conj Hlevel (conj Hheap (conj Hcovers (conj Hreasonless
    (conj Hlevelp (conj Hpwf (conj Hprocessed (conj Hfrontier Hcarrier))))))))).
Qed.

Lemma solver_propagation_weak_db_wmap_move__propagate_dbu :
  forall n F A_arr K M current old_lits new_lits prob_after learnt_after
    wm_after,
    solver_propagation_weak n F A_arr K M ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current old_lits new_lits
      prob_after learnt_after ->
    Permutation new_lits old_lits ->
    (forall v, 0 <= v < n -> Znth v (ms_reason_words M) 0 <> current) ->
    Zlength wm_after = Zlength (ms_wm M) ->
    wmap_exact n (prob_after ++ learnt_after) wm_after ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update
        M prob_after learnt_after wm_after).
Proof.
  intros n F A_arr K M current old_lits new_lits prob_after learnt_after
    wm_after [Hpending Hweak] Hupdate Hperm Hnoowner Hwmlen
    Hwmap.
  split; [exact Hpending|]. clear Hpending.
  revert Hweak Hupdate Hperm Hnoowner Hwmlen Hwmap.
  revert M current old_lits new_lits prob_after learnt_after wm_after.
  destruct K as [A_x|A_x]; cbn; revert n F A_arr A_x.
  - msat_inv_db_wmap_move msw_db_wf msw_db_matches msw_db_implied
      msw_db_complete msw_prob_db msw_learnt_db msw_binary_out msw_reasons_mem
      msw_reason_head msw_size msw_shape.
  - msat_inv_db_wmap_move msa_db_wf msa_db_matches msa_db_implied
      msa_db_complete msa_prob_db msa_learnt_db msa_binary_out msa_reasons_mem
      msa_reason_head msa_size msa_shape.
Qed.

(** ===== group: solver_propagate_db_update_reason_owner ===== *)


Lemma no_live_reason_owner_candidate_not_false__propagate_dbu :
  forall n M current co candidate,
    n = ms_size M ->
    db_wf n (msolver_db M) ->
    mtrail_wf n (ms_core M) ->
    stable_view (msolver_view n M) ->
    reasons_match n (ms_core M) (msolver_db M)
      (ms_reason_words M) (ms_reason_of M) ->
    reason_head_ok M ->
    In (current, co) (msolver_db M) ->
    In candidate (co_lits co) ->
    lit_wf_c n candidate ->
    lit_var_c candidate <> lit_var_c (co_watch0 co) ->
    Znth (lit_var_c candidate) (mt_assigns (ms_core M)) 0 <>
      2 * lit_sign_c candidate - 1 ->
    forall v, 0 <= v < n -> Znth v (ms_reason_words M) 0 <> current.
Proof.
  intros n M current co candidate Hsize Hdbwf Htrail Hstable Hreasons Hhead
    Hin Hcandin Hcandwf Hvardiff Hcandidate v Hv Heq.
  pose proof (db_wf_ptr_pos n (msolver_db M) current co Hdbwf Hin) as Hpos.
  assert (Hreal : is_tag current = false).
  { apply even_not_tag.
    exact (db_wf_even n (msolver_db M) current co Hdbwf Hin). }
  assert (Hheadvar : lit_var_c (co_watch0 co) = v).
  { apply (Hhead v co).
    - rewrite <- Hsize. exact Hv.
    - rewrite Heq. exact Hreal.
    - rewrite Heq. lia.
    - rewrite Heq. exact Hin. }
  destruct (reason_owner_valid__propagate_dbu
    n M current co v Hdbwf Htrail Hstable Hreasons Hin Hv Heq)
    as [b [Hpv Hvalid]].
  destruct Hvalid as [b' [d' [rx' [Hpv' [Hlevel' [Hrank' [Hsat Hside]]]]]]].
  change (mt_pv (ms_core M) v = Some b') in Hpv'.
  rewrite Hpv in Hpv'. inversion Hpv'; subst b'.
  assert (Hlitin : In (lit_denote candidate) (denote_obj co)).
  { unfold denote_obj. apply lits_denote_in. exact Hcandin. }
  specialize (Hside (lit_denote candidate) Hlitin).
  assert (Hvarneq : literal_var (lit_denote candidate) <> v).
  { rewrite lit_var_c_denote, <- Hheadvar. exact Hvardiff. }
  specialize (Hside Hvarneq). destruct Hside as [Heval Hrankside].
  unfold msolver_view, view_of in Heval. cbn in Heval.
  assert (Hvarnonneg : 0 <= lit_var_c candidate).
  { eapply lit_var_c_nonneg. exact Hcandwf. }
  assert (Heqeval :
    eval_partial_literal (mt_pv (ms_core M)) (lit_denote candidate) =
    eval_partial_literal (assigns_pv (mt_assigns (ms_core M)))
      (lit_denote candidate)).
  { unfold eval_partial_literal. rewrite lit_var_c_denote.
    rewrite mt_pv_nonneg by exact Hvarnonneg. reflexivity. }
  rewrite Heqeval in Heval.
  assert (Hcandnonneg : 0 <= candidate) by (destruct Hcandwf; lia).
  apply (proj2 (lit_false_iff (mt_assigns (ms_core M)) candidate
    Hcandnonneg)) in Heval.
  apply Hcandidate. rewrite Heval.
  unfold lit_sig, lit_sign_c. destruct (Z.odd candidate); lia.
Qed.

Lemma no_live_reason_owner_false_clause__propagate_dbu :
  forall n M current co,
    db_wf n (msolver_db M) ->
    mtrail_wf n (ms_core M) ->
    stable_view (msolver_view n M) ->
    reasons_match n (ms_core M) (msolver_db M)
      (ms_reason_words M) (ms_reason_of M) ->
    In (current, co) (msolver_db M) ->
    Forall (fun l => eval_partial_literal (mt_pv (ms_core M)) l = Some false)
      (denote_obj co) ->
    forall v, 0 <= v < n -> Znth v (ms_reason_words M) 0 <> current.
Proof.
  intros n M current co Hdbwf Htrail Hstable Hreasons Hin Hden_false v Hv Heq.
  destruct (reason_owner_valid__propagate_dbu
    n M current co v Hdbwf Htrail Hstable Hreasons Hin Hv Heq)
    as [b [Hpv Hvalid]].
  destruct Hvalid as [b' [d' [rx' [Hpv' [_ [_ [Hsat _]]]]]]].
  change (mt_pv (ms_core M) v = Some b') in Hpv'.
  rewrite Hpv in Hpv'. inversion Hpv'; subst b'.
  rewrite Forall_forall in Hden_false.
  pose proof (Hden_false (satisfying_literal v b) Hsat) as Hfalse.
  pose proof (eval_satisfying_literal_true (mt_pv (ms_core M)) v b Hpv)
    as Htrue.
  congruence.
Qed.

Lemma db_pair_lits_update_wmap_move__propagate_dbu :
  forall n prob learnt current old_lits new_lits prob_after learnt_after
    oldwm newwm co,
    db_wf n (prob ++ learnt) ->
    In (current, co) (prob ++ learnt) ->
    co_lits co = old_lits ->
    db_pair_lits_update prob learnt current old_lits new_lits
      prob_after learnt_after ->
    wmap_exact n (prob ++ learnt) oldwm ->
    Zlength newwm = 2 * n ->
    (forall l, 0 <= l < 2 * n ->
      Permutation
        (Znth l newwm nil ++ entry_watchers (current, co) l)
        (Znth l oldwm nil ++ entry_watchers
          (current, clause_obj_with_lits co new_lits) l)) ->
    wmap_exact n (prob_after ++ learnt_after) newwm.
Proof.
  intros n prob learnt current old_lits new_lits prob_after learnt_after
    oldwm newwm co Hdbwf Hin Hco Hupdate Hold Hlen Hdiff.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [selected [pre [post [Hbefore [Hafter Hlits]]]]].
  assert (Heq : selected = co).
  { eapply db_wf_lookup_unique; [exact Hdbwf| |exact Hin].
    rewrite Hbefore. apply in_or_app. right. left. reflexivity. }
  subst selected. rewrite Hbefore in Hold. rewrite Hafter.
  eapply wmap_move; [exact Hold|exact Hlen|exact Hdiff].
Qed.

Lemma propagation_move_wmap_cells__propagate_dbu :
  forall n M hole target wm source
    newsource current co new_lits,
    propagation_scan_slot M hole wm source ->
    0 <= hole < 2 * n ->
    propagation_destination_ok (2 * n) hole target ->
    Permutation (newsource ++ [current]) source ->
    (forall l,
      Permutation
        (entry_watchers (current, co) l ++
         (if (l =? target)%Z then [current] else []))
        (entry_watchers (current, clause_obj_with_lits co new_lits) l ++
         (if (l =? hole)%Z then [current] else []))) ->
    Zlength (ms_wm M) = 2 * n ->
    Zlength (propagation_move_wmap hole target wm newsource current) =
      2 * n /\
    forall l, 0 <= l < 2 * n ->
      Permutation
        (Znth l (propagation_move_wmap hole target wm newsource current)
           nil ++ entry_watchers (current, co) l)
        (Znth l (ms_wm M) nil ++
         entry_watchers (current, clause_obj_with_lits co new_lits) l).
Proof.
  intros n M hole target wm source
    newsource current co new_lits Hslot Hhole Htarget Hsource Hentry Hlen.
  destruct Hslot as [Hwm Hrange].
  unfold propagation_destination_ok in Htarget.
  destruct Htarget as [Hholenonneg [Htargetrange Hdistinct]].
  assert (Hwmlen : Zlength wm = 2 * n)
    by (rewrite <- Hlen, Hwm, Zlength_replace_Znth; reflexivity).
  assert (Hbase : replace_Znth hole newsource wm =
      replace_Znth hole newsource (ms_wm M)).
  { rewrite Hwm, replace_Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Htargetold : Znth target (ms_wm M) nil = Znth target wm nil).
  { rewrite Hwm. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnewlen : Zlength
      (propagation_move_wmap hole target wm newsource current) = 2 * n).
  { unfold propagation_move_wmap. rewrite !Zlength_replace_Znth. exact Hwmlen. }
  split; [exact Hnewlen|]. intros l Hl.
  unfold propagation_move_wmap.
  destruct (Z.eq_dec l target) as [Hltarget|Hltarget].
  - subst l. rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth, Hwmlen; exact Htargetrange).
    rewrite <- Htargetold.
    specialize (Hentry target).
    rewrite Z.eqb_refl in Hentry.
    assert (Hth : (target =? hole)%Z = false)
      by (apply Z.eqb_neq; exact Hdistinct).
    rewrite Hth, app_nil_r in Hentry.
    rewrite <- app_assoc. apply Permutation_app_head.
    eapply Permutation_trans.
    + apply Permutation_app_comm.
    + exact Hentry.
  - rewrite Znth_replace_Znth_Diff.
    2: { rewrite Zlength_replace_Znth, Hwmlen. exact Htargetrange. }
    2: { rewrite Zlength_replace_Znth, Hwmlen. exact Hl. }
    2: { congruence. }
    rewrite Hbase.
    destruct (Z.eq_dec l hole) as [Hlholes|Hlholes].
    + subst l.
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hhole).
      rewrite Hwm, Znth_replace_Znth_Same by (rewrite Hwmlen; exact Hhole).
      specialize (Hentry hole).
      assert (Hht : (hole =? target)%Z = false)
        by (apply Z.eqb_neq; congruence).
      rewrite Hht, Z.eqb_refl, app_nil_r in Hentry.
      eapply Permutation_trans.
      * apply Permutation_app_head. exact Hentry.
      * eapply Permutation_trans.
        -- apply Permutation_app_head. apply Permutation_app_comm.
        -- rewrite app_assoc. apply Permutation_app_tail. exact Hsource.
    + rewrite Znth_replace_Znth_Diff.
      2: { rewrite Hlen. exact Hhole. }
      2: { rewrite Hlen. exact Hl. }
      2: { congruence. }
      specialize (Hentry l).
      assert (Hlt : (l =? target)%Z = false)
        by (apply Z.eqb_neq; exact Hltarget).
      assert (Hlh : (l =? hole)%Z = false)
        by (apply Z.eqb_neq; exact Hlholes).
      rewrite Hlt, Hlh, !app_nil_r in Hentry.
      apply Permutation_app_head. exact Hentry.
Qed.

Lemma propagation_migrated_entry_watchers_delta__propagate_dbu :
  forall n p current co a0 a1 tail watch0 false_lit candidate offset,
    lit_wf_c n p ->
    false_lit = lit_neg_c p ->
    co_lits co = a0 :: a1 :: tail ->
    ((a0 = false_lit /\ watch0 = a1) \/
     (a1 = false_lit /\ watch0 = a0)) ->
    2 <= offset < Zlength (a0 :: a1 :: tail) ->
    forall l,
      Permutation
        (entry_watchers (current, co) l ++
         (if (l =? lit_neg_c candidate)%Z then [current] else []))
        (entry_watchers
           (current, clause_obj_with_lits co
             (propagation_migrated_clause watch0 candidate false_lit offset
               (a0 :: a1 :: tail))) l ++
         (if (l =? p)%Z then [current] else [])).
Proof.
  intros n p current co a0 a1 tail watch0 false_lit candidate offset
    Hp Hfalse Hco Hcases Hoffset l.
  assert (Hnegfalse : lit_neg_c false_lit = p).
  { rewrite Hfalse. apply lit_neg_c_involutive. }
  assert (Hnewlen :
      (3 <=? Zlength (propagation_migrated_clause watch0 candidate false_lit
        offset (a0 :: a1 :: tail)))%Z = true).
  { apply Z.leb_le. rewrite propagation_migrated_clause_length by lia. lia. }
  assert (Holdlen : (3 <=? Zlength (a0 :: a1 :: tail))%Z = true).
  { apply Z.leb_le. lia. }
  unfold entry_watchers, co_watch0, co_watch1.
  cbn [fst snd]. rewrite Hco, Holdlen.
  unfold clause_obj_with_lits. cbn [co_lits]. rewrite Hnewlen.
  unfold propagation_migrated_clause.
  rewrite !replace_Znth_cons by lia.
  rewrite !Znth0_cons.
  rewrite !Znth_cons by lia.
  replace (1 - 1) with 0 by lia. rewrite !Znth0_cons.
  destruct Hcases as [[Ha0 Hw]|[Ha1 Hw]].
  - subst a0. subst a1. rewrite Hnegfalse. change (Permutation
      (((if (p =? l)%Z then [current] else []) ++
        (if (lit_neg_c watch0 =? l)%Z then [current] else [])) ++
       (if (l =? lit_neg_c candidate)%Z then [current] else []))
      (((if (lit_neg_c watch0 =? l)%Z then [current] else []) ++
        (if (lit_neg_c candidate =? l)%Z then [current] else [])) ++
       (if (l =? p)%Z then [current] else []))).
    rewrite Z.eqb_sym with (x := l) (y := lit_neg_c candidate).
    rewrite Z.eqb_sym with (x := l) (y := p).
    rewrite <- app_assoc. apply Permutation_app_comm.
  - subst a1. subst a0. rewrite Hnegfalse. change (Permutation
      (((if (lit_neg_c watch0 =? l)%Z then [current] else []) ++
        (if (p =? l)%Z then [current] else [])) ++
       (if (l =? lit_neg_c candidate)%Z then [current] else []))
      (((if (lit_neg_c watch0 =? l)%Z then [current] else []) ++
        (if (lit_neg_c candidate =? l)%Z then [current] else [])) ++
       (if (l =? p)%Z then [current] else []))).
    rewrite Z.eqb_sym with (x := l) (y := lit_neg_c candidate).
    rewrite Z.eqb_sym with (x := l) (y := p).
    rewrite <- app_assoc. rewrite <- app_assoc. apply Permutation_app_head.
    apply Permutation_app_comm.
Qed.

Lemma propagation_migrated_clause_structure__propagate_dbu :
  forall n M p current contents watch0 false_lit lits stop k offset candidate sig
    prob_after learnt_after,
    db_wf n (msolver_db M) ->
    propagation_scan_candidate_layout current lits stop k offset false_lit p
      candidate sig contents ->
    real_watch_pair p contents ->
    watch0 + false_lit = Znth 0 contents 0 + Znth 1 contents 0 ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current contents
      (propagation_migrated_clause watch0 candidate false_lit offset contents)
      prob_after learnt_after ->
    exists co a0 a1 tail,
      contents = a0 :: a1 :: tail /\
      In (current, co) (msolver_db M) /\
      co_lits co = a0 :: a1 :: tail /\
      sublist 2 (Zlength contents) contents = tail /\
      ((a0 = false_lit /\ watch0 = a1) \/
       (a1 = false_lit /\ watch0 = a0)) /\
      candidate = Znth (offset - 2) tail 0 /\
      In candidate (co_lits co) /\
      lit_wf_c n candidate /\
      lit_var_c candidate <> lit_var_c (co_watch0 co) /\
      lit_neg_c watch0 <> p /\
      lit_neg_c candidate <> p /\
      Permutation
        (propagation_migrated_clause watch0 candidate false_lit offset contents)
        contents.
Proof.
  intros n M p current contents watch0 false_lit lits stop k offset candidate
    sig prob_after learnt_after Hdbwf Hlayout Hreal Hsum Hupdate.
  unfold propagation_scan_candidate_layout in Hlayout.
  destruct Hlayout as
    [Hlits [Hlen [Hfalse [Hstop [Hk [Hoffset [Hcandidate Hsig]]]]]]].
  destruct (db_pair_lits_update_selected_before__propagate_dbu
    _ _ _ _ _ _ _ Hupdate) as [co [Hin Hco]].
  pose proof (db_wf_obj n (msolver_db M) current co Hdbwf Hin) as Hobj.
  unfold obj_wf in Hobj. rewrite Hco in Hobj.
  destruct Hobj as [Hobjlen [Hall Hnodup]].
  destruct contents as [|a0 tail0]; cbn in Hobjlen; [lia|].
  destruct tail0 as [|a1 tail]; cbn in Hobjlen; [lia|].
  assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail))
      (a0 :: a1 :: tail) = tail).
  { replace (a0 :: a1 :: tail) with ((a0 :: a1 :: nil) ++ tail)
      by reflexivity.
    rewrite (sublist_split_app_r 2
      (Zlength ((a0 :: a1 :: nil) ++ tail)) 2
      (a0 :: a1 :: nil) tail ltac:(reflexivity)) by
      (split; [lia|rewrite Zlength_app, !Zlength_cons, Zlength_nil;
        pose proof (Zlength_nonneg tail); lia]).
    replace (Zlength ((a0 :: a1 :: nil) ++ tail) - 2)
      with (Zlength tail) by
      (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
    apply sublist_self. reflexivity. }
  rewrite Htail in Hcandidate.
  assert (Hwatchcases :
      (a0 = false_lit /\ watch0 = a1) \/
      (a1 = false_lit /\ watch0 = a0)).
  { unfold real_watch_pair in Hreal.
    rewrite !Znth0_cons in Hreal, Hsum.
    rewrite !Znth_cons in Hreal, Hsum by lia.
    replace (1 - 1) with 0 in Hreal, Hsum by lia.
    rewrite !Znth0_cons in Hreal, Hsum.
    destruct Hreal as [Hw|Hw].
    - left. rewrite <- Hfalse in Hw. split; [exact Hw|lia].
    - right. rewrite <- Hfalse in Hw. split; [exact Hw|lia]. }
  inversion Hnodup as [|v0 vars0 Hnot0 Hnd0]; subst v0 vars0.
  inversion Hnd0 as [|v1 vars1 Hnot1 Hndtail]; subst v1 vars1.
  assert (Hcandrange : 0 <= offset - 2 < Zlength tail).
  { rewrite <- Htail, Zlength_sublist by lia. lia. }
  assert (Hcandin : In candidate tail).
  { rewrite Hcandidate. apply Znth_In. exact Hcandrange. }
  assert (Hcandvarin : In (lit_var_c candidate) (map lit_var_c tail)).
  { apply in_map. exact Hcandin. }
  assert (Hcandinco : In candidate (co_lits co)).
  { rewrite Hco. cbn. right. right. exact Hcandin. }
  assert (Hcandwf : lit_wf_c n candidate).
  { rewrite Forall_forall in Hall. apply Hall.
    cbn. right. right. exact Hcandin. }
  assert (Hvardiff01 : lit_var_c a0 <> lit_var_c a1).
  { intro Heq. apply Hnot0. cbn. left. symmetry. exact Heq. }
  assert (Hvardiff0c : lit_var_c a0 <> lit_var_c candidate).
  { intro Heq. apply Hnot0. cbn. right. rewrite Heq. exact Hcandvarin. }
  assert (Hvardiff1c : lit_var_c a1 <> lit_var_c candidate).
  { intro Heq. apply Hnot1. rewrite Heq. exact Hcandvarin. }
  assert (Hwatchneq : lit_neg_c watch0 <> p).
  { intro Heq. apply Hvardiff01.
    pose proof (f_equal lit_var_c Heq) as Hv.
    rewrite lit_var_c_neg in Hv.
    assert (Hfv : lit_var_c false_lit = lit_var_c p).
    { rewrite Hfalse, lit_var_c_neg. reflexivity. }
    destruct Hwatchcases as [[Ha Hw]|[Ha Hw]]; subst; lia. }
  assert (Hcandneq : lit_neg_c candidate <> p).
  { intro Heq. pose proof (f_equal lit_var_c Heq) as Hv.
    rewrite lit_var_c_neg in Hv.
    assert (Hfv : lit_var_c false_lit = lit_var_c p).
    { rewrite Hfalse, lit_var_c_neg. reflexivity. }
    destruct Hwatchcases as [[Ha Hw]|[Ha Hw]]; subst;
      [apply Hvardiff0c|apply Hvardiff1c]; lia. }
  assert (Hcandhead : lit_var_c candidate <> lit_var_c (co_watch0 co)).
  { unfold co_watch0. rewrite Hco. cbn. congruence. }
  assert (Hpermnorm : Permutation (watch0 :: false_lit :: tail)
      (a0 :: a1 :: tail)).
  { destruct Hwatchcases as [[Ha Hw]|[Ha Hw]]; subst.
    - apply perm_swap. - reflexivity. }
  assert (Hperm_move : Permutation
      (propagation_migrated_clause watch0 candidate false_lit offset
        (a0 :: a1 :: tail))
      (watch0 :: false_lit :: tail)).
  { unfold propagation_migrated_clause. rewrite Htail.
    rewrite !replace_Znth_cons by lia.
    apply perm_skip.
    eapply Permutation_trans.
    - apply perm_skip.
      replace (offset - 1 - 1) with (offset - 2) by lia.
      apply (list_without_Znth_replace_perm 0 false_lit
        (offset - 2) tail Hcandrange).
    - eapply Permutation_trans.
      + apply perm_swap.
      + apply perm_skip. apply Permutation_sym.
        rewrite Hcandidate.
        apply (list_without_Znth_perm 0 (offset - 2) tail Hcandrange). }
  exists co, a0, a1, tail.
  split; [reflexivity|]. split; [exact Hin|]. split; [exact Hco|].
  split; [exact Htail|]. split; [exact Hwatchcases|].
  split; [exact Hcandidate|]. split; [exact Hcandinco|].
  split; [exact Hcandwf|]. split; [exact Hcandhead|].
  split; [exact Hwatchneq|]. split; [exact Hcandneq|].
  eapply Permutation_trans; [exact Hperm_move|exact Hpermnorm].
Qed.

Lemma propagation_migrated_clause_db_rebuild__propagate_dbu :
  forall n prob learnt current lits stop k offset false_lit p candidate sig
    watch0 contents,
    db_wf n (prob ++ learnt) ->
    propagation_scan_candidate_layout current lits stop k offset false_lit p
      candidate sig contents ->
    (clause_db_pair_frame prob learnt current contents **
     (lits + 0 * sizeof(INT)) # Int |-> watch0 **
     (lits + 1 * sizeof(INT)) # Int |-> candidate **
     IntArray.seg lits 2 (Zlength contents)
       (replace_Znth (offset - 2) false_lit
         (replace_Znth (offset - 2) candidate
           (sublist 2 (Zlength contents) contents))))
    |-- EX prob_after learnt_after : dbmap,
      “ db_pair_lits_update prob learnt current contents
          (propagation_migrated_clause watch0 candidate false_lit offset contents)
          prob_after learnt_after ” &&
      (clause_db_rep prob_after ** clause_db_rep learnt_after).
Proof.
  intros n prob learnt current lits stop k offset false_lit p candidate sig
    watch0 contents Hdbwf Hlayout.
  unfold propagation_scan_candidate_layout in Hlayout.
  destruct Hlayout as
    [Hlits [Hlen [Hfalse [Hstop [Hk [Hoffset [Hcandidate Hsig]]]]]]].
  unfold clause_lits_pointer in Hlits. subst lits.
  assert (Htailrange : 0 <= offset - 2 <
      Zlength (sublist 2 (Zlength contents) contents)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Htailrestore : replace_Znth (offset - 2) candidate
      (sublist 2 (Zlength contents) contents) =
      sublist 2 (Zlength contents) contents).
  { rewrite Hcandidate. apply replace_Znth_Znth. }
  assert (Hnewlen : Zlength
      (propagation_migrated_clause watch0 candidate false_lit offset contents) =
      Zlength contents).
  { apply propagation_migrated_clause_length. lia. }
  unfold clause_db_pair_frame. Intros is_learnt.
  sep_apply_l_atomic
    (IntArray.seg_single (clause_lits_addr current) 0 watch0).
  sep_apply_l_atomic
    (IntArray.seg_single (clause_lits_addr current) 1 candidate).
  
  replace (0 + 1) with 1 by lia. replace (1 + 1) with 2 by lia.
  sep_apply_l_atomic
    (IntArray.seg_merge_to_seg (clause_lits_addr current)
      0 1 2 (watch0 :: nil) (candidate :: nil)).
  - dump_pre_spatial. lia.
  - cbn [app].
    sep_apply_l_atomic
      (IntArray.seg_merge_to_seg (clause_lits_addr current)
        0 2 (Zlength contents) (watch0 :: candidate :: nil)
        (replace_Znth (offset - 2) false_lit
          (replace_Znth (offset - 2) candidate
            (sublist 2 (Zlength contents) contents)))).
    + dump_pre_spatial. lia.
    + cbn [app]. rewrite Htailrestore.
      assert (Hfold : watch0 :: candidate ::
          replace_Znth (offset - 2) false_lit
            (sublist 2 (Zlength contents) contents) =
          propagation_migrated_clause watch0 candidate false_lit offset contents).
      { unfold propagation_migrated_clause.
        rewrite !replace_Znth_cons by lia.
        replace (offset - 1 - 1) with (offset - 2) by lia. reflexivity. }
      rewrite Hfold. unfold clause_db_pair_remainder. Split.
      * Intros co pre post. 
        destruct H as [Hprob [Hco_lits Hco_learnt]].
        assert (Hin : In (current, co) (prob ++ learnt)).
        { rewrite Hprob, !in_app_iff. cbn. tauto. }
        assert (Hpos : 0 < current).
        { eapply db_wf_ptr_pos; [exact Hdbwf|exact Hin]. }
        assert (Hmod : current mod 2 = 0).
        { apply clause_ptr_mod2. eapply db_wf_even; eassumption. }
        set (new_lits := propagation_migrated_clause
          watch0 candidate false_lit offset contents).
        set (co_new := clause_obj_with_lits co new_lits).
        set (prob_after := pre ++ (current, co_new) :: post).
        Exists prob_after learnt. split_pure_spatial.
        -- unfold prob_after.
           sep_apply_r_atomic
             (clause_db_rep_app_intro pre ((current, co_new) :: post)).
           rewrite clause_db_rep_cons.
           unfold MiniSatClause.rep, co_new, clause_obj_with_lits, new_lits.
           cbn [fst snd co_lits co_learnt]. rewrite Hco_learnt, Hnewlen.
           (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
        -- apply derivable1s_coq_prop_r. left. exists co, pre, post.
           split; [exact Hprob|]. split; [exact Hco_lits|].
           split; reflexivity.
      * Intros co pre post. 
        destruct H as [Hlearnt [Hco_lits Hco_learnt]].
        assert (Hin : In (current, co) (prob ++ learnt)).
        { rewrite Hlearnt, !in_app_iff. cbn. tauto. }
        assert (Hpos : 0 < current).
        { eapply db_wf_ptr_pos; [exact Hdbwf|exact Hin]. }
        assert (Hmod : current mod 2 = 0).
        { apply clause_ptr_mod2. eapply db_wf_even; eassumption. }
        set (new_lits := propagation_migrated_clause
          watch0 candidate false_lit offset contents).
        set (co_new := clause_obj_with_lits co new_lits).
        set (learnt_after := pre ++ (current, co_new) :: post).
        Exists prob learnt_after. split_pure_spatial.
        -- unfold learnt_after.
           sep_apply_r_atomic
             (clause_db_rep_app_intro pre ((current, co_new) :: post)).
           rewrite clause_db_rep_cons.
           unfold MiniSatClause.rep, co_new, clause_obj_with_lits, new_lits.
           cbn [fst snd co_lits co_learnt]. rewrite Hco_learnt, Hnewlen.
           (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
        -- apply derivable1s_coq_prop_r. right. exists co, pre, post.
           split; [exact Hlearnt|]. split; [exact Hco_lits|].
           split; reflexivity.
Qed.

