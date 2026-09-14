Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Field.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
(* Load the reals and Flocq modules; [Binary] is imported below.
   The additional local imports used by [MSatFloatFacts] are in
   [solver_qcp_model.v], inside that module. *)
From Coq Require Reals SpecFloat.
From Flocq.Core Require Core.
From Flocq.IEEE754 Require Import Binary.
From CDCLLib Require Export cdcl_shared_lib.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_model.

(* Proof tactics over the MiniSat model. *)

(* [solver_rep_levels_at] and its cancel-split view differ only in the direction
   of the entailment; one script proves both. *)
Ltac msat_rep_levels_cancel_split :=
  intros s M lvl wl;
  unfold solver_rep_levels_wl_at, solver_cancel_owned;
  entailer_with lia.

(* Refolding a full learnt-database vector back into the staged solver
   representation.  [STAGE] is the stage-refold lemma of the flavour being
   proved (the wlists-named one for the [_wl] fork). *)
Ltac msat_full_db_stage_refold STAGE :=
  intros s begin clause_out database watch0 watch1 wl lvl M words p
    Hshape Hdatabase Hwatch0 Hwatch1 Hne Hfull Hcap Hidx0 Hidx1;
  fold (vecp_size_addr database);
  fold (vecp_cap_addr database);
  fold (vecp_ptr_addr database);
  sep_apply (vecp_full_refold__act_clause_bump database p
    (db_words (ms_learnt M)) (ms_learnt_cap M) Hfull Hcap);
  transitivity
    (clause_new_stage_rep_at
      s begin clause_out database watch0 watch1 wl lvl M words);
  [ unfold clause_new_stage_rep_at; cbn;
    split_pure_spatial;
    [ entailer_with lia | unfold db_words; entailer_with lia ]
  | sep_apply (STAGE
      s begin clause_out database watch0 watch1 wl lvl M words
      Hshape Hidx0 Hidx1);
    entailer_with lia ].

(* ---------------------------------------------------------------------- *)
(* One projection-transport step for [msolver_install_clause].  It stands
   in for the pasted 38-conjunct [assert (Hproj : ...)] + [destruct] +
   [rewrite] block that each of the four
   [clause_new_install_rep_at_refold__clause_new*] proofs below would
   otherwise carry.  Only two conjuncts differ between the
   learnt (sel = true) and problem (sel = false) forks, so they are passed in:
   [PROB] and [LEARNT] are the right-hand sides of the [ms_prob] / [ms_learnt]
   equations.  The tactic sequence is IDENTICAL to the text it replaces --
   same assert, same closer, same rewrite order.  Suffixed [_w1perf] so it
   cannot collide with a tactic moved into a proof_common file.         *)
(* ---------------------------------------------------------------------- *)
Ltac msat_install_clause_proj_rw M c words sel PROB LEARNT :=
  assert (Hproj :
    ms_size (msolver_install_clause M c words sel) = ms_size M /\
    ms_cap (msolver_install_clause M c words sel) = ms_cap M /\
    ms_core (msolver_install_clause M c words sel) = ms_core M /\
    ms_qtail (msolver_install_clause M c words sel) = ms_qtail M /\
    ms_root_level (msolver_install_clause M c words sel) = ms_root_level M /\
    ms_reason_words (msolver_install_clause M c words sel) = ms_reason_words M /\
    ms_prob (msolver_install_clause M c words sel) = PROB /\
    ms_learnt (msolver_install_clause M c words sel) = LEARNT /\
    ms_binary (msolver_install_clause M c words sel) = ms_binary M /\
    ms_binary_lits (msolver_install_clause M c words sel) = ms_binary_lits M /\
    ms_wm (msolver_install_clause M c words sel) = clause_new_watch_map M c words /\
    ms_wcaps (msolver_install_clause M c words sel) = ms_wcaps M /\
    ms_activity (msolver_install_clause M c words sel) = ms_activity M /\
    ms_orderpos (msolver_install_clause M c words sel) = ms_orderpos M /\
    ms_order (msolver_install_clause M c words sel) = ms_order M /\
    ms_order_cap (msolver_install_clause M c words sel) = ms_order_cap M /\
    ms_lim_cap (msolver_install_clause M c words sel) = ms_lim_cap M /\
    ms_model (msolver_install_clause M c words sel) = ms_model M /\
    ms_model_cap (msolver_install_clause M c words sel) = ms_model_cap M /\
    ms_tags (msolver_install_clause M c words sel) = ms_tags M /\
    ms_tagged (msolver_install_clause M c words sel) = ms_tagged M /\
    ms_tagged_cap (msolver_install_clause M c words sel) = ms_tagged_cap M /\
    ms_stack (msolver_install_clause M c words sel) = ms_stack M /\
    ms_stack_cap (msolver_install_clause M c words sel) = ms_stack_cap M /\
    ms_var_inc (msolver_install_clause M c words sel) = ms_var_inc M /\
    ms_var_decay (msolver_install_clause M c words sel) = ms_var_decay M /\
    ms_cla_inc (msolver_install_clause M c words sel) = ms_cla_inc M /\
    ms_cla_decay (msolver_install_clause M c words sel) = ms_cla_decay M /\
    ms_random_seed (msolver_install_clause M c words sel) = ms_random_seed M /\
    ms_progress (msolver_install_clause M c words sel) = ms_progress M /\
    ms_simpdb_assigns (msolver_install_clause M c words sel) = ms_simpdb_assigns M /\
    ms_simpdb_props (msolver_install_clause M c words sel) = ms_simpdb_props M /\
    ms_verbosity (msolver_install_clause M c words sel) = ms_verbosity M /\
    ms_stats (msolver_install_clause M c words sel) = ms_stats M /\
    ms_prob_cap (msolver_install_clause M c words sel) = ms_prob_cap M /\
    ms_learnt_cap (msolver_install_clause M c words sel) = ms_learnt_cap M /\
    ms_capacity_pending_qhead (msolver_install_clause M c words sel) = ms_capacity_pending_qhead M /\
    ms_capacity_root_propagation_pending (msolver_install_clause M c words sel) =
      ms_capacity_root_propagation_pending M)
    by (repeat split; reflexivity);
  destruct Hproj as (Esize & Ecap & Ecore & Eqtail & Eroot & Ereasons & Eprob
    & Elearnt & Ebinary & Ebinary_lits & Ewm & Ewcaps & Eactivity & Eorderpos
    & Eorder & Eorder_cap & Elim_cap & Emodel & Emodel_cap & Etags & Etagged
    & Etagged_cap & Estack & Estack_cap & Evar_inc & Evar_decay & Ecla_inc &
    Ecla_decay & Erandom_seed & Eprogress & Esimpdb_assigns & Esimpdb_props &
    Everbosity & Estats & Eprob_cap & Elearnt_cap & Ecapacity_pending &
    Ecapacity_root);
  rewrite Esize, Ecap, Ecore, Eqtail, Eroot, Ereasons, Eprob, Elearnt,
    Ebinary, Ebinary_lits, Ewm, Ewcaps, Eactivity, Eorderpos, Eorder,
    Eorder_cap, Elim_cap, Emodel, Emodel_cap, Etags, Etagged, Etagged_cap,
    Estack, Estack_cap, Evar_inc, Evar_decay, Ecla_inc, Ecla_decay,
    Erandom_seed, Eprogress, Esimpdb_assigns, Esimpdb_props, Everbosity,
    Estats, Eprob_cap, Elearnt_cap, Ecapacity_pending, Ecapacity_root.

(* Installing a learnt clause with more than two literals: the address-level
   bookkeeping covers both watch words, both watch-map entries, the untouched
   remainder and the post-install shape while retaining the named [wl]
   address.  Opening half. *)
(* Shared watch words, watch-map updates, and the untouched two-list remainder. *)
Tactic Notation "msat_cn_install_watch_facts"
    ident(M) ident(c) ident(words) ident(wl) ident(Hshape) ident(Hne)
    ident(Hwm_len) ident(Hwcaps_len) ident(Hwatch_word0) ident(Hwatch_word1)
    ident(Hwm0) ident(Hwm1) ident(Hrem) :=
  pose proof (solver_shape_wm_len M Hshape) as Hwm_len;
  pose proof (solver_shape_wcaps_len M Hshape) as Hwcaps_len;
  assert (Hwatch_word0 :
      clause_watch_word c words (Znth 1 words 0) = c) by (unfold clause_watch_word;
        destruct (Z.ltb 2 (Zlength words)) eqn:E; [reflexivity |]; apply Z.ltb_ge in E;
        lia);
  assert (Hwatch_word1 :
      clause_watch_word c words (Znth 0 words 0) = c) by (unfold clause_watch_word;
        destruct (Z.ltb 2 (Zlength words)) eqn:E; [reflexivity |]; apply Z.ltb_ge in E;
        lia);
  assert (Hwm0 :
      Znth (lit_neg_c (Znth 0 words 0))
        (clause_new_watch_map M c words) nil =
      Znth (lit_neg_c (Znth 0 words 0)) (ms_wm M) nil +:: c) by (rewrite clause_new_watch_map_Znth
        by lia; rewrite Z.eqb_refl, Hwatch_word0; reflexivity);
  assert (Hwm1 :
      Znth (lit_neg_c (Znth 1 words 0))
        (clause_new_watch_map M c words) nil =
      Znth (lit_neg_c (Znth 1 words 0)) (ms_wm M) nil +:: c) by (rewrite clause_new_watch_map_Znth
        by lia; destruct (Z.eqb (lit_neg_c (Znth 0 words 0))
        (lit_neg_c (Znth 1 words 0))) eqn:E; [ apply Z.eqb_eq in E; contradiction | rewrite
          Z.eqb_refl, Hwatch_word1; reflexivity ]);
  assert (Hrem :
      wlists_two_remainder wl
        (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0))
        (ms_wm M) (ms_wcaps M) =
      wlists_two_remainder wl
        (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0))
        (clause_new_watch_map M c words) (ms_wcaps M)) by (unfold clause_new_watch_map,
          wmap_push_word; rewrite Znth_replace_Znth_Diff by lia; transitivity
        (wlists_two_remainder wl
          (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0))
          (replace_Znth (lit_neg_c (Znth 0 words 0))
            (Znth (lit_neg_c (Znth 0 words 0)) (ms_wm M) nil +::
              clause_watch_word c words (Znth 1 words 0)) (ms_wm M))
          (ms_wcaps M)); [ apply wlists_two_remainder_replace_wm_i__clause_new;
          try lia | apply wlists_two_remainder_replace_wm_j__clause_new;
          rewrite ?Zlength_replace_Znth; try lia ]).

(* Rejoin the updated watcher map after either installation frame is opened. *)
Tactic Notation "msat_cn_refold_install_slots"
    ident(M) ident(c) ident(words) ident(wl)
    ident(Hrem) ident(Hwm0) ident(Hwm1) ident(Hne) :=
  rewrite Hrem;
  rewrite <- Hwm0, <- Hwm1;
  sep_apply (wlists_two_remainder_refold__act_clause_bump wl
      (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0))
      (clause_new_watch_map M c words) (ms_wcaps M)
      ltac:(rewrite clause_new_watch_map_Zlength; lia)
      ltac:(rewrite clause_new_watch_map_Zlength; lia)
      ltac:(rewrite clause_new_watch_map_Zlength; lia) Hne).

Tactic Notation "msat_cn_install_rep_open"
    ident(Hwm_len) ident(Hwcaps_len) ident(Hwatch_word0) ident(Hwatch_word1)
    ident(Hwm0) ident(Hwm1) ident(Hrem) ident(Hshape') :=
  intros s begin clause_out database watch0 watch1 wl lvl M words c
      Hshape Hlen Hidx0 Hidx1 Hne Hdatabase Hwatch0 Hwatch1;
  msat_cn_install_watch_facts M c words wl Hshape Hne
    Hwm_len Hwcaps_len Hwatch_word0 Hwatch_word1 Hwm0 Hwm1 Hrem;
  assert (Hshape' :
      solver_shape (msolver_install_learnt_clause M c words)) by (rewrite
        msolver_install_learnt_clause_gen; apply solver_shape_install; exact Hshape);
  subst database watch0 watch1;
  unfold clause_new_transaction_rest_at, clause_new_frame_at;
  Intros act asg opos rsn trl tgs;
  msat_cn_refold_install_slots M c words wl Hrem Hwm0 Hwm1 Hne;
  sep_apply (clause_db_rep_learnt_snoc_rev__clause_new
      (ms_learnt M) c words).

(* Closing half of the same install refold: reduce the record projections and
   fold the database word list back.  The idents are the solver, clause and
   word-list binders plus the watch-map length fact the opening half poses. *)
Tactic Notation "msat_cn_install_rep_close"
    ident(M) ident(c) ident(words) ident(Hwm_len) :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, solver_scalars_rep,
    solver_fp_rep,
    solver_vecs_rep, solver_trail_array_rep, solver_var_arrays_rep,
    clause_new_scalars_frame, clause_new_vecs_frame,
    clause_new_ptrs_frame, solver_wlists_handle, wlists_rep;
  assert (Hinstall : msolver_install_learnt_clause M c words =
      msolver_install_clause M c words true) by reflexivity;
  rewrite Hinstall;
  msat_install_clause_proj_rw M c words true
      (ms_prob M)
      (ms_learnt M +:: (c, clause_obj_of words true));
  assert (Edbwords :
      map fst (ms_learnt M +:: (c, clause_obj_of words true)) =
      db_words (ms_learnt M) +:: c) by (unfold db_words; rewrite map_app; reflexivity);
  rewrite Edbwords;
  entailer_with lia;
  rewrite clause_new_watch_map_Zlength;
  exact Hwm_len.

(* Installing a two-literal learnt clause into the watch lists (spatial half):
   the transaction frame is opened, both watcher slots are updated and the new
   clause is appended to the learnt database.  Used by the [wl]-named binary
   refold. *)
(* Restore the two binary watcher slots after the caller opens its own frame.
   The learnt and problem branches keep their distinct database introductions. *)
Tactic Notation "msat_cn_refold_updated_slots"
    ident(M) ident(words) ident(wl) ident(Hshape)
    ident(Hi) ident(Hj) ident(Hne) ident(Hcapslen) ident(Hwmlen) :=
  pose proof (solver_shape_wcaps_len M Hshape) as Hcapslen;
  pose proof (solver_shape_wm_len M Hshape) as Hwmlen;
  sep_apply (wlists_two_remainder_update_refold__clause_new
      wl (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0))
      (ms_wm M) (ms_wcaps M)
      (Znth (lit_neg_c (Znth 0 words 0)) (ms_wm M) nil ++
       (tag_of_lit (Znth 1 words 0) :: nil))
      (Znth (lit_neg_c (Znth 1 words 0)) (ms_wm M) nil ++
       (tag_of_lit (Znth 0 words 0) :: nil))
      ltac:(lia) Hi Hj Hne).

Ltac msat_cn_install_spatial_open :=
  intros s wl M words lvl c Hshape Hlen Hi Hj Hne;
  unfold clause_new_transaction_rest_at, clause_new_frame_at;
  Intros act asg opos rsn trl tgs;
  msat_cn_refold_updated_slots M words wl Hshape Hi Hj Hne Hcapslen Hwmlen;
  assert (Hsingle : MiniSatClause.rep c msat_true words |--
      clause_db_rep ((c, {| co_lits := words; co_learnt := true |}) :: nil)) by (simpl;
        entailer_with int_auto);
  sep_apply Hsingle;
  sep_apply (clause_db_rep_app_intro (ms_learnt M)
      ((c, {| co_lits := words; co_learnt := true |}) :: nil)).

(* The pure side of the same refold: the installed state still satisfies
   [solver_shape].  The idents are the solver-state, clause and word-list
   binders and the shape hypothesis the caller introduced; [lrn] is the
   learnt flag of the database the clause goes into (learnt refold: [true],
   generic problem-database branch: [false]). *)
Tactic Notation "msat_cn_install_spatial_split"
    ident(M) ident(c) ident(words) ident(Hshape) constr(lrn) :=
  split_pure_spatial;
  [ | pose proof (solver_shape_install M c words lrn Hshape) as Hshape_install;
      entailer_with int_auto ].

(* Reduce the installed record to its field updates before the entailment closer runs.
   One unfold list serves both installation shapes: the learnt refold, whose
   goal names [msolver_install_learnt_clause], and the selector-parameterised
   generic branch, whose goal names [msolver_install_clause] -- the two are
   convertible, so the [cbn] reaches the same field-update shape either way. *)
Ltac msat_cn_install_spatial_mid :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, wlists_rep, solver_scalars_rep,
    solver_fp_rep, solver_vecs_rep, solver_var_arrays_rep,
    solver_trail_array_rep, clause_new_scalars_frame,
    clause_new_vecs_frame, clause_new_ptrs_frame, db_words,
    clause_obj_of;
  unfold msolver_install_clause, msolver_propagation_overlay, msolver_propagation_update;
  cbn.

(* Closing half: cancel the spatial atoms, then discharge the watch-map index
   and length residues.  [Hlen] and [Hwmlen] are the word-count and watch-map
   length facts the opening half establishes. *)
Tactic Notation "msat_cn_install_spatial_close"
    ident(Hlen) ident(Hwmlen) :=
  split_pure_spatial;
  [ Intros; msat_cancel_sound; entailer_with int_auto;
    unfold clause_new_watch_map, wmap_push_word, clause_watch_word; rewrite Hlen;
    simpl; rewrite Znth_replace_Znth_Diff by auto; unfold clause_obj_of;
    rewrite map_app; simpl; entailer_with int_auto;
    unfold solver_wlists_handle, DoubleArray.seg, IntArray.seg,
      PtrArray.seg, CharArray.seg; entailer_with int_auto
  | entailer_with int_auto; rewrite clause_new_watch_map_Zlength;
    exact Hwmlen ].

(* The cancel-projection leaves the abstract view unchanged: only the cancelled
   suffix loses its reasons, and those variables are no longer on the trail.
   The [_test] fork unfolds [msolver_set_root] at its own call site first. *)
Ltac msat_view_cancel_project :=
  intros n M level orderpos order order_cap root Hwf Hlevel;
  unfold msolver_view, view_of, msolver_cancel_project,
    msolver_core_heap_update, msolver_clauses, msolver_db;
  simpl;
  f_equal; simpl; try reflexivity;
  apply functional_extensionality; intros v;
  destruct (trail_pos (mt_cancel (ms_core M) level) v) as [k|] eqn:Hpos;
  [ | reflexivity ];
  f_equal;
  apply clear_reason_fun_notin;
  intros Hin;
  assert (Hkeep : In v
    (map lit_var_c (ztake (Znth level (mt_lim (ms_core M)) 0)
      (mt_trail (ms_core M)))))
    by (rewrite <- mt_cancel_trail;
        unfold trail_pos in Hpos;
        exact (find_var_pos_some_in v _ k Hpos));
  eapply NoDup_app_disjoint;
  [ rewrite <- map_ztake_zdrop; exact (mtw_trail_nodup Hwf)
  | exact Hkeep
  | exact Hin ].

(* [db_complete] survives a cancel-projection: the clause is either still
   present or was satisfied at the root.  Shared by the solver_search and
   solver_canceluntil_capacity forms. *)
Ltac msat_db_complete_cancel_project :=
  intros n F M level orderpos order order_cap root Hwf Hlevel Hdb c Hin;
  destruct (Hdb c Hin) as [Hpresent|Hroot];
  [ left; exact Hpresent
  | right; simpl;
    apply root_satisfied_cancel__canceluntil_cap
      with (n := n); assumption ].

(* [reason_head_ok] survives a cancel-projection: the head variable is not in
   the cancelled suffix, so its reason word is untouched. *)
Ltac msat_reason_head_ok_cancel_project :=
  intros n M level orderpos order order_cap root
    Htrail Hlevel Hwords Hsize Hhead;
  unfold reason_head_ok in *;
  unfold msolver_cancel_project, msolver_core_heap_update,
    msolver_db, heap_of_lists in *; simpl in *;
  intros v co Hv Htag Hnz Hin;
  set (suffix := zdrop (Znth level (mt_lim (ms_core M)) 0)
    (mt_trail (ms_core M)));
  assert (Hrange : forall x, In x suffix ->
    0 <= lit_var_c x < Zlength (ms_reason_words M))
    by (intros x Hx; rewrite Hwords; apply lit_var_c_in_range;
        pose proof (mtw_trail_lits Htrail) as Hlits;
        rewrite Forall_forall in Hlits; apply Hlits;
        apply In_zdrop in Hx; exact Hx);
  assert (Hnot : ~ In v (map lit_var_c suffix))
    by (intros Hinv;
        pose proof (clear_vars_in suffix (ms_reason_words M) v) as Hz;
        specialize (Hz ltac:(rewrite Hwords, Hsize; exact Hv) Hrange Hinv);
        unfold suffix in Hz; rewrite Hz in Hnz; contradiction);
  assert (Hword : Znth v (clear_vars suffix (ms_reason_words M)) 0 =
    Znth v (ms_reason_words M) 0)
    by (apply clear_vars_notin;
        [ rewrite Hwords, Hsize; exact Hv | exact Hrange | exact Hnot ]);
  unfold suffix in Hword; rewrite Hword in Htag, Hnz, Hin;
  eapply Hhead; eauto.

(* [binary_reason_same_level] survives a cancel-projection, by the same
   suffix-membership case split as [reason_head_ok]. *)
Ltac msat_binary_reason_cancel_project :=
  intros n M level orderpos order order_cap root
    Htrail Hlevel Hwords Hsize Hbin;
  unfold binary_reason_same_level in *;
  unfold msolver_cancel_project, msolver_core_heap_update,
    heap_of_lists in *; simpl in *;
  intros v Hv Htag;
  set (suffix := zdrop (Znth level (mt_lim (ms_core M)) 0)
    (mt_trail (ms_core M)));
  assert (Hrange : forall x, In x suffix ->
    0 <= lit_var_c x < Zlength (ms_reason_words M))
    by (intros x Hx; rewrite Hwords; apply lit_var_c_in_range;
        pose proof (mtw_trail_lits Htrail) as Hlits;
        rewrite Forall_forall in Hlits; apply Hlits;
        apply In_zdrop in Hx; exact Hx);
  destruct (List.in_dec Z.eq_dec v (map lit_var_c suffix)) as [Hin|Hnot];
  [ pose proof (clear_vars_in suffix (ms_reason_words M) v) as Hz;
    specialize (Hz ltac:(rewrite Hwords, Hsize; exact Hv) Hrange Hin);
    unfold suffix in Hz; rewrite Hz in Htag; discriminate
  | assert (Hword : Znth v (clear_vars suffix (ms_reason_words M)) 0 =
      Znth v (ms_reason_words M) 0)
      by (apply clear_vars_notin;
          [ rewrite Hwords, Hsize; exact Hv | exact Hrange | exact Hnot ]);
    assert (Hword_full := Hword); unfold suffix in Hword_full;
    rewrite Hword_full in Htag; rewrite Hword;
    destruct (Hbin v Hv Htag) as [Hlitwf [Hsame Hdifferent]];
    exact (conj Hlitwf (conj Hsame Hdifferent)) ].

(* Eliminate the two impossible enqueue outcomes before exposing the successful frame. *)
Tactic Notation "msat_enqueue_refold_transition"
    ident(n) ident(cap) ident(qtail) ident(assigns) ident(levels) ident(reasons)
    ident(trail) ident(lim) ident(lim_cap) ident(l) ident(Hfresh) ident(rsn) ident(trl) ident(Htransition)
    ident(qtail') ident(assigns') ident(levels') ident(reasons') ident(trail') :=
  subst n; subst cap; subst qtail; subst assigns; subst levels;
  subst reasons; subst trail; subst lim; subst lim_cap;
  unfold enqueue_post_at;
  Intros qtail' assigns' levels' reasons' trail';
  unfold enqueue_state_at;
  Intros rsn trl;
  rename H into Htransition;
  unfold enqueue_transition in Htransition;
  destruct Htransition as [Hsame | [Hconflict | Hnew]];
  [ destruct Hsame as [Hsame _]; rewrite Hfresh in Hsame;
    pose proof (lit_sig_nonzero l); lia
  | destruct Hconflict as [Hne _]; contradiction
  | destruct Hnew as [Hz [_ [Hassigns' [Hlevels' [Hreasons' [Htrail' Hqtail']]]]]];
    subst assigns'; subst levels'; subst reasons'; subst trail'; subst qtail' ].

(* Projection reduction and array closing are identical after the frame binder is selected. *)
Tactic Notation "msat_enqueue_refold_close" ident(Hshape) :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_enqueue_scalars_frame,
    solver_enqueue_vecs_frame, msolver_enqueue_fresh,
    msolver_propagation_overlay, msolver_propagation_update;
  unfold solver_fp_rep, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_trail_array_rep,
    solver_levels_slice_at;
  cbn [mt_enqueue mt_push ms_size ms_cap ms_qtail
      ms_capacity_pending_qhead ms_capacity_root_propagation_pending ms_core
      ms_root_level ms_reason_words ms_reason_of ms_prob ms_learnt
      ms_prob_cap ms_learnt_cap ms_binary ms_binary_lits ms_wm ms_wcaps
      ms_activity ms_orderpos ms_order ms_order_cap ms_lim_cap ms_model
      ms_model_cap ms_tags ms_tagged ms_tagged_cap ms_stack ms_stack_cap
      ms_var_inc ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed
      ms_progress ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats];
  entailer_with lia;
  try exact Hshape;
  try (rewrite Zlength_replace_Znth; lia);
  try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
  cbn;
  unfold DoubleArray.seg, IntArray.seg, CharArray.seg, PtrArray.seg;
  cbn;
  unfold store_double;
  entailer_with lia.

(* Refolding the removable-check scratch state back into the analyze-time
   representation.  The residual and the return-3 exit share one script; the
   idents name the pointers [Intros] recovers from the frame. *)
Tactic Notation "msat_removable_scratch_refold"
    ident(wl) ident(act) ident(asg) ident(opos) :=
  intros s M rsn lvl trl tgs tagged_ptr tagged_cap stack stack_cap wl Hshape;
  sep_apply veci_rep_at_rep;
  unfold solver_removable_frame_at at 1;
  Intros act asg opos;
  unfold solver_rep_analyze_at;
  Exists act asg opos;
  unfold solver_rep_at;
  match goal with |- ?P |-- _ => change (P |-- “ solver_shape M ” &&
      (solver_scalars_rep s M ** solver_fp_rep s M **
       (vecp_rep &(s # "solver_t" ->ₛ "clauses")
          (map fst (ms_prob M)) (ms_prob_cap M) **
        vecp_rep &(s # "solver_t" ->ₛ "learnts")
          (map fst (ms_learnt M)) (ms_learnt_cap M) **
        veci_rep &(s # "solver_t" ->ₛ "tagged")
          (ms_tagged M) tagged_cap **
        veci_rep &(s # "solver_t" ->ₛ "stack") stack stack_cap **
        veci_rep &(s # "solver_t" ->ₛ "order")
          (ms_order M) (ms_order_cap M) **
        veci_rep &(s # "solver_t" ->ₛ "trail_lim")
          (mt_lim (ms_core M)) (ms_lim_cap M) **
        veci_rep &(s # "solver_t" ->ₛ "model")
          (ms_model M) (ms_model_cap M)) **
       (&(s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
        &(s # "solver_t" ->ₛ "activity") # Ptr |-> act **
        &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
        &(s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
        &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
        &(s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
        &(s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
        &(s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
       (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
        DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
        CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
        CharArray.undef_seg asg (ms_size M) (ms_cap M) **
        IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
        IntArray.undef_seg opos (ms_size M) (ms_cap M) **
        PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
        PtrArray.undef_seg rsn (ms_size M) (ms_cap M) **
        CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
        CharArray.undef_seg tgs (ms_size M) (ms_cap M)) **
       solver_trail_array_rep M trl **
       wlists_rep wl (ms_size M) (ms_wm M) (ms_wcaps M) **
       clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
       MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
       stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats M) **
       solver_levels_slice_at s M lvl)) end;
  unfold solver_scalars_rep, clause_new_scalars_frame,
    solver_levels_slice_at;
  entailer_with lia.

(* Rejoining an analyze-time [veci] with the reason/level slices: the two
   statements below differ only in the order of the spatial atoms. *)
Tactic Notation "msat_reason_levels_veci_join"
    ident(a) ident(b) ident(c) ident(d) :=
  intros v p words cap s M rsn lvl trl tgs a Hshape Hlen Hcap;
  unfold solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_rep_analyze_at, solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_scalars_rep, solver_vecs_rep,
    clause_new_scalars_frame, veci_rep_at, veci_size_addr,
    veci_cap_addr, veci_ptr_addr;
  Intros b c d;
  Exists b c d;
  entailer_with lia.

(* The five [learnt_cmp_result_*_two] statements below differ only in the `**`
   order of the spatial atoms; the reassociation proof is one script.  Lifted
   once per hypothesis shape (the intro list is part of the shared text). *)
Ltac msat_learnt_cmp_lt_two_join :=
  intros db activities x xlits xa y ylits ya
    Hxpos Hxeven Hxnonneg Hypos Hyeven Hynonneg Hxlen Hycond;
  pose proof (learnt_cmp_result_lt_two__clause_cmp
    db activities x xlits xa y ylits ya Hxlen Hycond) as Hlemma;
  unfold learnt_clause_snapshot_raw in Hlemma;
  etransitivity; [ | exact Hlemma ]; entailer_with lia.

(* Same reassociation, [stop] direction (one packed condition hypothesis). *)
Ltac msat_learnt_cmp_stop_two_join :=
  intros db activities x xlits xa y ylits ya
    Hxpos Hxeven Hxnonneg Hypos Hyeven Hynonneg Hcondition;
  pose proof (learnt_cmp_result_stop_two__clause_cmp
    db activities x xlits xa y ylits ya Hcondition) as Hlemma;
  unfold learnt_clause_snapshot_raw in Hlemma;
  etransitivity; [ | exact Hlemma ]; entailer_with lia.

(* Same reassociation for the aliased (x = y) comparison. *)
Ltac msat_learnt_cmp_stop_alias_join :=
  intros db activities x xlits xa Hxpos Hxeven Hxnonneg;
  pose proof (learnt_cmp_result_stop_alias__clause_cmp
    db activities x xlits xa Hxnonneg) as Hlemma;
  unfold learnt_clause_snapshot_raw in Hlemma;
  etransitivity; [ | exact Hlemma ]; entailer_with lia.

(* Shape preservation under [msolver_remove_clause] is the same computation for
   the learnt (true) and problem (false) side. *)
Ltac msat_shape_remove_clause :=
  intros M p wm stats Hshape Hwm Hstats;
  unfold solver_shape, msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update in *;
  cbn in *; tauto.

(* Refolding the post-state of [solver_assume]: substitute the entry-state
   equations, pick the grown trail-limit capacity and split the enqueue
   transition into its three cases.  [lc] names the capacity witness. *)
Tactic Notation "msat_assume_post_open" ident(lc) :=
  intros s asg lvl l n cap qtail assigns levels reasons trail lim lim_cap M
      Hn Hcap Hq Hassigns Hlevels Hreasons Htrail Hlim Hlimcap
      Hshape Hroom Hpending Hdrain Hfresh;
  subst n;
  subst cap;
  subst qtail;
  subst assigns;
  subst levels;
  subst reasons;
  subst trail;
  subst lim;
  subst lim_cap;
  assert (Htrailq : Zlength (mt_trail (ms_core M)) = ms_qtail M) by (unfold solver_shape in Hshape;
    tauto);
  unfold assume_post_at;
  Intros lc;
  Exists lc;
  entailer_with lia;
  assert (Hshapenew : solver_shape (msolver_assume M l lc)) by (eapply
    solver_shape_assume__search; eauto);
  unfold enqueue_post_at;
  Intros qtail' assigns' levels' reasons' trail';
  unfold enqueue_state_at;
  Intros rsn trl;
  unfold enqueue_transition in *;
  match goal with
    | Ht : _ \/ (_ \/ _) |- _ =>
        destruct Ht as [Hsame | [Hconflict | Hnew]]
    end.

(* The "fresh assignment" case of the same transition: substitute the five
   updated components and open the enqueue frame. *)
Tactic Notation "msat_assume_post_new"
    ident(hn) ident(qt) ident(ag) ident(lv) ident(rw) ident(tr) :=
  destruct hn as
        [Hz [_ [Hassigns' [Hlevels' [Hreasons' [Htrail' Hqtail']]]]]];
  subst ag; subst lv; subst rw; subst tr; subst qt;
  unfold solver_assume_frame, solver_enqueue_frame_with_scalars, solver_enqueue_cells_at;
  Intros wl act opos tgs.

(* Closing half: reduce the assume record to its field updates.  [Hdrain] and
   [Htrailq] are the queue-drained and trail-length facts. *)
Tactic Notation "msat_assume_post_close" ident(Hdrain) ident(Htrailq) :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_assume_scalars_frame,
    solver_enqueue_vecs_frame, msolver_assume;
  unfold solver_fp_rep, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_trail_array_rep,
    solver_levels_slice_at;
  try rewrite Hdrain;
  try rewrite Htrailq;
  cbn [mt_decide mt_push ms_size ms_cap ms_qtail ms_capacity_pending_qhead
        ms_capacity_root_propagation_pending ms_core ms_root_level
        ms_reason_words ms_reason_of ms_prob ms_learnt ms_prob_cap
        ms_learnt_cap ms_binary ms_binary_lits ms_wm ms_wcaps ms_activity
        ms_orderpos ms_order ms_order_cap ms_lim_cap ms_model ms_model_cap
        ms_tags ms_tagged ms_tagged_cap ms_stack ms_stack_cap ms_var_inc
        ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
        ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats];
  entailer_with lia.

(* Opening the simplify-time reason/level representation at a database
   selector: the script is the same for selector 0 and selector 1. *)
Tactic Notation "msat_rep_reasons_simplify_open"
    ident(wl) ident(act) ident(asg) ident(opos) ident(trl) ident(tgs) :=
  intros s M reasons lvl Hlim;
  unfold solver_rep_reasons_levels_at;
  Intros wl act asg opos trl tgs;
  Exists wl asg;
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_db_rest_at,
    solver_simplify_clause_frame_at,
    solver_selected_vec, solver_selected_db, solver_selected_cap,
    solver_other_db_vec_rep, solver_other_clause_db_rep,
    solver_wlists_handle, solver_scalars_rep, clause_new_scalars_frame,
    solver_vecs_rep, solver_trail_array_rep, solver_levels_slice_at,
    db_words;
  Exists act opos trl tgs;
  cbn; rewrite Hlim; entailer_with lia.

(* Shared script for a pairwise literal update that no live reason owns.
   Both invariant bundles are rebuilt by the same eleven transports; the
   projections that read the old bundle are the arguments. *)
(* Transport the database facts after an unowned clause-literal update.
   Watcher-map exactness and the new solver shape belong to the caller: one
   wrapper retains the old map, while the other supplies a replacement map.
   Output identifiers keep the existing invariant-closing scripts unchanged. *)
Tactic Notation "msat_inv_db_transport"
    ident(n) ident(F) ident(M) ident(p) ident(old_lits) ident(new_lits)
    ident(prob') ident(learnt') constr(wm') constr(wcaps')
    ident(Hweak) ident(Hupdate) ident(Hperm) ident(Hnoowner)
    uconstr(p_db_wf) uconstr(p_db_matches) uconstr(p_db_implied)
    uconstr(p_db_complete) uconstr(p_prob_db) uconstr(p_learnt_db)
    uconstr(p_binary_out) uconstr(p_reasons_mem) uconstr(p_reason_head)
    uconstr(p_size)
    ident(Hdbwf) ident(Hmatches) ident(Himplied) ident(Hcomplete)
    ident(Hprobdb) ident(Hlearntdb) ident(Hbinary) ident(Hreasons) ident(Hhead) :=
  pose proof Hupdate as Hupdate0;
  pose proof (db_pair_lits_update_prob_entry_bi__propagate_dbu
    _ _ _ _ _ _ _ Hperm Hupdate) as [Hprobforward Hprobreverse];
  pose proof (db_pair_lits_update_learnt_entry_bi__propagate_dbu
    _ _ _ _ _ _ _ Hperm Hupdate) as [Hlearntforward Hlearntreverse];
  assert (Hdbwf : db_wf n (prob' ++ learnt'))
    by (exact (@db_pair_lits_update_db_wf__propagate_dbu
      n (ms_prob M) (ms_learnt M) p old_lits new_lits prob' learnt'
      (p_db_wf Hweak) Hperm Hupdate));
  assert (Hmatches : db_matches_cnf F
      (msolver_propagation_db_wmap_update
        M prob' learnt' wm' wcaps'))
    by (unfold db_matches_cnf,
          msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update; cbn;
        eapply db_matches_entries_transport__propagate_dbu;
        [exact Hprobforward|exact (p_db_matches Hweak)]);
  assert (Himplied : db_implied F
      (msolver_propagation_db_wmap_update
        M prob' learnt' wm' wcaps'))
    by (unfold db_implied,
          msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update; cbn;
        eapply db_implied_entries_transport__propagate_dbu;
        [exact Hlearntforward|exact (p_db_implied Hweak)]);
  assert (Hcomplete : db_complete F
      (msolver_propagation_db_wmap_update
        M prob' learnt' wm' wcaps'))
    by (unfold db_complete,
          msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update; cbn;
        eapply db_complete_entries_transport__propagate_dbu;
        [exact Hprobreverse|exact (p_db_complete Hweak)]);
  destruct (db_pair_lits_update_prob_learnt__propagate_dbu
    _ _ _ _ _ _ _ (p_prob_db Hweak) (p_learnt_db Hweak) Hupdate)
    as [Hprobdb Hlearntdb];
  destruct (db_pair_lits_update_words__propagate
    _ _ _ _ _ _ _ Hupdate) as [Hprobkeys Hlearntkeys];
  assert (Hbinary : ~ In (ms_binary M) (map fst (prob' ++ learnt')))
    by (intros Hin; apply (p_binary_out Hweak);
        unfold msolver_db; rewrite map_app in Hin;
        rewrite Hprobkeys, Hlearntkeys in Hin;
        rewrite map_app; exact Hin);
  assert (Hreasons : reasons_match n (ms_core M) (prob' ++ learnt')
      (ms_reason_words M) (ms_reason_of M))
    by (unfold reasons_match in *; intros v Hv;
        pose proof (p_reasons_mem Hweak v Hv) as Hold;
        unfold reason_word_ok in Hold |- *;
        destruct ((Znth v (ms_reason_words M) 0 =? 0)%Z) eqn:Hz;
          [exact Hold|];
        destruct (is_tag (Znth v (ms_reason_words M) 0)) eqn:Htag;
          [exact Hold|];
        destruct Hold as [Hassigned [obj [Hlookup Hr]]];
        split; [exact Hassigned|]; exists obj; split; [|exact Hr];
        apply (proj1 (db_pair_lits_update_other_iff__propagate_dbu
          _ _ _ _ _ _ _ _ _ Hupdate0 (Hnoowner v Hv)));
        exact Hlookup);
  assert (Hhead : reason_head_ok
      (msolver_propagation_db_wmap_update
        M prob' learnt' wm' wcaps'))
    by (unfold reason_head_ok in *;
        intros v obj Hv Htag Hnz Hlookup;
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update in *; cbn in *;
        apply (p_reason_head Hweak v obj); try assumption;
        apply (proj2 (db_pair_lits_update_other_iff__propagate_dbu
          _ _ _ _ _ _ _ _ _ Hupdate0
          (Hnoowner v ltac:(rewrite (p_size Hweak); exact Hv))));
        exact Hlookup).

Tactic Notation "msat_inv_db_pair_lits_no_owner"
    uconstr(p_db_wf) uconstr(p_db_matches) uconstr(p_db_implied)
    uconstr(p_db_complete) uconstr(p_prob_db) uconstr(p_learnt_db)
    uconstr(p_binary_out) uconstr(p_reasons_mem) uconstr(p_reason_head)
    uconstr(p_size) uconstr(p_wmap_exact) :=
  intros n F A_arr A_x M p old_lits new_lits prob' learnt'
    Hweak Hupdate Hperm Hexpected Hnoowner;
  let Hdbwf := fresh "Hdbwf" in
  let Hmatches := fresh "Hmatches" in
  let Himplied := fresh "Himplied" in
  let Hcomplete := fresh "Hcomplete" in
  let Hprobdb := fresh "Hprobdb" in
  let Hlearntdb := fresh "Hlearntdb" in
  let Hbinary := fresh "Hbinary" in
  let Hreasons := fresh "Hreasons" in
  let Hhead := fresh "Hhead" in
  msat_inv_db_transport n F M p old_lits new_lits
    prob' learnt' (ms_wm M) (ms_wcaps M) Hweak Hupdate Hperm Hnoowner
    p_db_wf p_db_matches p_db_implied p_db_complete p_prob_db p_learnt_db
    p_binary_out p_reasons_mem p_reason_head p_size
    Hdbwf Hmatches Himplied Hcomplete Hprobdb Hlearntdb Hbinary Hreasons Hhead;
  assert (Hwmap : wmap_exact n (prob' ++ learnt') (ms_wm M))
    by (destruct (p_wmap_exact Hweak) as [Hlen Hexact];
        split; [exact Hlen|];
        intros l Hl; eapply Permutation_trans; [apply Hexact; exact Hl|];
        apply Hexpected);
  unfold msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update; cbn;
  constructor; try exact Hdbwf; try exact Hmatches; try exact Himplied;
    try exact Hcomplete; try exact Hlearntdb; try exact Hprobdb;
    try exact Hbinary; try exact Hreasons; try exact Hhead;
    try exact Hwmap; try apply Hweak.

(* Shared script for the watcher-map move.  The weak and the assuming bundle
   run the same ten database transports; only the projections that feed them
   differ, so those are the arguments. *)
Tactic Notation "msat_inv_db_wmap_move"
    uconstr(p_db_wf) uconstr(p_db_matches) uconstr(p_db_implied)
    uconstr(p_db_complete) uconstr(p_prob_db) uconstr(p_learnt_db)
    uconstr(p_binary_out) uconstr(p_reasons_mem) uconstr(p_reason_head)
    uconstr(p_size) uconstr(p_shape) :=
  intros n F A_arr A_x M current old_lits new_lits prob_after
    learnt_after wm_after wcaps_after Hweak Hupdate Hperm Hnoowner
    Hwmlen Hcapslen Hwmap;
  let Hdbwf := fresh "Hdbwf" in
  let Hmatches := fresh "Hmatches" in
  let Himplied := fresh "Himplied" in
  let Hcomplete := fresh "Hcomplete" in
  let Hprobdb := fresh "Hprobdb" in
  let Hlearntdb := fresh "Hlearntdb" in
  let Hbinary := fresh "Hbinary" in
  let Hreasons := fresh "Hreasons" in
  let Hhead := fresh "Hhead" in
  msat_inv_db_transport n F M current old_lits new_lits
    prob_after learnt_after wm_after wcaps_after Hweak Hupdate Hperm Hnoowner
    p_db_wf p_db_matches p_db_implied p_db_complete p_prob_db p_learnt_db
    p_binary_out p_reasons_mem p_reason_head p_size
    Hdbwf Hmatches Himplied Hcomplete Hprobdb Hlearntdb Hbinary Hreasons Hhead;
  assert (Hshape : solver_shape
      (msolver_propagation_db_wmap_update
        M prob_after learnt_after wm_after wcaps_after))
    by (pose proof (p_shape Hweak) as Hshape0;
        unfold solver_shape, msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update in Hshape0 |- *;
        cbn in Hshape0 |- *; rewrite Hwmlen, Hcapslen; exact Hshape0);
  unfold msolver_propagation_db_wmap_update,
    msolver_propagation_overlay, msolver_propagation_update in *; cbn in *;
  destruct Hweak; constructor; assumption.

(* Direct scan-step closer for the 24 fresh scan-same/scan-move owners. *)
(* Each caller passes its clause/watch witnesses and its prefix, index and *)
(* memory-equality facts explicitly; generated hypothesis names stay local. *)
Tactic Notation "msat_propagate_scan_step_close" constr(a) constr(cc) constr(ii)
    constr(wm) constr(sc) constr(hpre) constr(hidx) constr(hmem) :=
  Exists 2 (Znth a cc 0);
  split_pure_spatial;
  [ unfold solver_propagation_scan_core_at;
    unfold PtrArray.seg, stats_propagate_scan;
    set_String_name; sepcon_assoc_change; sepcon_cancel; subst_all_strings;
    unfold Znth; cbn; csimpl; intros m Hm; exact Hm
  | assert (Hii0 : 0 <= ii < Zlength wm) by lia;
    assert (Hscan : Znth ii wm 0 = sc) by
      (rewrite hpre; rewrite app_Znth2 by lia; rewrite hidx;
       replace (ii - ii) with 0 by lia; reflexivity);
    split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia; try tauto;
    rewrite hmem; exact Hscan ].

(* ---------------------------------------------------------------------- *)


(* ---- hoisted from solver_qcp_proof_manual_part2.v ---- *)

(* ---------------------------------------------------------------------- *)
(* Fold-recipe helper.  User: proof_of_solver_analyze_entail_wit_17, in
   solver_qcp_proof_manual_part2.v.  It sits here, with the other hoisted
   helpers, because no statement-equivalent lemma exists in the peel/join set
   above. *)
(* The two statistics cells are spelled as nested C fields at the site and as
   [stats_t] fields off the [stats] sub-object in [stats_rep]; bridge the two
   on a TINY goal (running [csimpl] over the whole 80-atom entailment is what
   made the naive script expensive).  Shared by the join and split direction. *)
Tactic Notation "msat_analyze_frame_bridge"
    ident(p) ident(wl) ident(asg) :=
  intros s M wl;
  set (p := &( s # "solver_t" ->ₛ "stats"));
  assert (Hmax : &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals")
                 = &( p # "stats_t" ->ₛ "max_literals"))
      by (unfold p; csimpl; reflexivity);
  assert (Htot : &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")
                 = &( p # "stats_t" ->ₛ "tot_literals"))
      by (unfold p; csimpl; reflexivity);
  rewrite Hmax, Htot;
  unfold solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame, db_words,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep, stats_rep;
  Intros asg;
  Exists asg;
  entailer_with int_auto.

(* ---------------------------------------------------------------------- *)
(* Normalisation.  At sel = 1 the generalised layer IS the shipped layer    *)
(* (every gate above is `reflexivity`), so rewriting with the gates puts    *)
(* the goal back into exactly the spelling the shipped proofs use, and      *)
(* they run verbatim.  At sel = 0 only the selectors reduce --              *)
(* there is no shipped predicate for the problem arm to reduce TO.          *)
(* ---------------------------------------------------------------------- *)

Ltac cn_at_learnt :=
  try (rewrite ?sel_db_learnt in *);
  try (rewrite ?sel_cap_learnt in *);
  try (rewrite ?sel_vec_learnt in *);
  try (rewrite ?sel_learnt_learnt in *);
  try (rewrite ?cn_F_learnt in *);
  try (rewrite ?sel_other_learnt in *);
  try (rewrite ?sel_other_cap_learnt in *);
  try (rewrite ?sel_other_vec_learnt in *);
  try (rewrite ?msolver_with_clause_caps_gen_learnt in *);
  try (rewrite ?clause_new_vecs_frame_gen_learnt in *);
  try (rewrite ?clause_new_frame_gen_learnt in *);
  try (rewrite ?clause_new_frame_at_gen_learnt in *);
  try (rewrite ?clause_new_transaction_rest_gen_learnt in *);
  try (rewrite ?clause_new_transaction_rest_at_gen_learnt in *);
  try (rewrite ?clause_new_stage_rep_at_gen_learnt in *);
  try (rewrite ?clause_new_caps_progress_gen_learnt in *);
  try (rewrite ?clause_new_capacity_failure_gen_learnt in *);
  try (rewrite ?clause_new_stage_ready_gen_learnt in *);
  try (rewrite ?clause_new_reserved_rooms_gen_learnt in *);
  try (rewrite ?clause_new_success_transition_gen_learnt in *);
  try (rewrite ?clause_new_pre_at_gen_learnt in *);
  try (rewrite ?clause_new_post_at_gen_learnt in *).

(* Normalise the clause_new selector-0 projections in the goal/context. *)
Ltac cn_at_prob :=
  try (rewrite ?sel_db_prob in *);
  try (rewrite ?sel_cap_prob in *);
  try (rewrite ?sel_vec_prob in *);
  try (rewrite ?sel_learnt_prob in *);
  try (rewrite ?cn_F_prob in *);
  try (rewrite ?sel_other_prob in *);
  try (rewrite ?sel_other_cap_prob in *);
  try (rewrite ?sel_other_vec_prob in *).

(* Expose a generic installation stage and restore its watch-map remainder. *)
Tactic Notation "msat_gen_stage_open"
    ident(M) ident(words) ident(wl) ident(Hshape) ident(Hidx0) ident(Hidx1)
    ident(database) ident(watch0) ident(watch1)
    ident(act) ident(asg) ident(opos) ident(rsn) ident(trl) ident(tgs) :=
  unfold clause_new_stage_rep_at_gen; cbn;
  apply coq_prop_andp_left; intros (Hdatabase & Hwatch0 & Hwatch1 & Hne);
  subst database watch0 watch1;
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen;
  Intros act asg opos rsn trl tgs;
  pose proof (solver_shape_wm_len M Hshape) as Hwm_len;
  pose proof (solver_shape_wcaps_len M Hshape) as Hwcaps_len;
  sep_apply (wlists_two_remainder_refold__act_clause_bump wl
    (lit_neg_c (Znth 0 words 0)) (lit_neg_c (Znth 1 words 0))
    (ms_wm M) (ms_wcaps M) ltac:(lia) Hidx0 Hidx1 Hne).

(* Restore the full vector and discharge the common staged transaction footprint. *)
Tactic Notation "msat_full_gen_stage"
    ident(s) ident(begin) ident(clause_out) ident(database) ident(watch0) ident(watch1)
    ident(wl) ident(lvl) ident(M) ident(words) ident(p) ident(Hfull) ident(Hcap) :=
  fold (vecp_size_addr database); fold (vecp_cap_addr database); fold (vecp_ptr_addr database);
  sep_apply (vecp_full_refold__act_clause_bump database p
    (db_words (solver_selected_db 0 M)) (solver_selected_cap 0 M) Hfull Hcap);
  transitivity (clause_new_stage_rep_at_gen
    s begin clause_out database watch0 watch1 wl lvl M words 0);
  [ unfold clause_new_stage_rep_at_gen; cbn; split_pure_spatial;
    [ entailer_with lia | unfold db_words; entailer_with lia ]
  | idtac ].

(* ====================================================================== *)
(* The two SPATIAL install refolds, generalised.                          *)
(*                                                                        *)
(* Mirror, do not symbolise: within an arm the index is a literal, so the  *)
(* sel = 0 arm is the shipped body with the problem-side names -- the      *)
(* frame at sel = 0 holds [ms_learnt] untouched, exactly as the frame at   *)
(* sel = 1 holds [ms_prob].  Arm 1 is the shipped lemma verbatim.          *)
(* ====================================================================== *)

(* The generic install refold (spatial half), problem-database branch: open the
   transaction frame, update both watcher slots and append the new clause to
   the problem database.  One script for the hiding and the [wl]-named form. *)
Tactic Notation "msat_cn_install_spatial_gen_open"
    ident(M) ident(c) ident(words) ident(wl) ident(Hshape)
    ident(Hi) ident(Hj) ident(Hne) :=
  cn_at_prob;
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen,
    clause_new_vecs_frame_gen;
  cn_at_prob;
  Intros act asg opos rsn trl tgs;
  msat_cn_refold_updated_slots M words wl Hshape Hi Hj Hne Hcapslen Hwmlen;
  assert (Hsingle : MiniSatClause.rep c false words |--
        clause_db_rep ((c, {| co_lits := words; co_learnt := false |}) :: nil)) by (simpl;
          entailer_with int_auto);
  sep_apply Hsingle;
  sep_apply (clause_db_rep_app_intro (ms_prob M)
        ((c, {| co_lits := words; co_learnt := false |}) :: nil)).

(* The generic (selector-parameterised) install refold, problem-database
   branch: the same address bookkeeping as the shipped learnt refold, done at
   [sel = 0].  The idents are the binders the caller introduced, so one script
   serves the hiding and the [wl]-named statement. *)
Tactic Notation "msat_cn_install_rep_gen_open"
    ident(M) ident(c) ident(words) ident(wl) ident(database)
    ident(watch0) ident(watch1) ident(Hshape) ident(Hne)
    ident(Hwm_len) ident(Hwcaps_len) ident(Hwatch_word0) ident(Hwatch_word1)
    ident(Hwm0) ident(Hwm1) ident(Hrem) :=
  cn_at_prob;
  msat_cn_install_watch_facts M c words wl Hshape Hne
    Hwm_len Hwcaps_len Hwatch_word0 Hwatch_word1 Hwm0 Hwm1 Hrem;
  assert (Hshape' :
        solver_shape (msolver_install_clause M c words false)) by (apply solver_shape_install;
          exact Hshape);
  subst database watch0 watch1;
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen,
    clause_new_vecs_frame_gen;
  cn_at_prob;
  Intros act asg opos rsn trl tgs;
  msat_cn_refold_install_slots M c words wl Hrem Hwm0 Hwm1 Hne;
  sep_apply (clause_db_rep_snoc_rev_gen (ms_prob M) c words false).

(* Field projections of the installed record, then the database word list.
   Runs after the caller has unfolded its own representation predicate. *)
Tactic Notation "msat_cn_install_rep_gen_mid"
    ident(M) ident(c) ident(words) :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, solver_scalars_rep,
    solver_fp_rep,
    solver_vecs_rep, solver_trail_array_rep, solver_var_arrays_rep,
    clause_new_scalars_frame, clause_new_vecs_frame,
    clause_new_ptrs_frame, solver_wlists_handle, wlists_rep;
  msat_install_clause_proj_rw M c words false
        (ms_prob M +:: (c, clause_obj_of words false))
        (ms_learnt M);
  assert (Edbwords :
        map fst (ms_prob M +:: (c, clause_obj_of words false)) =
        db_words (ms_prob M) +:: c) by (unfold db_words; rewrite map_app; reflexivity);
  rewrite Edbwords.

(* Closing entailment plus the watch-map length residue. *)
Tactic Notation "msat_cn_install_rep_gen_fin" ident(Hwm_len) :=
  entailer_with lia;
  rewrite clause_new_watch_map_Zlength;
  exact Hwm_len.
