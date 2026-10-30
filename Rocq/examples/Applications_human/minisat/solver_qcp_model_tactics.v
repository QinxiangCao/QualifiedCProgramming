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

Ltac msat_rep_levels_cancel_split :=
  intros s M lvl wl;
  unfold solver_rep_levels_wl_at, solver_cancel_owned;
  (Intros; cancel).

Ltac msat_view_cancel_project :=
  intros n M level orderpos order root Hwf Hlevel;
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
   present or was satisfied at the root. *)
Ltac msat_db_complete_cancel_project :=
  intros n F M level orderpos order root Hwf Hlevel Hdb c Hin;
  destruct (Hdb c Hin) as [Hpresent|Hroot];
  [ left; exact Hpresent
  | right; simpl;
    apply root_satisfied_cancel__canceluntil_cap
      with (n := n); assumption ].

(* [reason_head_ok] survives a cancel-projection: the head variable is not in
   the cancelled suffix, so its reason word is untouched. *)
Ltac msat_reason_head_ok_cancel_project :=
  intros n M level orderpos order root
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

Ltac msat_binary_reason_cancel_project :=
  intros n M level orderpos order root
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
    ident(trail) ident(lim) ident(l) ident(Hfresh) ident(rsn) ident(trl) ident(Htransition)
    ident(qtail') ident(assigns') ident(levels') ident(reasons') ident(trail') :=
  subst n; subst cap; subst qtail; subst assigns; subst levels;
  subst reasons; subst trail; subst lim;
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

Tactic Notation "msat_enqueue_refold_close" ident(Hshape) :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_without_qtail_rep,
    solver_vecs_without_lim_rep, msolver_enqueue_fresh,
    msolver_propagation_overlay, msolver_propagation_update;
  unfold solver_fp_rep, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_trail_array_rep,
    solver_levels_slice_at;
  cbn [mt_enqueue mt_push ms_size ms_cap ms_qtail
      ms_capacity_pending_qhead ms_capacity_root_propagation_pending ms_core
      ms_root_level ms_reason_words ms_reason_of ms_prob ms_learnt ms_binary ms_binary_lits ms_wm
      ms_activity ms_orderpos ms_order ms_model ms_tags ms_tagged ms_stack
      ms_var_inc ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed
      ms_progress ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats];
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]);
  try exact Hshape;
  try (rewrite Zlength_replace_Znth; lia);
  try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
  cbn;
  unfold DoubleArray.seg, IntArray.seg, CharArray.seg, PtrArray.seg;
  cbn;
  unfold store_double;
  cancel.

Tactic Notation "msat_removable_scratch_refold"
    ident(wl) ident(act) ident(asg) ident(opos) :=
  intros s M rsn lvl trl tgs tagged_ptr tagged_cap stack wl Hshape;
  sep_apply Veci.rep_at_rep;
  unfold solver_removable_frame_at at 1;
  Intros act asg opos;
  unfold solver_rep_analyze_at;
  Exists act asg opos;
  unfold solver_rep_at;
  match goal with |- ?P |-- _ => change (P |-- “ solver_shape M ” &&
      (solver_scalars_rep s M ** solver_fp_rep s M **
       (Vecp.rep &(s # "solver_t" ->ₛ "clauses")
          (map fst (ms_prob M)) **
        Vecp.rep &(s # "solver_t" ->ₛ "learnts")
          (map fst (ms_learnt M)) **
        Veci.rep &(s # "solver_t" ->ₛ "tagged")
          (ms_tagged M) **
        Veci.rep &(s # "solver_t" ->ₛ "stack") stack **
        Veci.rep &(s # "solver_t" ->ₛ "order")
          (ms_order M) **
        Veci.rep &(s # "solver_t" ->ₛ "trail_lim")
          (mt_lim (ms_core M)) **
        Veci.rep &(s # "solver_t" ->ₛ "model")
          (ms_model M)) **
       (&(s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
        &(s # "solver_t" ->ₛ "activity") # Ptr |-> act **
        &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
        &(s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
        &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
        &(s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
        &(s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
        &(s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
       (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
        solver_double_tail act (ms_size M) (ms_cap M) **
        CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
        solver_char_tail asg (ms_size M) (ms_cap M) **
        IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
        solver_int_tail opos (ms_size M) (ms_cap M) **
        PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
        solver_ptr_tail rsn (ms_size M) (ms_cap M) **
        CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
        solver_char_tail tgs (ms_size M) (ms_cap M)) **
       solver_trail_array_rep M trl **
       wlists_rep wl (ms_size M) (ms_wm M) **
       clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
       binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
       stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats M) **
       solver_levels_slice_at s M lvl)) end;
  unfold solver_scalars_rep, clause_new_scalars_frame,
    solver_levels_slice_at;
  msat_entailer_with ltac:(first [assumption | lia]).

Ltac msat_learnt_cmp_lt_two_join :=
  intros db activities x xlits xa y ylits ya
    Hxpos Hxeven Hxnonneg Hypos Hyeven Hynonneg Hxlen Hycond;
  pose proof (learnt_cmp_result_lt_two__clause_cmp
    db activities x xlits xa y ylits ya Hxlen Hycond) as Hlemma;
  unfold learnt_clause_snapshot_raw in Hlemma;
  sep_apply_r_atomic Hlemma; (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).

Ltac msat_learnt_cmp_stop_two_join :=
  intros db activities x xlits xa y ylits ya
    Hxpos Hxeven Hxnonneg Hypos Hyeven Hynonneg Hcondition;
  pose proof (learnt_cmp_result_stop_two__clause_cmp
    db activities x xlits xa y ylits ya Hcondition) as Hlemma;
  unfold learnt_clause_snapshot_raw in Hlemma;
  sep_apply_r_atomic Hlemma; (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).

Ltac msat_learnt_cmp_stop_alias_join :=
  intros db activities x xlits xa Hxpos Hxeven Hxnonneg;
  pose proof (learnt_cmp_result_stop_alias__clause_cmp
    db activities x xlits xa Hxnonneg) as Hlemma;
  unfold learnt_clause_snapshot_raw in Hlemma;
  sep_apply_r_atomic Hlemma; (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).

Ltac msat_shape_remove_clause :=
  intros M p wm stats Hshape Hwm Hstats;
  unfold solver_shape, msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update in *;
  cbn in *; tauto.

Tactic Notation "msat_assume_post_open" :=
  intros s asg lvl l n cap qtail assigns levels reasons trail lim M
      Hn Hcap Hq Hassigns Hlevels Hreasons Htrail Hlim
      Hshape Hroom Hpending Hdrain Hfresh;
  subst n;
  subst cap;
  subst qtail;
  subst assigns;
  subst levels;
  subst reasons;
  subst trail;
  subst lim;
  assert (Htrailq : Zlength (mt_trail (ms_core M)) = ms_qtail M) by (unfold solver_shape in Hshape;
    tauto);
  unfold assume_post_at;
  assert (Hshapenew : solver_shape (msolver_assume M l)) by (eapply
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

Tactic Notation "msat_assume_post_close" ident(Hdrain) ident(Htrailq) :=
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_assume_scalars_frame,
    solver_vecs_without_lim_rep, msolver_assume;
  unfold solver_fp_rep, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_trail_array_rep,
    solver_levels_slice_at;
  try rewrite Hdrain;
  try rewrite Htrailq;
  cbn [mt_decide mt_push ms_size ms_cap ms_qtail ms_capacity_pending_qhead
        ms_capacity_root_propagation_pending ms_core ms_root_level
        ms_reason_words ms_reason_of ms_prob ms_learnt ms_binary ms_binary_lits ms_wm ms_activity
        ms_orderpos ms_order ms_model
        ms_tags ms_tagged ms_stack ms_var_inc
        ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
        ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats];
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).

Tactic Notation "msat_inv_db_transport"
    ident(n) ident(F) ident(M) ident(p) ident(old_lits) ident(new_lits)
    ident(prob') ident(learnt') constr(wm')
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
        M prob' learnt' wm'))
    by (unfold db_matches_cnf,
          msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update; cbn;
        eapply db_matches_entries_transport__propagate_dbu;
        [exact Hprobforward|exact (p_db_matches Hweak)]);
  assert (Himplied : db_implied F
      (msolver_propagation_db_wmap_update
        M prob' learnt' wm'))
    by (unfold db_implied,
          msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update; cbn;
        eapply db_implied_entries_transport__propagate_dbu;
        [exact Hlearntforward|exact (p_db_implied Hweak)]);
  assert (Hcomplete : db_complete F
      (msolver_propagation_db_wmap_update
        M prob' learnt' wm'))
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
        M prob' learnt' wm'))
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
    prob' learnt' (ms_wm M) Hweak Hupdate Hperm Hnoowner
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

Tactic Notation "msat_inv_db_wmap_move"
    uconstr(p_db_wf) uconstr(p_db_matches) uconstr(p_db_implied)
    uconstr(p_db_complete) uconstr(p_prob_db) uconstr(p_learnt_db)
    uconstr(p_binary_out) uconstr(p_reasons_mem) uconstr(p_reason_head)
    uconstr(p_size) uconstr(p_shape) :=
  intros n F A_arr A_x M current old_lits new_lits prob_after
    learnt_after wm_after Hweak Hupdate Hperm Hnoowner
    Hwmlen Hwmap;
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
    prob_after learnt_after wm_after Hweak Hupdate Hperm Hnoowner
    p_db_wf p_db_matches p_db_implied p_db_complete p_prob_db p_learnt_db
    p_binary_out p_reasons_mem p_reason_head p_size
    Hdbwf Hmatches Himplied Hcomplete Hprobdb Hlearntdb Hbinary Hreasons Hhead;
  assert (Hshape : solver_shape
      (msolver_propagation_db_wmap_update
        M prob_after learnt_after wm_after))
    by (pose proof (p_shape Hweak) as Hshape0;
        unfold solver_shape, msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update in Hshape0 |- *;
        cbn in Hshape0 |- *; rewrite Hwmlen; exact Hshape0);
  unfold msolver_propagation_db_wmap_update,
    msolver_propagation_overlay, msolver_propagation_update in *; cbn in *;
  destruct Hweak; constructor; assumption.

Tactic Notation "msat_propagate_scan_step_close" constr(a) constr(cc) constr(ii)
    constr(wm) constr(sc) constr(hpre) constr(hidx) constr(hmem) :=
  Exists 2 (Znth a cc 0);
  split_pure_spatial;
  [ unfold solver_propagation_scan_core_at;
    unfold PtrArray.seg, stats_propagate_scan;
    msat_cancel_sound;
    unfold Znth; cbn; csimpl;
    lazymatch goal with |- ?A |-- ?B => unify A B; change (A |-- A) end; cancel
  | assert (Hii0 : 0 <= ii < Zlength wm) by lia;
    assert (Hscan : Znth ii wm 0 = sc) by
      (rewrite hpre; rewrite app_Znth2 by lia; rewrite hidx;
       replace (ii - ii) with 0 by lia; reflexivity);
    split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia; try tauto;
    rewrite hmem; exact Hscan ].

(* Reconcile nested statistics addresses on isolated equalities;
   [csimpl] over the whole solver entailment is expensive. *)
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
  unfold p, solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame, db_words,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep, stats_rep;
  Intros asg;
  Exists asg;
  Intros;
  split_pure_spatial; [ cancel | dump_pre_spatial; lia ].

Ltac cn_at_learnt :=
  try (rewrite ?sel_db_learnt in *);
  try (rewrite ?sel_vec_learnt in *);
  try (rewrite ?sel_learnt_learnt in *);
  try (rewrite ?cn_F_learnt in *);
  try (rewrite ?sel_other_learnt in *);
  try (rewrite ?sel_other_vec_learnt in *);
  try (rewrite ?clause_new_frame_at_gen_learnt in *).

Ltac cn_at_prob :=
  try (rewrite ?sel_db_prob in *);
  try (rewrite ?sel_vec_prob in *);
  try (rewrite ?sel_learnt_prob in *);
  try (rewrite ?cn_F_prob in *);
  try (rewrite ?sel_other_prob in *);
  try (rewrite ?sel_other_vec_prob in *).
