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

(* This part covers ten C functions, in file order: clause_is_lit,
   clause_read_lit, solver_analyze, solver_dlevel, solver_lit_removable,
   solver_propagate, solver_read_wlist, solver_search, solver_solve,
   vecp_remove.  Each family is marked below by a banner comment naming the
   function and its proof count.  The part-local helper lemmas and Ltacs used
   across those families sit ahead of the first VC proof; see the comment
   above each one for what it captures.  Every `Lemma proof_of_*` below
   proves exactly one VC from solver_qcp_goal.v -- do not add new lemmas here
   without a matching goal.v entry; see solver_qcp_proof_manual.v for the
   part index and the auto/manual split rationale. *)

(* ---------------------------------------------------------------------------
   Part-local proof tactics.
   Each one is the shared script of a group of proofs in THIS file; the
   varying identifiers are the caller's
   own binders, passed as `ident` arguments because `aggressive_pre_process` /
   `Unfold` introduce them inside the tactic, where the Ltac interner cannot
   see them.  Parts are mutually independent, so these live here and not in
   solver_qcp_proof_common.v; the `_p2` suffix keeps them from colliding when
   solver_qcp_proof_manual.v `Include`s all nine parts into one module.
   --------------------------------------------------------------------------- *)

(* The heap conjunct of the analyze cancellation obligation: everything the
   entailer leaves is either arithmetic, the [solver_shape] record, or the
   heap well-formedness carried by [analysis_cancel_ready].  The caller keeps
   `LLM_pre_process` and `split_pures` as its own sentences: rewriting the
   whole opener as one `;` chain leaves goals open. *)
Ltac msat_analyze_cancel_heap_tail_p2 :=
  dump_pre_spatial;
  try lia;
  try match goal with
        Hshape : solver_shape ?M |- _ =>
          unfold solver_shape in Hshape; intuition congruence
      end;
  match goal with
  | Hready : analysis_cancel_ready ?anz_n _ _ _ ?M _ |- _ =>
      destruct Hready as [? [? [? [Hheap _]]]];
      unfold order_heap_wf, msolver_heap; cbn;
      try match goal with
            Hsize : ms_size M = anz_n |- _ => rewrite Hsize
          end;
      exact Hheap
  end.

(* The literal-range obligations of the learnt-clause copy loop: read the
   bound off the clause's [Forall (lit_wf_c n)] fact at the loop index.
   [hf] is that fact, [nn] the variable count, [cw] the clause words, [jj] the
   index.  The caller keeps its opener as sentences for the same reason. *)
Ltac msat_analyze_learnt_lit_range_tail_p2 hf nn cw jj :=
  dump_pre_spatial;
  pose proof
    (Forall_Znth_elim Z (lit_wf_c nn) cw 0 (jj - 0) hf ltac:(lia)) as Hwf;
  unfold lit_wf_c in Hwf;
  lia.

(* The pure conjuncts of `solver_search`'s model-ready precondition: bind the
   invariant under [hr] and let the shared dispatcher split it. *)
Tactic Notation "msat_search_model_ready_conjuncts_p2" ident(hr) ident(nn)
  ident(ff) ident(aa) ident(ai) ident(ms) :=
  Unfold; right; intros;
  bind_fact ( solver_search_model_ready nn ff aa ai ms ) as hr;
  msat_search_close_model_ready_conjuncts hr.

(* The model-copy loop entailment: same invariant, but the goals come from
   `aggressive_pre_process` and are closed by the entry-fact dispatcher. *)
Tactic Notation "msat_search_model_copy_entry_p2" ident(hr) ident(nn)
  ident(ff) ident(aa) ident(ai) ident(ms) :=
  aggressive_pre_process;
  bind_fact ( solver_search_model_ready nn ff aa ai ms ) as hr;
  msat_search_close_model_copy_entry_facts hr nn ff aa ai ms.

(* The learnt-clause vector bounds: unfold the leading [veci_rep] to expose its
   data pointer, then hand the capacity fact [hcap] to the shared closer. *)
Tactic Notation "msat_search_learnt_vec_bounds_p2" ident(hcap) :=
  Unfold; left; intros; unfold veci_rep at 1; Intros p;
  msat_search_close_learnt_clause_vec_bounds hcap.

(* The propagation safety obligation on a sign-extended assignment cell: the
   whole goal is the range of [signed_last_nbits] at [rv]. *)
Tactic Notation "msat_propagate_safety_signed_range_p2" ident(rv) :=
  aggressive_pre_process;
  dump_pre_spatial;
  pose proof (signed_Lastnbits_range rv 8 ltac:(lia));
  lia.

(* Non-negativity of the clause-activity increment, read off the solver
   invariant [hinv] bound at the record [mr]. *)
Tactic Notation "msat_search_cla_inc_nonneg_p2" ident(hinv) ident(nn)
  ident(ff) ident(aa) ident(ai) ident(mr) :=
  Unfold; left; intros;
  bind_fact ( msolver_inv nn ff aa ai mr ) as hinv;
  entailer_with ltac:(lia);
  exact (@msi_cla_inc_nonnegative nn ff aa ai mr hinv).

(* The assumption-loop side conditions.  Some are stated through the call's
   return value and some through `ms_size`, where the loop invariant spells
   the variable index [kk] and `n`; both are re-spelled by shape, with pattern
   variables only -- an Ltac pattern cannot name a goal-local hypothesis. *)
Tactic Notation "msat_solve_assume_fresh_pure_p2" ident(kk) :=
  Unfold; left; intros;
  unfold assumption_fresh_ready in *;
  entailer_with ltac:(lia);
  try match goal with
      | H : _ = lit_var_c (Znth (_ - 0) _ 0) |- _ => rewrite H
      end;
  try match goal with
      | H : ms_size _ = _ |- _ => rewrite H
      end;
  replace (kk - 0) with kk by lia; tauto.

(* The three pure conjuncts guarding a backjump: the retval is not the
   `unknown` code, the clause-decay is a positive finite fp32, and the model
   is still empty.  The last one is rebased through the backjump invariant. *)
Tactic Notation "msat_search_backjump_ready_pure_p2" ident(hrv) ident(hbj)
  ident(hfp) ident(hmdl) ident(rv) ident(nn) ident(ff) ident(aa) ident(ai)
  ident(mc) ident(mb) ident(wds) :=
  Unfold; left; intros;
  bind_fact ( rv <> -2 ) as hrv;
  bind_fact ( solver_search_backjump_ready nn ff aa ai mc mb wds ) as hbj;
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay mb) ) as hfp;
  bind_fact ( ms_model mc = nil ) as hmdl;
  unfold solver_search_backjump_ready in hbj;
  destruct hbj as [_ [_ [_ [_ [_ [_ [Hmodel [_ _]]]]]]]];
  split_pures; dump_pre_spatial;
  first [assumption | rewrite Hmodel; exact hmdl].

(* Shared core of the four assumption-assignment side conditions: the trail
   cell at the assumption's variable is an [lbool_cell], so it survives an
   8-bit sign extension.  Both the plain and the negated representability
   facts are derived and whichever matches [hsl] is rewritten. *)
Ltac msat_solve_assign_repr_core_p2 hsl rv2 rv mc kk rw nn :=
  repeat rewrite Z.sub_0_r in *;
  subst rv2;
  assert (Hcell : lbool_cell
    (Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0))
    by (eapply Forall_Znth_elim;
        [ match goal with
          | H : msolver_inv_assuming_strong _ _ _ _ mc |- _ =>
              exact (mtw_cells (msa_trail_wf (msas_weak H)))
          end
        | match goal with
          | H : Zlength (mt_assigns (ms_core mc)) = nn |- _ => rewrite H
          end; lia ]);
  assert (Hrepr : signed_last_nbits
    (Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0) 8 =
    Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0)
    by (apply signed_last_nbits_eq; [lia|];
        unfold lbool_cell in Hcell;
        destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia);
  assert (Hreprn : signed_last_nbits
    (- Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0) 8 =
    - Znth (lit_var_c (Znth kk rw 0)) (mt_assigns (ms_core mc)) 0)
    by (apply signed_last_nbits_eq; [lia|];
        unfold lbool_cell in Hcell;
        destruct Hcell as [Hc | [Hc | Hc]]; rewrite Hc; lia);
  rewrite ?Hrepr, ?Hreprn in hsl;
  subst rv;
  entailer_with ltac:(lia).

(* The positive-polarity form: the call returns the cell itself. *)
Tactic Notation "msat_solve_assign_pos_pure_p2" ident(hsl) ident(rv2) ident(rv)
  ident(mc) ident(kk) ident(rw) ident(nn) :=
  bind_fact ( signed_last_nbits
    (Znth (rv2 - 0) (mt_assigns (ms_core mc)) 0) 8 = -1 ) as hsl;
  msat_solve_assign_repr_core_p2 hsl rv2 rv mc kk rw nn.

(* The negated form: the call returns the negated cell, so the goal also has
   to discharge the literal's sign bit. *)
Tactic Notation "msat_solve_assign_neg_pure_p2" ident(hsl) ident(rv2) ident(rv)
  ident(mc) ident(kk) ident(rw) ident(nn) :=
  bind_fact ( signed_last_nbits
    (- Znth (rv2 - 0) (mt_assigns (ms_core mc)) 0) 8 = -1 ) as hsl;
  msat_solve_assign_repr_core_p2 hsl rv2 rv mc kk rw nn;
  unfold lit_sign_c in *;
  destruct (Z.odd (Znth kk rw 0)); simpl in *; lia.

(* `solver_solve` states the assumption array as a prefix of the raw literal
   vector; at the return points the prefix is the whole vector.  The equation
   is selected by shape, not by PreH index: the numbering shifts whenever the
   obligation gains a binder.  The clause uses pattern variables only: an
   `ident` argument substituted into a match PATTERN selected the wrong
   hypothesis. *)
Tactic Notation "msat_solve_assumption_denote_p2" ident(aarr) ident(rw) :=
  assert (HA : aarr = lits_denote rw)
    by (match goal with
        | H : _ = assumption_prefix ?y (Zlength ?y) |- _ => rewrite H
        end;
        unfold assumption_prefix;
        rewrite sublist_self by reflexivity;
        reflexivity).

(* The capacity arm of `solver_solve`: open the prepare-capacity post, rebase
   its root fact from `ms_size Mcur` to `n` (the loop invariant identifies the
   two), and hand back the model together with the raw assumption vector.
   [mm] and [hh] are the model and the pure fact that `Intros` introduces:
   names a tactic creates itself are invisible to the Ltac1 interner, so the
   caller passes them in. *)
Tactic Notation "msat_solve_capacity_arm_return_p2" ident(aarr) ident(rw)
  ident(mc) ident(nn) ident(ff) ident(mm) ident(hh) :=
  Unfold; right; intros;
  rename A_arr_solver_solve_spec into aarr;
  rename n_solver_solve_spec into nn;
  rename F_solver_solve_spec into ff;
  msat_solve_assumption_denote_p2 aarr rw;
  unfold solver_prepare_capacity_post;
  Intros mm;
  destruct hh as (Hexhausted & Hroot & Hshadow & Hcap & Hreuse);
  match goal with H : ms_size mc = nn |- _ => rewrite H in Hroot end;
  pose proof (solver_operational_root_size nn ff mm Hroot) as Hsize;
  lazymatch goal with
  | Hcontinue : minisat_base_watch_completed ?capacity_entry ->
      solver_query_watch_ready ?published,
    Hentry : solver_query_reuse ?entry ?capacity_entry |- _ =>
      let Hwatch := fresh "Hpublic_watch" in
      let Hready := fresh "Hquery_ready" in
      assert (Hwatch : solver_query_reuse_guard entry -> solver_query_watch_ready published)
        by (intro Hready; exact (Hcontinue (Hentry Hready)))
  end;
  unfold assumptions_array;
  Exists mm rw;
  unfold solver_capacity_arm_at;
  entailer_with int_auto.

(* The unsat arm of `solver_solve`, up to its final entailment: the caller
   keeps that closer because the four return obligations discharge it with
   different arithmetic. *)
Tactic Notation "msat_solve_unsat_arm_return_p2" ident(aarr) ident(rw)
  ident(mu) :=
  Unfold; right; intros;
  rename A_arr_solver_solve_spec into aarr;
  msat_solve_assumption_denote_p2 aarr rw;
  unfold assumptions_array, solver_unsat_arm_at;
  Intros;
  Exists mu rw.

(* The rollback step of `solver_lit_removable`: give back the five local C
   variables as undefined stores, then split on whether the tag stack still
   has room.  [htop] [hlits] [htags] [hscan] name the four facts bound out of
   the precondition; the rest are the caller's binders. *)
Tactic Notation "msat_lit_removable_rollback_p2" ident(htop) ident(hlits)
  ident(htags) ident(hscan) ident(nn) ident(m0) ident(lp)
  ident(mnl) ident(tp) ident(lts) ident(tgs) ident(tgd) ident(dn) ident(stk)
  ident(cn) ident(vv) ident(cc) ident(ii) ident(rv3) ident(rsp) ident(lvp)
  ident(tagret) :=
  Unfold;
  pre_process_default;
  subst tagret;
  bind_fact ( tp = Zlength (ms_tagged m0) ) as htop;
  bind_fact ( lts = clause_lits_addr cc ) as hlits;
  bind_fact ( analysis_tags_exact nn tgs tgd ) as htags;
  bind_fact ( removable_reason_scan_inv nn m0 lp mnl (ms_tagged m0) dn stk
    tgs tgd cn vv cc ii ) as hscan;
  replace (ii - 0) with ii in * by lia;
  replace (rv3 - 0) with rv3 in * by lia;
  assert (Hdfs : removable_dfs_loop_inv nn m0 lp mnl
    (ms_tagged m0) tgs tgd (vv :: stk) dn)
    by (unfold removable_reason_scan_inv in hscan; tauto);
  assert (Hrollback : removable_rollback_inv nn tp tp (ms_tagged m0)
    (ms_tags m0) tgs tgd tgs)
    by (eapply removable_rollback_start__lit_removable; eauto);
  assert (Htop0 : 0 <= tp) by (rewrite htop; apply Zlength_nonneg);
  sep_apply_l_atomic (store_int_undef_store_int (&( "v")) rv3);
  sep_apply_l_atomic (store_int_undef_store_int (&( "i")) ii);
  sep_apply_l_atomic (store_int_undef_store_int (&( "v")) vv);
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "reasons")) rsp);
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "levels")) lvp);
  lazymatch goal with
  | |- _ |-- ?rhs =>
      lazymatch rhs with
      | context [veci_rep_at ?addr ?ptr tgd ?cap] =>
          let sp := open_constr:(_ : Z) in
          let tagged_addr := constr:(&( sp # "solver_t" ->ₛ "tagged")) in
          unify addr tagged_addr;
          sep_apply_l_atomic
            (tagged_open_refold__lit_removable
              sp ptr tgd cap ltac:(lia) ltac:(lia))
      end
  end;
  destruct (Z_lt_ge_dec tp (Zlength tgd)) as [Hlt | Hge];
  [ assert (Htagvar : 0 <= Znth tp tgd 0 < nn)
      by (unfold analysis_tags_exact in htags;
          destruct htags as [_ [_ [Hbounds _]]];
          eapply Forall_Znth_elim; [exact Hbounds | lia]);
    Left; Exists tgs;
    entailer_with ltac:(lia);
    rewrite hlits; reflexivity
  | assert (Htople : tp <= Zlength tgd)
      by (unfold removable_rollback_inv in Hrollback; tauto);
    assert (Htopeq : tp = Zlength tgd) by lia;
    Right; Exists tgs;
    entailer_with ltac:(lia);
    rewrite hlits; reflexivity ].

(* The two `binary_keep` arms of the propagation loop join the same next-state
   model: bind the level equation out of the precondition, select the disjunct
   with [br], hand over the nineteen loop binders and the next model [mnext],
   then close with the shared `proof_common` tail.  The arms differ only in
   [br] and in which statistics counter comes first ([c1] before [c2]).  Every
   binder is an argument because it exists only after the caller's own opener
   has run, so the tactic body cannot name it. *)
Tactic Notation "msat_propagate_next_join_p2" ident(hlvl) ident(lvl)
    ident(lvls) ident(trl) ident(rsn) ident(c1) ident(c2)
    ident(cpre) ident(wcap) ident(cpost) ident(wmpre)
    ident(wmpost) ident(lgw) ident(srcw) ident(mvd) ident(gbg) ident(mem)
    ident(ii) ident(jj) ident(ret) ident(rest) ident(ment) ident(mnext) tactic(br) :=
  aggressive_pre_process;
  bind_fact ( lvl = lvls ) as hlvl;
  br;
  Exists trl rsn c1 c2 cpre wcap cpost wmpre wmpost
    lgw srcw mvd gbg mem ii jj ret rest ment;
  Exists mnext;
  msat_propagate_binary_keep_close hlvl.

(* Shared tail of [proof_of_solver_propagate_entail_wit_2_1] and its sibling
   [_2_2]: takes the entry facts by name, re-exports the propagate footprint
   and closes with the binary-keep entailment.  Both call sites differ only in
   the opener that introduces these binders. *)
Tactic Notation "msat_propagate_entail_wit_2_shared_p2"
    ident(Hshape) ident(Hwm) ident(Hwcaps) ident(Hzlen) ident(Hinv)
    ident(Hcallfr) ident(Hqtail) ident(Hcf) ident(Hseed) ident(Hzlen2)
    ident(Hreuse_loop) :=
  unfold stats_propagations, stats_inspects;
  Unfold; left; intros conflict_out_pre s_pre wlists_entry levels_entry assigns_entry M0
    K A_arr F n M1 rsn trl cf retval_2 caps_post wm_pre words wm_post caps_pre wcap p
    retval retval_3 retval_4 source_words_2 Mentry_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 ;
  bind_fact ( solver_shape M1 ) as Hshape;
  bind_fact ( ms_wm M1 = wm_pre ++ words :: wm_post ) as Hwm;
  bind_fact ( ms_wcaps M1 = caps_pre ++ wcap :: caps_post ) as Hwcaps;
  bind_fact ( Zlength wm_pre =
    Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0 ) as Hzlen;
  bind_fact ( solver_propagation_inv n F A_arr K M1 ) as Hinv;
  bind_fact ( propagation_caller_frame M0 M1 ) as Hcallfr;
  bind_fact ( ms_qtail M1 - mt_qhead (ms_core M1) > 0 ) as Hqtail;
  bind_fact ( cf = 0 ) as Hcf;
  bind_fact ( msolver_seed_shadow M1 ) as Hseed;
  bind_fact ( Zlength (mt_trail (ms_core M1)) = ms_qtail M1 ) as Hzlen2;
  Exists trl rsn retval_4
    (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
    caps_pre wcap caps_post wm_pre wm_post
    words words (@nil Z) (@nil Z) words 0 0 (@nil Z) words M1;
  set (Mscan := msolver_propagation_scan_begin M1 retval_4
    (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64));
  Exists Mscan;
  bind_fact (minisat_propagation_reuse_loop n M0 M1 cf) as Hreuse_loop;
  rewrite Hcf in Hreuse_loop;
  assert (Hwatch_map : wmap_exact n (msolver_db M1) (ms_wm M1))
    by (destruct (propagation_inv_context_facts__analyze n F A_arr K M1 Hinv)
      as (_ & _ & _ & _ & _ & _ & Hmap); exact Hmap);
  destruct Hwatch_map as [Hmap_length Hmap];
  assert (Hmap_index : 0 <= Zlength wm_pre < 2 * n)
    by (rewrite Hwm, Zlength_app, Zlength_cons in Hmap_length;
      pose proof (Zlength_nonneg wm_pre); pose proof (Zlength_nonneg wm_post); lia);
  assert (Hpending : incl (expected_watchers (msolver_db M1)
    (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)) words)
    by (specialize (Hmap (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
      ltac:(rewrite <- Hzlen; exact Hmap_index));
      rewrite Hwm, app_Znth2 in Hmap by lia;
      replace (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0
        - Zlength wm_pre) with 0 in Hmap by lia;
      cbn in Hmap; intros word Hin;
      eapply Permutation_in; [apply Permutation_sym; exact Hmap|exact Hin]);
  assert (Hreuse_scan : minisat_propagation_reuse_scan M0 Mscan
    (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0) cf words)
    by (rewrite Hcf; exact (minisat_propagation_reuse_scan_begin__api_reentry
      n M0 M1 (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
      retval_4 (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
      words Hreuse_loop eq_refl Hpending));
  assert (Hstatslen : Zlength (ms_stats M1) = 11)
    by (unfold solver_shape in Hshape; intuition);
  pose proof (propagation_scan_begin_initial__analyze
    n F A_arr K M0 M1
    (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
    retval_4
    (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
    cf words wm_pre wm_post Hshape Hinv Hseed Hcallfr Hqtail
    (eq_sym Hzlen2) eq_refl Hwm Hzlen Hcf) as Hscan;
  change (solver_shape Mscan /\
    msolver_seed_shadow Mscan /\
    propagation_caller_frame M0 Mscan /\
    propagation_scan_frontier M1 Mscan
      (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0) /\
    solver_propagation_scan_semantics n F A_arr K Mscan
      (Znth (mt_qhead (ms_core M1)) (mt_trail (ms_core M1)) 0)
      cf (@nil Z) words) in Hscan;
  destruct Hscan as
    [Hshape_scan [Hseed_scan [Hcaller_scan [Hfrontier_scan Hsem_scan]]]];
  assert (Hcaps : ms_wcaps M1 = caps_pre ++ wcap :: caps_post)
    by exact Hwcaps;
  assert (Hbinary : solver_binary_rep Mscan = solver_binary_rep M1)
    by (unfold solver_binary_rep, Mscan, msolver_propagation_scan_begin,
        msolver_propagation_scan, msolver_propagation_update, stats_set_propagations; reflexivity);
  assert (Hframe : solver_propagate_frame s_pre Mscan =
      solver_propagate_frame s_pre M1)
    by (unfold solver_propagate_frame, solver_fp_rep, stats_propagate_frame,
        stats_starts, stats_decisions, stats_conflicts, stats_clauses,
        stats_clauses_literals, stats_learnts, stats_learnts_literals,
        stats_max_literals, stats_tot_literals,
        Mscan, msolver_propagation_scan_begin, msolver_propagation_scan,
        msolver_propagation_update, stats_set_propagations;
        simpl [mt_set_qhead];
        rewrite !Zlength_replace_Znth;
        rewrite !Znth_replace_Znth_Diff by lia;
        reflexivity);
  sep_apply_l_atomic (PtrArray.seg_to_full retval 0 (Zlength words) words);
  split_pure_spatial;
  [ rewrite Hbinary, Hframe;
    unfold Mscan, msolver_propagation_scan_begin, msolver_propagation_scan,
        msolver_propagation_update, stats_set_propagations;
    simpl [mt_set_qhead];
    rewrite Znth_replace_Znth_Diff by lia;
    rewrite Z.add_0_r;
    replace (retval + 0 * sizeof(PTR)) with retval by lia;
    replace (Zlength words - 0) with (Zlength words) by lia;
    match goal with
    | |- ?P |-- ?Q =>
      assert (Hspatial_identity : P |-- Q) by
        (set_String_name;
         sepcon_assoc_change;
         sepcon_cancel;
         subst_all_strings);
      exact Hspatial_identity
    end
  | split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia;
    try (unfold propagation_watch_scan_physical, wlist_scan_inv;
      simpl; repeat split; try reflexivity; apply Zlength_nonneg);
    unfold Mscan, msolver_propagation_scan_begin,
      msolver_propagation_scan, msolver_propagation_update, stats_set_propagations; cbn [mt_set_qhead];
    try rewrite Znth_replace_Znth_Same by lia;
    try rewrite Znth_replace_Znth_Diff by lia;
    try assumption; try reflexivity; try lia; try apply Zlength_nonneg;
    first
      [ change (ms_wcaps M1 = caps_pre ++ wcap :: caps_post); exact Hcaps
      | change
          (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64 =
           Znth 2
             (replace_Znth 2
               (unsigned_last_nbits (Znth 2 (ms_stats M1) 0 + 1) 64)
               (ms_stats M1)) 0);
        rewrite Znth_replace_Znth_Same by lia; reflexivity ] ].

(* ---------------------------------------------------------------------------
   Part-local helper.
   Bundles the three clause-store positivity facts that
   `proof_of_solver_analyze_partial_solve_wit_35_pure` needs into one
   entailment, so the precondition is normalised and lifted once instead of
   three times.  Not used anywhere else; parts are mutually independent.
   --------------------------------------------------------------------------- *)
Lemma ms_analyze_db_triple_positive_part2 :
  forall prob learnt b lits,
    clause_db_rep prob
    ** clause_db_rep learnt
    ** MiniSatClause.rep b msat_false lits
    |-- “ Forall (fun e => 0 < fst e) prob
          /\ Forall (fun e => 0 < fst e) learnt
          /\ 0 < b ”.
Proof.
  intros prob learnt b lits.
  prop_apply_p (clause_db_rep_positive__analyze prob).
  Intros_p H1.
  prop_apply_p (clause_db_rep_positive__analyze learnt).
  Intros_p H2.
  prop_apply_p (MiniSatClause_rep_positive__analyze b msat_false lits).
  Intros_p H3.
  dump_pre_spatial. tauto.
Qed.

(* ---------------------------------------------------------------------------
   Part-local helper lemmas.
   These carry the reasoning shared by
   `proof_of_solver_propagate_which_implies_wit_33` and
   `proof_of_solver_propagate_entail_wit_24_unit_success`; each one states an
   ordinary fact with explicit hypotheses, so the two branches differ only in
   which database holds the rewritten entry.  The block also holds `msat_solve_lbool_cell_arm_p2`, the shared
   lbool-cell arm of `proof_of_solver_solve_entail_wit_6_1` .. `_6_4`.
   Parts are mutually independent, so they live here and not in
   solver_qcp_proof_common.v; the `_p2` suffix keeps them from colliding when
   solver_qcp_proof_manual.v `Include`s all nine parts into one module.
   --------------------------------------------------------------------------- *)

(* Dropping the first two literals of a clause: the sublist that
   [propagation_normalized_clause] keeps is exactly the clause tail. *)
Lemma msat_sublist_two_tail_p2 : forall (a0 a1 : Z) (tl : list Z),
  sublist 2 (Zlength (a0 :: a1 :: tl)) (a0 :: a1 :: tl) = tl.
Proof.
  intros a0 a1 tl.
  replace (a0 :: a1 :: tl) with ((a0 :: a1 :: nil) ++ tl) by reflexivity.
  assert (Hrange : 2 <= 2 <= Zlength ((a0 :: a1 :: nil) ++ tl)).
  { split; [lia|]. rewrite Zlength_app.
    change (2 <= 2 + Zlength tl). pose proof (Zlength_nonneg tl). lia. }
  rewrite (sublist_split_app_r 2 (Zlength ((a0 :: a1 :: nil) ++ tl)) 2
    (a0 :: a1 :: nil) tl ltac:(reflexivity) Hrange).
  replace (Zlength ((a0 :: a1 :: nil) ++ tl) - 2) with (Zlength tl) by
    (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
  apply sublist_self. reflexivity.
Qed.

(* Both directions of the database-append cancellation in one equivalence, so
   a caller can `rewrite` with it instead of asserting the pair by hand. *)
Lemma msat_clause_db_rep_app_p2 : forall db1 db2,
  clause_db_rep (db1 ++ db2) --||-- clause_db_rep db1 ** clause_db_rep db2.
Proof.
  intros db1 db2.
  split; [apply clause_db_rep_app_elim | apply clause_db_rep_app_intro].
Qed.

(* A literal-order update that does not actually change the literal order
   leaves both databases untouched. *)
Lemma msat_db_pair_update_identity_p2 :
  forall prob learnt q old_lits new_lits prob' learnt',
    db_pair_lits_update prob learnt q old_lits new_lits prob' learnt' ->
    new_lits = old_lits ->
    prob' = prob /\ learnt' = learnt.
Proof.
  intros prob learnt q old_lits new_lits prob' learnt' Hupdate Heq.
  subst new_lits.
  destruct Hupdate as
    [[co [pre [post [Hp [Hold [Hp' Hl']]]]]]
    |[co [pre [post [Hl [Hold [Hp' Hl']]]]]]].
  - assert (Hco : clause_obj_with_lits co old_lits = co).
    { unfold clause_obj_with_lits. rewrite <- Hold. destruct co. reflexivity. }
    rewrite Hco in Hp'. rewrite Hp', Hp. split; [reflexivity|exact Hl'].
  - assert (Hco : clause_obj_with_lits co old_lits = co).
    { unfold clause_obj_with_lits. rewrite <- Hold. destruct co. reflexivity. }
    rewrite Hco in Hl'. rewrite Hl', Hl. split; [exact Hp'|reflexivity].
Qed.

(* The physical side of a watcher-list scan that keeps the current clause:
   the retained prefix grows by one word and the garbage list is whatever the
   incoming one was, shifted by the same word. *)
Lemma msat_propagate_scan_keep_step_p2 :
  forall source_words retained moved rest garbage watch_memory ii jj
         scan_current raw_suffix,
    propagation_watch_scan_physical source_words retained moved rest garbage
      watch_memory ii jj ->
    rest = scan_current :: raw_suffix ->
    exists garbage_route,
      propagation_scan_keep_step source_words retained moved rest
        watch_memory ii jj scan_current (retained ++ scan_current :: nil)
        raw_suffix garbage_route (replace_Znth jj scan_current watch_memory).
Proof.
  intros source_words retained moved rest garbage watch_memory ii jj
    scan_current raw_suffix Hphysical Hrest.
  unfold propagation_watch_scan_physical in Hphysical.
  destruct Hphysical as [Hinv [Hmem [Hjj [Hii Hlenmem]]]].
  rewrite Hrest in Hinv, Hmem.
  destruct garbage as [|g gs].
  - exists nil. unfold propagation_scan_keep_step.
    split; [exact Hrest|]. split; [reflexivity|]. split; [reflexivity|].
    unfold propagation_watch_scan_physical. repeat split.
    + apply wlist_scan_keep. exact Hinv.
    + rewrite Hmem, <- Hjj. rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (Zlength retained - Zlength retained) with 0 by lia.
      cbn. rewrite <- app_assoc. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hjj. lia.
    + cbn in Hii. rewrite app_nil_r in Hii.
      rewrite app_nil_r, Zlength_app. cbn. lia.
    + rewrite Zlength_replace_Znth. exact Hlenmem.
  - exists (gs ++ scan_current :: nil). unfold propagation_scan_keep_step.
    split; [exact Hrest|]. split; [reflexivity|]. split; [reflexivity|].
    unfold propagation_watch_scan_physical. repeat split.
    + apply wlist_scan_keep. exact Hinv.
    + rewrite Hmem, <- Hjj. rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (Zlength retained - Zlength retained) with 0 by lia.
      cbn. rewrite <- !app_assoc. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hjj. lia.
    + rewrite !Zlength_app in Hii |- *.
      assert (Hrl : Zlength (retained ++ scan_current :: nil) =
          Zlength retained + 1).
      { rewrite Zlength_app. cbn. lia. }
      assert (Hgsl : Zlength (gs ++ scan_current :: nil) = Zlength gs + 1).
      { rewrite Zlength_app. cbn. lia. }
      rewrite Hrl, Hgsl. rewrite Zlength_cons in Hii. lia.
    + rewrite Zlength_replace_Znth. exact Hlenmem.
Qed.

(* The two solver facts every live propagation scan carries, projected once
   for both propagation contexts instead of per use site. *)
Lemma msat_propagate_scan_live_core_p2 :
  forall n F A_arr K M p kept rest,
    solver_propagation_scan_semantics n F A_arr K M p 0 kept rest ->
    solver_shape M /\ mtrail_wf n (ms_core M).
Proof.
  intros n F A_arr K M p kept rest Hsem.
  destruct Hsem as [Hlive | Hbad].
  - destruct Hlive as [_ [Hweak _]]. destruct Hweak as [_ Hinv].
    destruct K as [A_inst | A_proc]; split.
    + exact (msw_shape Hinv).
    + exact (msw_trail_wf Hinv).
    + exact (msa_shape Hinv).
    + exact (msa_trail_wf Hinv).
  - exfalso. destruct Hbad as [Hnz _]. lia.
Qed.

(* Enqueueing a fresh literal keeps the scan frontier: the queue head is
   untouched, the entry trail is still a prefix of the pushed trail, and the
   focused literal still sits one slot below the head. *)
Lemma msat_propagate_scan_frontier_push_p2 :
  forall n Mentry Mscan Mroute p watch0 rw rc prob learnt,
    mtrail_wf n (ms_core Mscan) ->
    Zlength (mt_trail (ms_core Mscan)) = ms_qtail Mscan ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 = 0 ->
    Mroute = msolver_propagation_enqueue_success
      (msolver_propagation_db_wmap_update Mscan prob learnt
        (ms_wm Mscan) (ms_wcaps Mscan)) watch0 rw rc ->
    propagation_scan_frontier Mentry Mscan p ->
    propagation_scan_frontier Mentry Mroute p.
Proof.
  intros n Mentry Mscan Mroute p watch0 rw rc prob learnt
    Hwf_scan Htrail_len Hzero HMroute Hfrontier.
  assert (Htest :
    (Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 =? 0)%Z = true)
    by (apply Z.eqb_eq; exact Hzero).
  unfold msolver_propagation_enqueue_success,
    msolver_propagation_db_wmap_update,
    msolver_propagation_overlay, msolver_propagation_update in HMroute.
  cbn in HMroute.
  rewrite Htest in HMroute.
  cbn [msolver_propagation_overlay msolver_propagation_update ] in HMroute.
  unfold propagation_scan_frontier in Hfrontier |- *.
  destruct Hfrontier as [Hqh [Hp [Htail [Hprefix Hrollback]]]].
  rewrite HMroute.
  cbn [mt_enqueue mt_push] in *.
  unfold propagation_heap_rollback_ready in Hrollback.
  destruct Hrollback as [Hqpos [Hfocus Hgate]].
  repeat split.
  - exact Hqh.
  - exact Hp.
  - change (ms_qtail Mentry <= ms_qtail Mscan + 1).
    apply Z.le_trans with (m := ms_qtail Mscan).
    + exact Htail.
    + exact (z_le_add_one__propagate (ms_qtail Mscan)).
  - unfold sublist in Hprefix |- *.
    cbn in Hprefix |- *.
    rewrite firstn_app.
    assert (Hnat :
      (Z.to_nat (ms_qtail Mentry) <= length (mt_trail (ms_core Mscan)))%nat).
    { destruct (Z_lt_ge_dec (ms_qtail Mentry) 0) as [Hneg | Hnonneg].
      - destruct (ms_qtail Mentry); cbn in *; lia.
      - assert (Hnonneg' : 0 <= ms_qtail Mentry) by lia.
        rewrite <- (Nat2Z.id (length (mt_trail (ms_core Mscan)))).
        rewrite <- Zlength_correct.
        apply (proj1 (Z2Nat.inj_le (ms_qtail Mentry)
          (Zlength (mt_trail (ms_core Mscan))) Hnonneg'
          (Zlength_nonneg (mt_trail (ms_core Mscan))))).
        rewrite Htrail_len. exact Htail. }
    replace (Z.to_nat (ms_qtail Mentry) -
      length (mt_trail (ms_core Mscan)))%nat with 0%nat by lia.
    cbn. rewrite app_nil_r. exact Hprefix.
  - exact Hqpos.
  - change (p = Znth (mt_qhead (ms_core Mscan) - 1)
      (mt_trail (ms_core Mscan) ++ (watch0 :: nil)) 0).
    rewrite app_Znth1.
    + exact Hfocus.
    + pose proof (mtw_qhead_range Hwf_scan); lia.
  - exact Hgate.
Qed.

(* Everything the clause-normalisation obligation needs about the rewritten
   clause object itself: which of the two watched literals is the false one,
   the focus contributions before and after the rewrite, the safety of the new
   occurrence, and whether the rewrite swaps the watch pair or is the
   identity.  [sig] is the sign the scan read back for [watch0_2]. *)
Lemma msat_propagate_clause_watch_facts_p2 :
  forall n Mscan p scan_current co a0 a1 tl new_lits co_new
         false_lit watch0_2 sig,
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tl ->
    3 <= Zlength (a0 :: a1 :: tl) ->
    real_watch_pair p (a0 :: a1 :: tl) ->
    watch0_2 + false_lit =
      Znth 0 (a0 :: a1 :: tl) 0 + Znth 1 (a0 :: a1 :: tl) 0 ->
    false_lit = lit_neg_c p ->
    sig = 1 - 2 * lit_sign_c watch0_2 ->
    Znth (lit_var_c watch0_2) (mt_assigns (ms_core Mscan)) 0 = sig ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    new_lits = propagation_normalized_clause watch0_2 false_lit
      (a0 :: a1 :: tl) ->
    co_new = clause_obj_with_lits co new_lits ->
    Permutation new_lits (a0 :: a1 :: tl) /\
    minisat_entry_focus_contributions p (scan_current, co) =
      (minisat_occurrence_of_entry (scan_current, co), scan_current) :: nil /\
    minisat_entry_focus_contributions p (scan_current, co_new) =
      (minisat_occurrence_of_entry (scan_current, co_new), scan_current) :: nil /\
    minisat_occurrence_safe
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (minisat_occurrence_of_entry (scan_current, co_new)) /\
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current, co_new) l)) /\
    ((co_watch0 co_new = co_watch1 co /\ co_watch1 co_new = co_watch0 co) \/
     (co_watch0 co_new = co_watch0 co /\ co_watch1 co_new = co_watch1 co)) /\
    (lit_false (mt_assigns (ms_core Mscan)) (co_watch0 co) \/
     new_lits = a0 :: a1 :: tl).
Proof.
  intros n Mscan p scan_current co a0 a1 tl new_lits co_new
    false_lit watch0_2 sig Hdbwf Hin Hlits Hbig Hrwp Hw02 Hfl Hsig Hznth
    Hp Hprocessed Hnewlits Hconew.
  pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin) as Hobj.
  unfold obj_wf in Hobj. rewrite Hlits in Hobj.
  destruct Hobj as [Hlen [Hall Hnodup]].
  assert (Htl : sublist 2 (Zlength (a0 :: a1 :: tl)) (a0 :: a1 :: tl) = tl)
    by (apply msat_sublist_two_tail_p2).
  unfold propagation_normalized_clause in Hnewlits.
  rewrite Htl in Hnewlits.
  assert (Hnewco : co_lits co_new = watch0_2 :: false_lit :: tl)
    by (rewrite Hconew; unfold clause_obj_with_lits; cbn [co_lits];
        exact Hnewlits).
  assert (Hwatchcases :
      (a0 = false_lit /\ watch0_2 = a1) \/ (a1 = false_lit /\ watch0_2 = a0)).
  { unfold real_watch_pair in Hrwp.
    rewrite !Znth0_cons in Hrwp, Hw02.
    rewrite !Znth_cons in Hrwp, Hw02 by lia.
    replace (1 - 1) with 0 in Hrwp, Hw02 by lia.
    rewrite !Znth0_cons in Hrwp, Hw02.
    destruct Hrwp as [Hw | Hw].
    - left. rewrite <- Hfl in Hw. split; [exact Hw|lia].
    - right. rewrite <- Hfl in Hw. split; [exact Hw|lia]. }
  inversion Hall as [|x xs Hwf0 Hall1]; subst x xs.
  inversion Hall1 as [|x xs Hwf1 Halltl]; subst x xs.
  inversion Hnodup as [|x xs Hnot0 Hnd1]; subst x xs.
  inversion Hnd1 as [|x xs Hnot1 Hndtl]; subst x xs.
  assert (Hvardiff : lit_var_c a0 <> lit_var_c a1).
  { intro Heq. apply Hnot0. simpl. left. symmetry. exact Heq. }
  assert (Hnegfalse : lit_neg_c false_lit = p).
  { rewrite Hfl. apply lit_neg_c_involutive. }
  assert (Hotherneg : lit_neg_c watch0_2 <> p).
  { intro Heq.
    assert (Hv := f_equal lit_var_c Heq).
    rewrite lit_var_c_neg in Hv.
    assert (Hvfalse : lit_var_c false_lit = lit_var_c p).
    { rewrite Hfl, lit_var_c_neg. reflexivity. }
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]]; subst; apply Hvardiff; lia. }
  assert (Hotherb : (lit_neg_c watch0_2 =? p)%Z = false)
    by (apply Z.eqb_neq; exact Hotherneg).
  assert (Hfalseb : (lit_neg_c false_lit =? p)%Z = true)
    by (apply Z.eqb_eq; exact Hnegfalse).
  assert (Hwatchtrue : lit_true (mt_assigns (ms_core Mscan)) watch0_2).
  { unfold lit_true. rewrite Hznth, Hsig.
    unfold lit_sig, lit_sign_c. destruct (Z.odd watch0_2); reflexivity. }
  assert (Hfalsefalse : lit_false (mt_assigns (ms_core Mscan)) false_lit).
  { destruct Hprocessed as [Hptrue _].
    unfold lit_true in Hptrue. unfold lit_false.
    rewrite Hfl, lit_var_c_neg, lit_sig_neg. lia. }
  assert (Hentryold : minisat_entry_focus_contributions p (scan_current, co) =
      (minisat_occurrence_of_entry (scan_current, co), scan_current) :: nil).
  { unfold minisat_entry_focus_contributions, entry_watchers.
    cbn [fst snd]. unfold co_watch0, co_watch1. rewrite Hlits.
    assert (Hb : (3 <=? Zlength (a0 :: a1 :: tl))%Z = true)
      by (apply Z.leb_le; exact Hbig).
    rewrite Hb.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - rewrite Ha0, Hfalseb. rewrite <- Hw, Hotherb. reflexivity.
    - rewrite <- Hw, Hotherb. rewrite Ha1, Hfalseb. reflexivity. }
  assert (Hentrynew :
      minisat_entry_focus_contributions p (scan_current, co_new) =
      (minisat_occurrence_of_entry (scan_current, co_new), scan_current) :: nil).
  { unfold minisat_entry_focus_contributions, entry_watchers.
    cbn [fst snd]. unfold co_watch0, co_watch1. rewrite Hnewco.
    assert (Hb : (3 <=? Zlength (watch0_2 :: false_lit :: tl))%Z = true).
    { apply Z.leb_le. rewrite !Zlength_cons in Hbig |- *. exact Hbig. }
    rewrite Hb.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    rewrite Hotherb, Hfalseb. reflexivity. }
  assert (Honewsafe : minisat_occurrence_safe
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (minisat_occurrence_of_entry (scan_current, co_new))).
  { assert (Hleft : watch_left (minisat_occurrence_of_entry (scan_current, co_new))
        = lit_denote watch0_2).
    { unfold minisat_occurrence_of_entry, watch_left, co_watch0.
      cbn. rewrite Hnewco. reflexivity. }
    unfold minisat_occurrence_safe. intro Hboth. destruct Hboth as [Hbad _].
    rewrite Hleft in Hbad.
    assert (Hwfwatch : lit_wf_c n watch0_2).
    { destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]]; subst; assumption. }
    assert (Hwfneg : lit_wf_c n (lit_neg_c watch0_2))
      by (apply lit_neg_c_wf; exact Hwfwatch).
    rewrite <- (lit_denote_neg watch0_2) in Hbad by (destruct Hwfwatch; lia).
    apply (proj1 (minisat_processed_denote n
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) (lit_neg_c watch0_2) Hwfneg)) in Hbad.
    destruct Hbad as [Hnegtrue _].
    unfold lit_true in Hwatchtrue, Hnegtrue.
    rewrite lit_var_c_neg, lit_sig_neg in Hnegtrue.
    destruct (lit_sig_values watch0_2); lia. }
  assert (Hentryperm : forall l,
      Permutation (entry_watchers (scan_current, co) l)
        (entry_watchers (scan_current, co_new) l)).
  { intros l. unfold entry_watchers, co_watch0, co_watch1.
    cbn [fst snd]. rewrite Hlits, Hnewco.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    rewrite !Zlength_cons.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - subst a0 watch0_2. apply Permutation_app_comm.
    - subst a1 watch0_2. reflexivity. }
  repeat split.
  - rewrite Hnewlits.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    + subst a0 watch0_2. apply perm_swap.
    + subst a1 watch0_2. reflexivity.
  - exact Hentryold.
  - exact Hentrynew.
  - exact Honewsafe.
  - exact Hentryperm.
  - unfold co_watch0, co_watch1. rewrite Hlits, Hnewco.
    rewrite !Znth0_cons.
    rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
    rewrite Znth0_cons.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    + left. subst a0 watch0_2. split; reflexivity.
    + right. subst a1 watch0_2. split; reflexivity.
  - destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    + left. unfold co_watch0. rewrite Hlits. rewrite Znth0_cons.
      subst a0. exact Hfalsefalse.
    + right. rewrite Hnewlits. subst a1 watch0_2. reflexivity.
Qed.

(* The database-level half of the clause-normalisation obligation, shared by
   the problem-database and the learnt-database branch: the two branches
   differ only in the segment [dpre]/[dpost] that surrounds the rewritten
   entry, so stating the split as an equation on the concatenated database
   makes the whole argument branch-independent.  The clause-level facts come
   from msat_propagate_clause_watch_facts_p2. *)
Lemma msat_propagate_route_facts_p2 :
  forall n F A_arr K Mscan Mroute p scan_current co co_new
         a0 a1 tl new_lits prob_route learnt_route dpre dpost
         retained raw_suffix,
    msolver_db Mscan = dpre ++ (scan_current, co) :: dpost ->
    prob_route ++ learnt_route = dpre ++ (scan_current, co_new) :: dpost ->
    db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current
      (a0 :: a1 :: tl) new_lits prob_route learnt_route ->
    Mroute = msolver_propagation_db_wmap_update Mscan prob_route learnt_route
      (ms_wm Mscan) (ms_wcaps Mscan) ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    Permutation new_lits (a0 :: a1 :: tl) ->
    minisat_entry_focus_contributions p (scan_current, co) =
      (minisat_occurrence_of_entry (scan_current, co), scan_current) :: nil ->
    minisat_entry_focus_contributions p (scan_current, co_new) =
      (minisat_occurrence_of_entry (scan_current, co_new), scan_current) :: nil ->
    minisat_occurrence_safe
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (minisat_occurrence_of_entry (scan_current, co_new)) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current, co_new) l)) ->
    ((co_watch0 co_new = co_watch1 co /\ co_watch1 co_new = co_watch0 co) \/
     (co_watch0 co_new = co_watch0 co /\ co_watch1 co_new = co_watch1 co)) ->
    (lit_false (mt_assigns (ms_core Mscan)) (co_watch0 co) \/
     new_lits = a0 :: a1 :: tl) ->
    solver_propagation_weak n F A_arr K Mscan ->
    prop_level (ms_core Mscan) ->
    propagation_heap_ready n Mscan ->
    heap_covers n (msolver_heap Mscan) (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) ->
    current_reasonless_earliest n Mscan ->
    level_of (msolver_view n Mscan) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core Mscan))) ->
    lit_wf_c n p ->
    processed (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) p ->
    minisat_watch_frontier_except n (msolver_db Mscan)
      (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
      (mt_qhead (ms_core Mscan)) (lit_denote p) ->
    minisat_focus_scan_carrier (msolver_db Mscan) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      retained (scan_current :: raw_suffix) ->
    propagation_real_satisfied_transition n F A_arr K Mscan p
      prob_route learnt_route (retained ++ scan_current :: nil)
      raw_suffix Mroute.
Proof.
  intros n F A_arr K Mscan Mroute p scan_current co co_new
    a0 a1 tl new_lits prob_route learnt_route dpre dpost retained raw_suffix
    Hdb Hdb2 Hupdate HM Hdbwf Hin Hperm Hentryold Hentrynew Honewsafe
    Hentryperm Hswap Hhead Hweak Hprop Hheapready Hheapcovers Hreasonless
    Hlevel Hp Hprocessed Hfrontier Hscan.
  set (fpre := minisat_focus_contributions dpre p).
  set (fpost := minisat_focus_contributions dpost p).
  assert (Hcurrentreal : is_tag scan_current = false)
    by (apply even_not_tag; eapply db_wf_even; eassumption).
  assert (Hfocusold : minisat_focus_contributions (msolver_db Mscan) p =
      fpre ++ (minisat_occurrence_of_entry (scan_current, co), scan_current)
        :: fpost).
  { rewrite Hdb.
    rewrite minisat_focus_contributions_app__propagate_dbu.
    rewrite minisat_focus_contributions_cons__propagate_dbu.
    rewrite Hentryold. unfold fpre, fpost. cbn. reflexivity. }
  assert (Hfocusnew : minisat_focus_contributions
      (prob_route ++ learnt_route) p =
      fpre ++ (minisat_occurrence_of_entry (scan_current, co_new), scan_current)
        :: fpost).
  { rewrite Hdb2.
    rewrite minisat_focus_contributions_app__propagate_dbu.
    rewrite minisat_focus_contributions_cons__propagate_dbu.
    rewrite Hentrynew. unfold fpre, fpost. cbn. reflexivity. }
  assert (Hfocusroute : minisat_focus_scan_carrier
      (prob_route ++ learnt_route) p
      (minisat_processed n (mt_assigns (ms_core Mscan))
        (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      (retained ++ scan_current :: nil) raw_suffix).
  { eapply focus_scan_carrier_db_pair_token_replace__propagate_dbu
      with (olddb := msolver_db Mscan) (co := co) (pre := fpre) (post := fpost)
        (onew := minisat_occurrence_of_entry (scan_current, co_new)).
    - exact Hdbwf.
    - exact Hin.
    - exact Hcurrentreal.
    - exact Hfocusold.
    - exact Hfocusnew.
    - exact Honewsafe.
    - exact Hscan. }
  pose proof (msat_db_entry_swap_expected_watchers (msolver_db Mscan)
    (prob_route ++ learnt_route) dpre dpost scan_current co co_new
    Hdb Hdb2 Hentryperm) as Hexpected.
  assert (Hfrontierroute : minisat_watch_frontier_except n
      (prob_route ++ learnt_route) (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)) (lit_denote p)).
  { unfold minisat_watch_frontier_except,
      minisat_watch_occurrences in Hfrontier |- *.
    unfold watch_frontier_except in Hfrontier |- *.
    rewrite Forall_forall in Hfrontier |- *.
    intros o Ho. apply in_map_iff in Ho as [[q obj] [<- Hentry]].
    rewrite Hdb2 in Hentry.
    destruct (in_app_or _ _ _ Hentry) as [Hepre | Hecons].
    - apply Hfrontier. apply in_map. rewrite Hdb.
      apply in_or_app. left. exact Hepre.
    - destruct Hecons as [Heq | Hepost].
      + inversion Heq; subst q obj.
        specialize (Hfrontier (minisat_occurrence_of_entry (scan_current, co))).
        assert (Holdin : In (minisat_occurrence_of_entry (scan_current, co))
            (map minisat_occurrence_of_entry (msolver_db Mscan)))
          by (apply in_map; exact Hin).
        specialize (Hfrontier Holdin).
        unfold minisat_occurrence_of_entry in Hfrontier |- *.
        cbn [watch_left watch_right] in Hfrontier |- *.
        destruct Hswap as [[Hl Hr] | [Hl Hr]]; rewrite Hl, Hr; tauto.
      + apply Hfrontier. apply in_map. rewrite Hdb.
        apply in_or_app. right. simpl. right. exact Hepost. }
  assert (Hweakroute : solver_propagation_weak n F A_arr K
      (msolver_propagation_db_wmap_update Mscan prob_route learnt_route
        (ms_wm Mscan) (ms_wcaps Mscan))).
  { destruct Hhead as [Hheadfalse | Hsame].
    - unfold solver_propagation_weak in Hweak |- *.
      destruct Hweak as [Hroot Hctx]. split.
      + unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hroot.
      + eapply (ctx_db_pair_lits_no_owner__propagate_dbu n F A_arr K Mscan).
        * exact Hctx.
        * exact Hupdate.
        * exact Hperm.
        * exact Hexpected.
        * eapply (ctx_no_live_reason_owner_head_false__propagate_dbu
            n F A_arr K Mscan); eassumption.
    - destruct (msat_db_pair_update_identity_p2 (ms_prob Mscan) (ms_learnt Mscan)
        scan_current (a0 :: a1 :: tl) new_lits prob_route learnt_route
        Hupdate Hsame) as [Hprobid Hlearntid].
      assert (HMid : msolver_propagation_db_wmap_update Mscan prob_route
          learnt_route (ms_wm Mscan) (ms_wcaps Mscan) = Mscan).
      { rewrite Hprobid, Hlearntid.
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update. destruct Mscan. reflexivity. }
      rewrite HMid. exact Hweak. }
  unfold propagation_real_satisfied_transition. split; [exact HM|].
  rewrite HM. left. split; [reflexivity|]. split; [exact Hweakroute|].
  split; [exact Hprop|]. split; [exact Hheapready|].
  split; [exact Hheapcovers|]. split; [exact Hreasonless|].
  split; [exact Hlevel|]. split; [exact Hp|]. split; [exact Hprocessed|].
  split; [exact Hfrontierroute | exact Hfocusroute].
Qed.

(* The spatial half of the clause-normalisation obligation, identical for the
   problem and the learnt database: split the rewritten entry [cn] out of the
   segment [pr] .. [po] around it, expand its literal list [nl] through
   [htail]/[hlearnt], unfold the literal array named by [hptr] and [lts], and
   close the residual pointer side conditions off the database's own
   well-formedness.  [sc] is the clause pointer, [tl] its literal tail. *)
Tactic Notation "msat_propagate_db_entry_spatial_p2" ident(pr) ident(po)
    ident(sc) ident(cn) ident(nl) ident(htail) ident(hlearnt)
    ident(hptr) ident(lts) ident(tl) :=
  rewrite (msat_clause_db_rep_app_p2 pr ((sc, cn) :: po));
  rewrite clause_db_rep_cons;
  unfold MiniSatClause.rep, cn, clause_obj_with_lits, nl,
    propagation_normalized_clause; cbn [fst snd co_lits co_learnt];
  rewrite htail, hlearnt;
  unfold clause_lits_pointer in hptr; subst lts;
  rewrite !IntArray.seg_unfold;
  sep_apply store_ptr_undef_store_ptr;
  sep_apply store_char_undef_store_char;
  entailer_with ltac:(lia);
  try (match goal with
       | Hw : db_wf ?nn ?dbb, Hi : In (?q, ?cobj) ?dbb |- _ =>
           pose proof (db_wf_ptr_pos nn dbb q cobj Hw Hi)
       end; lia);
  try (apply clause_ptr_mod2;
       match goal with
       | Hw : db_wf ?nn ?dbb, Hi : In (?q, ?cobj) ?dbb |- _ =>
           eapply db_wf_even; [exact Hw | exact Hi]
       end);
  repeat rewrite Zlength_cons; cbn; entailer_with ltac:(lia);
  pose proof (Zlength_nonneg tl); lia.

(* Both live arms of `enqueue` install the same route shape: the five
   existentials [aa] .. [qq] introduced from `enqueue_post_at` are substituted
   away, and the route equation [hm] is reduced past the freshness test [ht]
   so that the shared closer can rewrite with it. *)
Tactic Notation "msat_propagate_enqueue_route_shape_p2" ident(ht) ident(hm)
    ident(aa) ident(ll) ident(rr) ident(tt) ident(qq) :=
  subst aa; subst ll; subst rr; subst tt; subst qq;
  unfold msolver_propagation_enqueue_success,
    msolver_propagation_db_wmap_update,
    msolver_propagation_overlay, msolver_propagation_update in hm;
  cbn in hm; rewrite ht in hm;
  cbn [msolver_propagation_overlay msolver_propagation_update ] in hm.

(* The four `solver_solve` lbool-cell obligations differ only in which
   returned index [rv] they read back out of [mc]'s assignment array; the
   invariant is selected by shape, not by PreH position, because the
   numbering shifts whenever the obligation gains a binder. *)
Tactic Notation "msat_solve_lbool_cell_arm_p2" ident(mc) ident(rv) :=
  match goal with
  | H : msolver_inv_assuming_strong _ _ _ _ _ |- _ =>
      assert (lbool_cell (Znth rv (mt_assigns (ms_core mc)) 0)) as Hcell0
        by (apply (Forall_Znth_elim _ _ _ 0 rv
              (mtw_cells (msa_trail_wf (msas_weak H)))); lia)
  end;
  match goal with
  | Hc : lbool_cell _ |- _ =>
      unfold lbool_cell in Hc; destruct Hc as [Hv | [Hv | Hv]]
  end;
  rewrite Z.sub_0_r;
  rewrite signed_last_nbits_eq by lia;
  entailer_with ltac:(lia).

(* A watcher vector is rebuilt from its three header cells plus the used and the unused half of
   its payload; stating it once keeps the caller from re-spelling the whole cell list. *)
Lemma msat_vecp_rep_from_cells_p2 :
  forall slot ws cap base,
    Zlength ws <= cap ->
    0 < cap ->
    cap <= 2147483647 ->
    vecp_size_addr slot # Int |-> Zlength ws **
    vecp_cap_addr slot # Int |-> cap **
    vecp_ptr_addr slot # Ptr |-> base **
    PtrArray.full base (Zlength ws) ws **
    PtrArray.undef_seg base (Zlength ws) cap
    |-- vecp_rep slot ws cap.
Proof.
  intros slot ws cap base Hfit Hpos Hmax.
  pose proof (Zlength_nonneg ws).
  unfold vecp_rep.
  Exists base.
  unfold vecp_rep_at, PtrArray.full.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* The database well-formedness every live propagation scan carries, projected on its own so
   the spatial database rebuild can be applied before the scan is taken apart. *)
Lemma msat_propagate_scan_db_wf_p2 :
  forall n F A_arr K M p kept rest,
    solver_propagation_scan_semantics n F A_arr K M p 0 kept rest ->
    db_wf n (msolver_db M).
Proof.
  intros n F A_arr K M p kept rest Hsem.
  destruct Hsem as [Hlive | Hbad].
  - destruct Hlive as [_ [Hweak _]]. destruct Hweak as [_ Hinv].
    destruct K as [A_inst | A_proc].
    + exact (msw_db_wf Hinv).
    + exact (msa_db_wf Hinv).
  - exfalso. destruct Hbad as [Hnz _]. lia.
Qed.

(* The whole pure island of the real-migration `which_implies` obligation: from the live
   scan semantics and the physical scan facts, through the rewritten database entry
   [Hupdate], to the exit carrier the caller has to hand back.  It is stated as a helper
   because the VC proof would otherwise carry 180 more lines of pure plumbing
   between two spatial steps; the three length/inequality conjuncts in front of the
   carrier are the side conditions the caller's own closing `sep_apply` still needs. *)
Lemma msat_propagate_real_migrated_exit_p2 :
  forall n F A_arr K M0 Mentry Mscan prob_after learnt_after scan_wm_pre logical_words scan_wm_post scan_caps_pre
    scan_wcap scan_caps_post destination_cap candidate scan_current clause_contents watch0 false_lit lits stop k
    offset retained rest raw_suffix source_words moved garbage watch_memory candidate_post_memory
    migration_post_memory ii jj simp_count prop_count,
    solver_shape Mscan ->
    msolver_seed_shadow Mscan ->
    propagation_caller_frame M0 Mscan ->
    propagation_scan_frontier Mentry Mscan (Zlength scan_wm_pre) ->
    solver_propagation_scan_semantics n F A_arr K Mscan (Zlength scan_wm_pre) 0 retained rest ->
    rest = scan_current :: raw_suffix ->
    propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ->
    candidate_post_memory = watch_memory ->
    Znth ii candidate_post_memory 0 = scan_current ->
    migration_post_memory =
      replace_Znth ii (Znth ii candidate_post_memory 0) candidate_post_memory ->
    false_lit = lit_neg_c (Zlength scan_wm_pre) ->
    real_watch_pair (Zlength scan_wm_pre) clause_contents ->
    watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ->
    propagation_scan_candidate_layout scan_current lits stop k offset false_lit
      (Zlength scan_wm_pre) candidate (2 * lit_sign_c candidate - 1) clause_contents ->
    Znth (lit_var_c candidate) (mt_assigns (ms_core Mscan)) 0 <> 2 * lit_sign_c candidate - 1 ->
    propagation_destination_index (2 * ms_size Mscan) (Zlength scan_wm_pre)
      (lit_neg_c candidate) ->
    propagation_scan_slot Mscan (Zlength scan_wm_pre) scan_wm_pre logical_words scan_wm_post
      scan_caps_pre scan_wcap scan_caps_post ->
    simp_count = ms_simpdb_props Mscan ->
    prop_count = Znth 2 (ms_stats Mscan) 0 ->
    db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents
      (propagation_migrated_clause watch0 candidate false_lit offset clause_contents)
      prob_after learnt_after ->
    minisat_propagation_reuse_scan M0 Mscan (Zlength scan_wm_pre) 0 rest ->
    Zlength (ms_wm Mscan) = 2 * n /\
    0 <= lit_neg_c candidate < 2 * n /\
    lit_neg_c candidate <> Zlength scan_wm_pre /\
    Zlength scan_wm_post = Zlength scan_caps_post /\
    propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry Mscan
      (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
        (propagation_move_wmap (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
          (retained ++ raw_suffix) scan_wm_post scan_current)
        (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap scan_caps_post
          destination_cap))
      (Zlength scan_wm_pre) prob_after learnt_after scan_wm_pre scan_wm_post scan_caps_pre
      scan_caps_post scan_wcap destination_cap candidate scan_current source_words retained moved
      rest watch_memory ii jj (moved ++ (scan_current :: nil)) raw_suffix
      (garbage ++ (scan_current :: nil)) migration_post_memory simp_count prop_count /\
    minisat_propagation_reuse_scan M0
      (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
        (propagation_move_wmap (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
          (retained ++ raw_suffix) scan_wm_post scan_current)
        (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap scan_caps_post
          destination_cap)) (Zlength scan_wm_pre) 0 raw_suffix.
Proof.
  intros n F A_arr K M0 Mentry Mscan prob_after learnt_after scan_wm_pre logical_words scan_wm_post scan_caps_pre
    scan_wcap scan_caps_post destination_cap candidate scan_current clause_contents watch0 false_lit lits stop k
    offset retained rest raw_suffix source_words moved garbage watch_memory candidate_post_memory
    migration_post_memory ii jj simp_count prop_count H_solver_shape H_msolver_seed_shadow H_propagation_caller_frame
    H_propagation_scan_frontier H_solver_propagation_scan_semantics H_rest H_propagation_watch_scan_physical
    H_candidate_post_memory H_Znth H_migration_post_memory H_false_lit H_real_watch_pair H_watch0
    H_propagation_scan_candidate_layout H_Znth_2 H_propagation_destination_index H_propagation_scan_slot H_simp_count
    H_prop_count Hupdate Hreuse_entry.
  pose proof H_solver_propagation_scan_semantics as Hsembase.
  rewrite H_rest in Hsembase.
  pose proof Hsembase as Hsem0.
  destruct Hsem0 as [Hlive | Hdead].
  2: {
    destruct Hdead as [Hnz _].
    lia.
  }
  destruct Hlive as [_ [Hweak [Hlevel [Hheap [Hcovers [Hreasonless [Hp_level [Hp_wf [Hprocessed [Hfrontier
      Hcarrier]]]]]]]]]].
  destruct (solver_propagation_weak_reason_core n F A_arr K Mscan Hweak) as [Hsize [Hreasons _]].
  assert (Hcommon : db_wf n (msolver_db Mscan) /\ mtrail_wf n (ms_core Mscan) /\ stable_view (msolver_view n Mscan)
      /\ reason_head_ok Mscan /\ wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  {
    unfold solver_propagation_weak in Hweak.
    destruct K as [A_inst | A_proc]; cbn in Hweak; destruct Hweak as [_ Hctx].
    - split; [exact (msw_db_wf Hctx)|].
    split; [exact (msw_trail_wf Hctx)|].
    split; [exact (msw_stable Hctx)|].
    split; [exact (msw_reason_head Hctx)|exact (msw_wmap_exact Hctx)].
    - split; [exact (msa_db_wf Hctx)|].
    split; [exact (msa_trail_wf Hctx)|].
    split; [exact (msa_stable Hctx)|].
    split; [exact (msa_reason_head Hctx)|exact (msa_wmap_exact Hctx)].
  }
  destruct Hcommon as [Hdbwf [Htrail [Hstable [Hhead Hwmapold]]]].
  destruct (propagation_migrated_clause_structure__propagate_dbu n Mscan (Zlength
      scan_wm_pre) scan_current clause_contents watch0 false_lit lits stop k offset candidate (2 * lit_sign_c
      candidate - 1) prob_after learnt_after Hdbwf H_propagation_scan_candidate_layout H_real_watch_pair H_watch0
      Hupdate) as [co [a0 [a1 [tail [Hcontents [Hin [Hco [Htail [Hwatch [Hcandidate [Hcandin [Hcandwf [Hcandhead
      [Hwatchneq [Hcandneq Hperm]]]]]]]]]]]]]]].
  pose proof H_propagation_scan_candidate_layout as Hlayout.
  unfold propagation_scan_candidate_layout in Hlayout.
  destruct Hlayout as [_ [_ [_ [_ [_ [Hoffset [_ _]]]]]]].
  assert (Hoffset_co : 2 <= offset < Zlength (a0 :: a1 :: tail)) by (rewrite <- Hcontents; exact Hoffset); pose
      proof Hupdate as Hupdate_co; rewrite Hcontents in Hupdate_co.
  assert (Hnoowner : forall v, 0 <= v < n -> Znth v (ms_reason_words Mscan) 0 <> scan_current).
  {
    eapply no_live_reason_owner_candidate_not_false__propagate_dbu; [exact Hsize|exact
        Hdbwf|exact Htrail|exact Hstable|exact Hreasons| exact Hhead|exact Hin|exact Hcandin|exact Hcandwf|exact
        Hcandhead|exact H_Znth_2].
  }
  pose proof (propagation_migrated_entry_watchers_delta__propagate_dbu n (Zlength
      scan_wm_pre) scan_current co a0 a1 tail watch0 false_lit candidate offset Hp_wf H_false_lit Hco Hwatch
      Hoffset_co) as Hentrydelta; rewrite <- Hcontents in Hentrydelta.
  pose proof H_propagation_scan_slot as Hslot.
  destruct Hslot as [Hwm [Hwcaps [Hpre Hcapspre]]].
  pose proof (solver_shape_wm_len Mscan H_solver_shape) as Hwmlen.
  pose proof (solver_shape_wcaps_len Mscan H_solver_shape) as Hwcapslen.
  rewrite <- Hsize in Hwmlen, Hwcapslen.
  assert (Hp : 0 <= Zlength scan_wm_pre < 2 * n).
  {
    rewrite Hwm in Hwmlen.
    rewrite Zlength_app, Zlength_cons in Hwmlen.
    pose proof (Zlength_nonneg scan_wm_pre); pose proof (Zlength_nonneg scan_wm_post); lia.
  }
  pose proof H_propagation_destination_index as Hdestination.
  rewrite <- Hsize in Hdestination.
  pose proof Hdestination as Hdest_n.
  unfold propagation_destination_index in Hdestination.
  destruct Hdestination as [Hholenonneg [Htargetrange Htargetneq]].
  pose proof (focus_scan_carrier_words_expected__propagate_dbu _ _ _ _ _ Hcarrier) as
      Hexpectedold.
  assert (Hsourceold : Permutation logical_words (expected_watchers (msolver_db Mscan) (Zlength scan_wm_pre))).
  {
    pose proof (proj2 Hwmapold _ Hp) as Hx.
    rewrite Hwm in Hx.
    rewrite app_Znth2 in Hx by lia.
    replace (Zlength scan_wm_pre - Zlength scan_wm_pre) with 0 in Hx by lia.
    cbn in Hx.
    exact Hx.
  }
  assert (Hsource : Permutation ((retained ++ raw_suffix) ++ (scan_current :: nil)) logical_words).
  {
    eapply Permutation_trans.
    2: {
      eapply Permutation_trans; [exact Hexpectedold|apply Permutation_sym; exact Hsourceold].
    }
    rewrite <- app_assoc.
    apply Permutation_app_head.
    apply Permutation_app_comm.
  }
  destruct (propagation_move_wmap_cells__propagate_dbu n Mscan (Zlength scan_wm_pre)
      (lit_neg_c candidate) scan_wm_pre logical_words scan_wm_post scan_caps_pre scan_wcap scan_caps_post (retained
      ++ raw_suffix) scan_current co (propagation_migrated_clause watch0 candidate false_lit offset clause_contents)
      H_propagation_scan_slot Hp Hdest_n Hsource Hentrydelta Hwmlen) as [Hmove_len Hcells]; pose proof Hmove_len as
      Hbase_len; unfold propagation_move_wmap in Hbase_len; rewrite Zlength_replace_Znth in Hbase_len.
  assert (Hco_contents : co_lits co = clause_contents).
  {
    rewrite Hco, Hcontents.
    reflexivity.
  }
  pose proof (db_pair_lits_update_wmap_move__propagate_dbu n (ms_prob Mscan) (ms_learnt
      Mscan) scan_current clause_contents (propagation_migrated_clause watch0 candidate false_lit offset
      clause_contents) prob_after learnt_after (ms_wm Mscan) (propagation_move_wmap (Zlength scan_wm_pre) (lit_neg_c
      candidate) scan_wm_pre (retained ++ raw_suffix) scan_wm_post scan_current) co Hdbwf Hin Hco_contents Hupdate
      Hwmapold Hmove_len Hcells) as Hwmapnew.
  assert (Hmove_caps_len : Zlength (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap
      scan_caps_post destination_cap) = Zlength (ms_wcaps Mscan)).
  {
    unfold propagation_move_wcaps.
    rewrite Zlength_replace_Znth, Hwcaps.
    reflexivity.
  }
  pose proof (solver_propagation_weak_db_wmap_move__propagate_dbu n F A_arr K Mscan
      scan_current clause_contents (propagation_migrated_clause watch0 candidate false_lit offset clause_contents)
      prob_after learnt_after (propagation_move_wmap (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
      (retained ++ raw_suffix) scan_wm_post scan_current) (propagation_move_wcaps (lit_neg_c candidate)
      scan_caps_pre scan_wcap scan_caps_post destination_cap) Hweak Hupdate Hperm Hnoowner ltac:(rewrite Hmove_len,
      Hwmlen; reflexivity) Hmove_caps_len Hwmapnew) as Hweakroute.
  pose proof (propagation_migrated_frontier_transport__propagate_dbu n Mscan (Zlength
      scan_wm_pre) scan_current co a0 a1 tail watch0 false_lit candidate offset prob_after learnt_after Hdbwf Hin
      Hco Hoffset_co Hcandwf H_Znth_2 Hupdate_co Hfrontier) as Hfrontierroute.
  pose proof (propagation_migrated_focus_transport__propagate_dbu n Mscan (Zlength
      scan_wm_pre) scan_current co a0 a1 tail watch0 false_lit candidate offset prob_after learnt_after
      (minisat_processed n (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
      retained raw_suffix Hdbwf Hin Hco Hwatch Hp_wf H_false_lit Hoffset_co Hwatchneq Hcandneq Hupdate_co Hcarrier)
      as Hcarrierroute.
  pose proof (propagation_migrated_scan_semantics__propagate_dbu n F A_arr K Mscan (Zlength
      scan_wm_pre) retained scan_current raw_suffix prob_after learnt_after (propagation_move_wmap (Zlength
      scan_wm_pre) (lit_neg_c candidate) scan_wm_pre (retained ++ raw_suffix) scan_wm_post scan_current)
      (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap scan_caps_post destination_cap) Hsembase
      Hweakroute Hfrontierroute Hcarrierroute) as Hsemroute.
  destruct (propagation_migrated_physical_step__propagate_dbu source_words retained moved
      rest garbage watch_memory candidate_post_memory migration_post_memory raw_suffix ii jj scan_current H_rest
      H_propagation_watch_scan_physical H_candidate_post_memory H_Znth H_migration_post_memory) as [Hmemory [Hstep
      Hphysical]].
  destruct (propagation_move_split_shape__propagate_dbu (2*n) (Zlength scan_wm_pre)
      (lit_neg_c candidate) scan_wm_pre (retained ++ raw_suffix) scan_wm_post scan_caps_pre scan_wcap scan_caps_post
      scan_current destination_cap eq_refl Hcapspre Hbase_len ltac:(rewrite <- Hwcaps; exact Hwcapslen) Hdest_n) as
      [Hsplitwm [Hsplitcaps [Hsplitpre Hsplitcapspre]]].
  set (Mroute := msolver_propagation_db_wmap_update Mscan prob_after learnt_after (propagation_move_wmap (Zlength
      scan_wm_pre) (lit_neg_c candidate) scan_wm_pre (retained ++ raw_suffix) scan_wm_post scan_current)
      (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap scan_caps_post destination_cap)).
  assert (Hreuseroute : minisat_propagation_reuse_scan M0 Mroute
    (Zlength scan_wm_pre) 0 raw_suffix).
  {
    set (normalized := watch0 :: lit_neg_c (Zlength scan_wm_pre) :: tail).
    set (migrated := propagation_migrated_clause
      watch0 candidate false_lit offset clause_contents).
    assert (Hnormalized : propagation_normalized_clause
      watch0 (lit_neg_c (Zlength scan_wm_pre)) clause_contents = normalized).
    { unfold propagation_normalized_clause, normalized. rewrite Htail. reflexivity. }
    assert (Hnormperm : Permutation normalized clause_contents).
    { unfold normalized. rewrite Hcontents, <- H_false_lit.
      destruct Hwatch as [[Ha Hw]|[Ha Hw]]; subst;
        [apply perm_swap|apply Permutation_refl]. }
    assert (Hfactor : exists norm_prob norm_learnt,
      db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan)
        scan_current clause_contents normalized norm_prob norm_learnt /\
      db_pair_lits_update norm_prob norm_learnt
        scan_current normalized migrated prob_after learnt_after).
    { destruct Hupdate as
        [[obj [pre [post [Hprob_before [Hwords [Hp' Hl']]]]]]
        |[obj [pre [post [Hlearnt_before [Hwords [Hp' Hl']]]]]]].
      - exists (pre ++ (scan_current, clause_obj_with_lits obj normalized) :: post),
          (ms_learnt Mscan). split.
        + left. exists obj, pre, post. repeat split; assumption || reflexivity.
        + left. exists (clause_obj_with_lits obj normalized), pre, post.
          repeat split; assumption || reflexivity.
      - exists (ms_prob Mscan),
          (pre ++ (scan_current, clause_obj_with_lits obj normalized) :: post). split.
        + right. exists obj, pre, post. repeat split; assumption || reflexivity.
        + right. exists (clause_obj_with_lits obj normalized), pre, post.
          repeat split; assumption || reflexivity. }
    destruct Hfactor as [norm_prob [norm_learnt [Hnormupdate Hmoveupdate]]].
    set (Mnorm := msolver_propagation_db_wmap_update Mscan
      norm_prob norm_learnt (ms_wm Mscan) (ms_wcaps Mscan)).
    assert (Hreusenorm : minisat_propagation_reuse_scan M0 Mnorm
      (Zlength scan_wm_pre) 0 (scan_current :: raw_suffix)).
    { unfold Mnorm. eapply minisat_propagation_reuse_normalize__api_reentry
        with (current := scan_current) (a0 := a0) (a1 := a1)
          (tail := tail) (other := watch0).
      - rewrite <- Hcontents, Hnormalized. exact Hnormupdate.
      - rewrite <- H_false_lit. exact Hwatch.
      - rewrite <- H_rest. exact Hreuse_entry. }
    assert (Hdbnorm : db_wf n (msolver_db Mnorm)).
    { eapply db_pair_lits_update_db_wf__propagate_dbu;
        [exact Hdbwf|exact Hnormperm|exact Hnormupdate]. }
    assert (Hdbroute : db_wf n (prob_after ++ learnt_after)).
    { eapply db_pair_lits_update_db_wf__propagate_dbu;
        [exact Hdbwf|exact Hperm|exact Hupdate]. }
    assert (Hreal : is_tag scan_current = false).
    { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan)
        scan_current co Hdbwf Hin). }
    set (newtail := replace_Znth (offset - 2) false_lit tail).
    assert (Hmigrated : migrated = watch0 :: candidate :: newtail).
    { unfold migrated, propagation_migrated_clause. rewrite Htail.
      rewrite !replace_Znth_cons by lia.
      replace (offset - 1 - 1) with (offset - 2) by lia. reflexivity. }
    assert (Hmoveperm : Permutation normalized (watch0 :: candidate :: newtail)).
    { rewrite <- Hmigrated. eapply Permutation_trans;
        [exact Hnormperm|apply Permutation_sym; exact Hperm]. }
    assert (Hcandidate_safe : ~ lit_false (mt_assigns (ms_core Mnorm)) candidate).
    { unfold lit_false. change (Znth (lit_var_c candidate)
        (mt_assigns (ms_core Mscan)) 0 <> - lit_sig candidate).
      replace (- lit_sig candidate) with (2 * lit_sign_c candidate - 1)
        by (unfold lit_sig, lit_sign_c; destruct (Z.odd candidate); reflexivity).
      exact H_Znth_2. }
    change (minisat_propagation_reuse_scan M0
      (msolver_propagation_db_wmap_update Mnorm prob_after learnt_after
        (propagation_move_wmap (Zlength scan_wm_pre) (lit_neg_c candidate)
          scan_wm_pre (retained ++ raw_suffix) scan_wm_post scan_current)
        (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap
          scan_caps_post destination_cap)) (Zlength scan_wm_pre) 0 raw_suffix).
    eapply minisat_propagation_reuse_migrate__api_reentry
      with (n := n) (current := scan_current) (other := watch0)
        (oldtail := tail) (candidate := candidate) (newtail := newtail).
    - exact Hdbnorm.
    - exact Hdbroute.
    - exact Hreal.
    - rewrite <- Hmigrated. exact Hmoveupdate.
    - exact Hmoveperm.
    - exact (proj1 Hprocessed).
    - exact Hcandidate_safe.
    - exact Hreusenorm.
  }
  assert (Hshaperoute : solver_shape Mroute).
  {
    unfold solver_propagation_weak in Hweakroute.
    destruct K as [A_inst|A_proc]; cbn in Hweakroute; [exact (msw_shape (proj2 Hweakroute))| exact (msa_shape (proj2
        Hweakroute))].
  }
  assert (Hseedroute : msolver_seed_shadow Mroute).
  {
    unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_msolver_seed_shadow.
  }
  assert (Hcallerroute : propagation_caller_frame M0 Mroute).
  {
    unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_propagation_caller_frame.
  }
  assert (Hscanroute : propagation_scan_frontier Mentry Mroute (Zlength scan_wm_pre)).
  {
    unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_propagation_scan_frontier.
  }
  assert (Hexit : propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry Mscan Mroute (Zlength scan_wm_pre)
      prob_after learnt_after scan_wm_pre scan_wm_post scan_caps_pre scan_caps_post scan_wcap destination_cap
      candidate scan_current source_words retained moved rest watch_memory ii jj (moved ++ (scan_current :: nil))
      raw_suffix (garbage ++ (scan_current :: nil)) migration_post_memory simp_count prop_count).
  {
    eapply propagation_real_migrated_exit_intro__propagate_dbu; [reflexivity|exact
        Hstep|exact Hshaperoute|exact Hseedroute|exact Hcallerroute| exact Hscanroute|exact Hsemroute| | |exact
        Hmemory|exact Hphysical| exact Hsplitwm|exact Hsplitcaps|exact Hsplitpre|exact Hsplitcapspre].
    - unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_simp_count.
    - unfold Mroute, msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    exact H_prop_count.
  }
  assert (Hpostcaps : Zlength scan_wm_post = Zlength scan_caps_post).
  {
    pose proof (solver_shape_wm_len Mscan H_solver_shape) as Hwm2; pose proof (solver_shape_wcaps_len Mscan
        H_solver_shape) as Hcaps2; rewrite Hwm, Zlength_app, Zlength_cons in Hwm2; rewrite Hwcaps, Zlength_app,
        Zlength_cons in Hcaps2; lia.
  }
  split; [exact Hwmlen|].
  split; [exact Htargetrange|].
  split; [exact Htargetneq|].
  split; [exact Hpostcaps|]. split; [exact Hexit|exact Hreuseroute].
Qed.


(* The three header cells of the solver's `tagged` vector are spelled with the
   C field syntax in the obligation but with [veci_size_addr] / [veci_cap_addr]
   / [veci_ptr_addr] inside [veci_rep_at]; these equations let the caller
   rewrite the spatial side back into the [veci_rep_at] spelling.  [s] is the
   solver pointer the obligation is stated over. *)
Tactic Notation "msat_veci_tagged_addr_facts_p2" ident(s) :=
  assert (Htag_size :
    &( s # "solver_t" ->ₛ "tagged" .ₛ "size") =
    veci_size_addr (&( s # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_size_addr; csimpl; reflexivity);
  assert (Htag_cap :
    &( s # "solver_t" ->ₛ "tagged" .ₛ "cap") =
    veci_cap_addr (&( s # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_cap_addr; csimpl; reflexivity);
  assert (Htag_ptr :
    &( s # "solver_t" ->ₛ "tagged" .ₛ "ptr") =
    veci_ptr_addr (&( s # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_ptr_addr; csimpl; reflexivity).

(* Same three equations for the solver's `stack` vector; the removable-literal
   obligations that rebuild both vectors call this one right after
   [msat_veci_tagged_addr_facts_p2]. *)
Tactic Notation "msat_veci_stack_addr_facts_p2" ident(s) :=
  assert (Hstack_size :
    &( s # "solver_t" ->ₛ "stack" .ₛ "size") =
    veci_size_addr (&( s # "solver_t" ->ₛ "stack"))) by
    (unfold veci_size_addr; csimpl; reflexivity);
  assert (Hstack_cap :
    &( s # "solver_t" ->ₛ "stack" .ₛ "cap") =
    veci_cap_addr (&( s # "solver_t" ->ₛ "stack"))) by
    (unfold veci_cap_addr; csimpl; reflexivity);
  assert (Hstack_ptr :
    &( s # "solver_t" ->ₛ "stack" .ₛ "ptr") =
    veci_ptr_addr (&( s # "solver_t" ->ₛ "stack"))) by
    (unfold veci_ptr_addr; csimpl; reflexivity).

(* Both live arms of the unit-propagation enqueue reach the same post-state:
   the seed shadow, the caller frame, the binary-clause part and the frame of
   the untouched solver fields all transport along the route equation [hm]
   ([hm0] is its un-reduced form, needed by the frame lemma).  [hs] / [hc] /
   [hd] are the obligation's own shadow, caller-frame and database facts, [mr]
   / [mc] the routed and the scanning solver, [m0] the caller's solver and
   [s] the solver pointer. *)
Tactic Notation "msat_propagate_unit_route_facts_p2" ident(hm) ident(hm0)
    ident(hs) ident(hc) ident(hd) ident(mr) ident(mc) ident(m0) ident(s) :=
  assert (Hseed_route : msolver_seed_shadow mr) by (rewrite hm; exact hs);
  assert (Hcaller_route : propagation_caller_frame m0 mr) by
    (rewrite hm; exact hc);
  assert (Hbinary : solver_binary_rep mr = solver_binary_rep mc) by
    (rewrite hm; unfold solver_binary_rep; reflexivity);
  assert (Hframe : solver_propagate_frame s mr =
      solver_propagate_frame s mc) by
    (destruct (db_pair_lits_update_words__propagate _ _ _ _ _ _ _ hd)
       as [Hprob_words Hlearnt_words];
     rewrite hm0; apply solver_propagate_frame_db_enqueue__propagate;
     assumption).

(* The spatial half of both unit-success arms: the watcher memory is the one
   the scan started from ([hcm] / [hmem]), and the routed solver differs from
   the scanning one only in the parts [hb] / [hf] / [hm] transport, so the
   scan core refolds into the statistics lemma.  [pc] is the propagation
   counter, [s] the solver pointer, [mc] the scanning solver. *)
Tactic Notation "msat_propagate_unit_scan_refold_p2" ident(hcm) ident(hmem)
    ident(hb) ident(hf) ident(hm) ident(pc) ident(s) ident(mc) :=
  rewrite hcm, <- hmem;
  unfold solver_propagation_scan_core_at;
  rewrite hb, hf, hm;
  (* A bare `cbn` reduces the pointer stride to the 32-bit literal on this
     side of the entailment, while the `unfold PtrArray.seg` below
     reintroduces the symbolic `ptr_size_Z` on the other -- and nothing folds
     a literal back into a constant.  Blocking delta on the arch constant
     keeps both sides spelled the same way, with no width named anywhere.
     `Znth` is blocked for the same reason: reducing it to
     `nth (Pos.to_nat 3)` on one side only would break the closing `exact`. *)
  cbn -[ptr_size_Z Znth];
  unfold CharArray.seg, IntArray.seg, PtrArray.seg;
  (* and again after the unfolds, which reintroduce `sizeof (CHAR)` /
     `sizeof (INT)` on the left while the right already carries their
     literals.  Same two constants stay blocked, so the pointer stride
     remains symbolic on both sides. *)
  cbn -[ptr_size_Z Znth];
  unfold replace_Znth;
  set_String_name; sepcon_assoc_change; sepcon_cancel; subst_all_strings;
  exact (stats_propagate_scan_refold__propagate s pc (ms_stats mc)).

(* The pure half of both unit-success arms: every residual conjunct is one of
   the eight facts already established about the routed solver, or follows
   from the route equation [hm] once the enqueue is reduced. *)
Tactic Notation "msat_propagate_unit_pure_close_p2" ident(hsh) ident(hsd)
    ident(hcl) ident(hfr) ident(hsm) ident(hph) ident(hlg) ident(hml)
    ident(hm) :=
  split_pures; dump_pre_spatial;
  try exact hsh; try exact hsd; try exact hcl; try exact hfr;
  try exact hsm; try exact hph; try exact hlg; try exact hml;
  try assumption; try reflexivity; try lia;
  try rewrite hm;
  cbn [mt_enqueue mt_push]; try assumption; try reflexivity; try lia.

(* ===== clause_is_lit return wits (1 proofs) ===== *)
Lemma proof_of_clause_is_lit_return_wit_1 : clause_is_lit_return_wit_1.
Proof.
  Unfold.
  intros c_pre PreH1.
  destruct (Z.odd c_pre) eqn:Hodd.
  - Left.
    assert (Hland : Z.land c_pre 1 = 1).
    { rewrite land_1_mod2.
      apply Z.odd_spec in Hodd. destruct Hodd as [k ->].
      apply Zmod2_pack. lia. }
    unfold clause_is_lit_result, is_tag, msat_true, msat_false.
    entailer_with ltac:(lia).
  - Right.
    assert (Heven : Z.even c_pre = true).
    { rewrite <- Z.negb_odd, Hodd. reflexivity. }
    assert (Hland : Z.land c_pre 1 = 0).
    { rewrite land_1_mod2.
      apply Z.even_spec in Heven. destruct Heven as [k ->].
      replace (2 * k) with (2 * k + 0) by lia.
      apply Zmod2_pack. lia. }
    unfold clause_is_lit_result, is_tag, msat_true, msat_false.
    msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_read_lit return wits (1 proofs) ===== *)
Lemma proof_of_clause_read_lit_return_wit_1 : clause_read_lit_return_wit_1.
Proof.
  Unfold.
  left.
  intros c_pre PreH1 PreH2 PreH3 PreH4.
  bind_fact ( 0 <= c_pre ) as H_c_pre.
  bind_fact ( tagged_word c_pre ) as H_tagged_word.
  bind_fact ( 0 <= tag_lit c_pre ) as H_tag_lit.
  bind_fact ( tag_lit c_pre <= 2147483647 ) as H_tag_lit_2.
  pose proof
    (clause_read_lit_value__clause_is_lit
       c_pre H_c_pre H_tagged_word H_tag_lit H_tag_lit_2) as Hread.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_analyze entail wits ===== *)
Lemma proof_of_solver_analyze_entail_wit_14_4_learnt : solver_analyze_entail_wit_14_4_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame cap_done words_done Sdone Rdone learnt_done Mdone.
Qed.

Lemma proof_of_solver_analyze_entail_wit_14_5_learnt : solver_analyze_entail_wit_14_5_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame cap_done words_done Sdone Rdone learnt_done Mdone.
Qed.

Lemma proof_of_solver_analyze_entail_wit_16 : solver_analyze_entail_wit_16.
Proof.
  unfold solver_analyze_entail_wit_16, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( Znth (retval - 0) (ms_tags Mresolved) 0 = 0 ) as H_Znth.
  bind_fact ( retval = lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mresolved)) 0) ) as H_retval.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  replace (retval - 0) with retval in H_Znth by lia.
  replace (ind - 0) with ind in H_retval by lia.
  assert (Hzero :
    Znth (trail_var (ms_core Mresolved) ind) (ms_tags Mresolved) 0 = 0).
  { unfold trail_var. rewrite <- H_retval. exact H_Znth. }
  destruct (analyze_backward_scan_decr__analyze
    anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind
    Sresolved Rresolved learnt_resolved H_analyze_backward_scan_inv Hzero)
    as [Hinv' [Hind' [Hvar' Hguard']]].
  entailer_with ltac:(lia).
  - replace (ind - 1 - 0) with (ind - 1) by lia.
    replace (lit_var_c (Znth (ind - 1) (mt_trail (ms_core Mresolved)) 0) - 0)
      with (lit_var_c (Znth (ind - 1) (mt_trail (ms_core Mresolved)) 0)) by lia.
    fold (trail_var (ms_core Mresolved) (ind - 1)). exact Hguard'.
  - replace (ind - 1 - 0) with (ind - 1) by lia.
    fold (trail_var (ms_core Mresolved) (ind - 1)). exact (proj2 Hvar').
  - replace (ind - 1 - 0) with (ind - 1) by lia.
    fold (trail_var (ms_core Mresolved) (ind - 1)). exact (proj1 Hvar').
Qed.

Lemma proof_of_solver_analyze_entail_wit_17 : solver_analyze_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( retval = lit_var_c (Znth (ind - 1 + 1 - 0) (mt_trail (ms_core Mresolved)) 0) ) as H_retval.
  bind_fact ( Znth (retval_2 - 0) (ms_tags Mresolved) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_2 = lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mresolved)) 0) ) as H_retval_2.
  bind_fact ( analysis_core_equiv M0 Mresolved ) as H_analysis_core_equiv.
  bind_fact ( msolver_seed_shadow Mresolved ) as H_msolver_seed_shadow.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  replace (ind - 1 + 1 - 0) with ind in * by lia.
  replace (retval_2 - 0) with retval_2 in * by lia.
  replace (retval - 0) with retval in * by lia.
  replace (ind - 0) with ind in * by lia.
  fold (trail_var (ms_core Mresolved) ind) in H_retval, H_retval_2.
  rewrite H_retval_2 in H_Znth.
  rewrite H_retval in *.
  pose proof H_analyze_backward_scan_inv as Hscan.
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Htail
      [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mresolved anz_focus Hready) as [Hsize Hreason_core].
  assert (Hstats_pure :
    solver_analyze_frame s_pre Mresolved anz_wl |--
      “ Zlength (ms_stats Mresolved) = 11 ”).
  { unfold solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame.
    Intros asg. entailer_with ltac:(lia). }
  prop_apply Hstats_pure.
  Intros_p Hstats.
  prop_apply (DoubleArray.seg_Zlength activity_ptr_back 0 anz_n
    (ms_activity Mresolved)).
  Intros_p Hactivity_raw.
  assert (Hactivity : Zlength (ms_activity Mresolved) = anz_n) by lia.
  assert (Hshape : solver_shape Mresolved).
  { eapply analysis_cancel_ready_shape__analyze; eauto. }
  assert (Hveci_pure :
    veci_rep learnt_pre words_resolved cap_resolved |--
      “ 0 <= Zlength words_resolved <= cap_resolved /\
        0 < cap_resolved <= INT_MAX ”).
  { unfold veci_rep, veci_rep_at. Intros learnt_ptr. entailer_with ltac:(lia). }
  prop_apply Hveci_pure.
  Intros_p Hveci.
  destruct Hveci as [[Hlen0 Hlencap] [Hcappos Hcapmax]].
  match goal with
  | |- ?P |-- _ =>
      assert (Hspatial : P |--
        solver_rep_analyze_at s_pre Mresolved reasons levels_ptr trail tags anz_wl **
        veci_rep learnt_pre words_resolved cap_resolved)
  end.
  { rewrite Hsize.
    (* [analyze_frame_join] consumes the stack vector and the two literal
       counters, which sit inside the folded [solver_analyze_inert_at]
       bundle; open it so the join and the closing [solver_rep_analyze_at]
       cancellation see the nine raw atoms. *)
    unfold solver_analyze_inert_at.
    Intros.
    sep_apply (analyze_frame_join s_pre Mresolved anz_wl).
    Intros asg.
    unfold solver_rep_analyze_at, solver_rep_at.
    Exists activity_ptr_back asg orderpos_ptr_back.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
      solver_trail_array_rep.
    entailer_with ltac:(int_auto). }
  destruct (Z.eq_dec cnt 1) as [Hcntone|Hcntnotone].
  - pose proof (analyze_backward_scan_exit__analyze
      anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind
      Sresolved Rresolved learnt_resolved H_analyze_backward_scan_inv H_Znth Hcntone) as Hexit.
    rewrite Hsize in *.
    Left.
    assert (Htwice : 2 * ms_size Mresolved <= INT_MAX)
      by (unfold solver_shape in Hshape; tauto).
    (* Peel the eight pure conjuncts of the RHS uniformly; each is either a
       hypothesis in scope or arithmetic.  The ninth conjunct is the spatial
       residue.  (Was a nine-deep bullet ladder.) *)
    repeat (apply _derivable1_andp_intros;
            [ apply derivable1s_coq_prop_r; solve [ assumption | lia ] | ]).
    exact Hspatial.
  - assert (Hcntgt : 1 < cnt) by lia.
    destruct (analyze_backward_scan_selected__analyze
      anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind
      Sresolved Rresolved learnt_resolved H_analyze_backward_scan_inv H_Znth Hcntgt)
      as [Cnext [Hnonzero [Htarget Hselected]]].
    rewrite Hsize in *.
    Right. Exists Cnext.
    assert (Htwice : 2 * ms_size Mresolved <= INT_MAX)
      by (unfold solver_shape in Hshape; tauto).
    apply _derivable1_andp_intros.
    + entailer_with ltac:(lia).
    + exact Hspatial.
Qed.

Lemma proof_of_solver_analyze_entail_wit_23 : solver_analyze_entail_wit_23.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_resolution_exit anz_n anz_F anz_A_arr K Mresolution anz_focus p words_before ) as
      H_analyze_resolution_exit.
  pose proof (analyze_resolution_exit_uip__analyze
    anz_n anz_F anz_A_arr K Mresolution anz_focus p words_before H_analyze_resolution_exit) as Huip.
  cbn in Huip.
  destruct Huip as
    [Hready [Hlen [Hwf [Hnodup [Hcert [Htags_exact [Hincl Hscope]]]]]]].
  Exists (replace_Znth 0 (lit_neg_c p) words_before).
  entailer_with ltac:(lia).
  unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists q.
  rewrite Zlength_replace_Znth.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_entail_wit_25 : solver_analyze_entail_wit_25.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( retval = lit_var_c (Znth (i - 0) words_uip 0) ) as H_retval.
  bind_fact ( 0 <= minl ) as Hmin0.
  bind_fact ( minl <= UINT_MAX ) as Hminmax.
  set (bit := unsigned_last_nbits
    (Z.shiftl 1 (Z.land (Znth (lit_var_c (Znth i words_uip 0))
      (mt_levels (ms_core Mresolution)) 0) 31)) 32).
  assert (Hbit : 0 <= bit < 2 ^ 32).
  { subst bit. apply unsigned_Lastnbits_range. lia. }
  assert (Hmin : 0 <= minl < 2 ^ 32).
  { split; [exact Hmin0|].
    change (minl < 4294967296).
    lia. }
  assert (Hlor : 0 <= Z.lor minl bit <= UINT_MAX).
  { pose proof (unsigned_last_nbits_lor_distr_missing
      minl bit 32 ltac:(lia) Hmin Hbit) as E.
    pose proof (unsigned_Lastnbits_range (Z.lor minl bit) 32 ltac:(lia)) as Hr.
    rewrite E in Hr.
    change (0 <= Z.lor minl bit < 4294967296) in Hr.
    lia. }
  subst bit.
  replace (i - 0) with i in H_retval by lia.
  rewrite <- H_retval in Hlor.
  entailer_with ltac:(lia).
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  entailer_with ltac:(lia).
  all: replace (retval - 0) with retval by lia; lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_26 : solver_analyze_entail_wit_26.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( solver_shape Mresolution ) as H_solver_shape.
  bind_fact ( Forall (lit_wf_c anz_n) words_uip ) as H_Forall.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mresolution anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mresolution) (ms_tagged Mresolution) ) as H_analysis_tags_exact.
  bind_fact ( analyze_clause_cert anz_n anz_F Mresolution words_uip ) as H_analyze_clause_cert.
  bind_fact ( minimize_tag_scope anz_n Mresolution words_uip nil ) as H_minimize_tag_scope.
  pose proof (analyze_clause_cert_vars_in_trail__analyze
    anz_n anz_F Mresolution words_uip H_analyze_clause_cert) as Htrail.
  pose proof (analyze_minimize_init__analyze
    anz_n Mresolution words_uip ltac:(lia) H_Forall H_analysis_tags_exact H_minimize_tag_scope) as Hinit.
  pose proof (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mresolution anz_focus H_analysis_cancel_ready) as [Hsize Hreason_core].
  Exists cap_before (sublist 0 1 words_uip) (@nil Z) words_uip (@nil Z) Mresolution.
  entailer_with ltac:(lia).
  rewrite Hsize.
  sep_apply_r_atomic (solver_reason_levels_veci_join__analyze
    learnt_pre lits words_uip cap_before s_pre Mresolution reasons levels_ptr trail tags
    anz_wl H_solver_shape ltac:(lia) ltac:(lia)).
  entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_27_1 : solver_analyze_entail_wit_27_1.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( solver_shape Mmin_2 ) as H_solver_shape.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin_2 anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( 1 <= j ) as H_j.
  bind_fact ( j <= i ) as H_j_2.
  bind_fact ( incl (map lit_var_c words_min_2) (map lit_var_c (mt_trail (ms_core Mmin_2))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min_2) (ms_tagged Mmin_2) ) as H_incl_2.
  assert (Hcur_in : In (Znth i words_min_2 0) words_min_2).
  { apply Znth_In. lia. }
  pose proof (replace_Znth_incl_self__analyze
    words_min_2 j (Znth i words_min_2 0) ltac:(lia) Hcur_in) as Hself.
  pose proof (incl_map_of_incl__analyze
    lit_var_c _ _ Hself) as Hmap.
  assert (Htagged : incl
    (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
    (ms_tagged Mmin_2)).
  { intros x Hx. apply H_incl_2, Hmap, Hx. }
  assert (Htrail : incl
    (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
    (map lit_var_c (mt_trail (ms_core Mmin_2)))).
  { intros x Hx. apply H_incl, Hmap, Hx. }
  pose proof (analyze_minimize_keep__analyze
    anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j
    H_analyze_minimize_loop_inv ltac:(lia) H_j H_j_2) as Hkeep.
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mmin_2 anz_focus H_analysis_cancel_ready) as [Hsize _].
  assert (Hreplen :
    Zlength (replace_Znth j (Znth i words_min_2 0) words_min_2) =
    Zlength words_min_2) by apply Zlength_replace_Znth.
  unfold analyze_minimize_loop_inv in Hkeep.
  Exists cap_min_2
    (kept_2 ++ Znth i words_min_2 0 :: nil)
    removed_2
    (replace_Znth j (Znth i words_min_2 0) words_min_2)
    T_2 Mmin_2.
  entailer_with ltac:(int_auto).
  replace (i - 0) with i by lia.
  rewrite Hsize.
  rewrite <- Hreplen.
  unfold IntArray.full.
  sep_apply_r_atomic (solver_reason_levels_veci_written_join__analyze
    learnt_pre lits
    (replace_Znth j (Znth i words_min_2 0) words_min_2) cap_min_2
    s_pre Mmin_2 reasons levels_ptr trail tags anz_wl H_solver_shape
    ltac:(rewrite Zlength_replace_Znth; lia) ltac:(lia)).
  entailer_with ltac:(lia).
  apply IntArray.full_to_seg.
Qed.

Lemma proof_of_solver_analyze_entail_wit_27_2 : solver_analyze_entail_wit_27_2.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mmin_2) (ms_tagged Mmin_2) ) as H_analysis_tags_exact.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( 1 <= j ) as H_j.
  bind_fact ( j <= i ) as H_j_2.
  bind_fact ( Forall (lit_wf_c anz_n) words_min_2 ) as H_Forall.
  bind_fact ( incl (map lit_var_c words_min_2) (map lit_var_c (mt_trail (ms_core Mmin_2))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min_2) (ms_tagged Mmin_2) ) as H_incl_2.
  unfold solver_lit_removable_post.
  Intros Mpost.
  Intros.
  destruct H as
    (Hready' & Hseed' & Hequiv' & Htagcap' & Hstackcap' & Hret).
  destruct Hret as [(Hret & Etags & Etagged) | (Hret & Hstack & Hfresh)].
  - replace (i - 0) with i in * by lia.
    pose proof (analyze_minimize_keep__analyze
      anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j
      H_analyze_minimize_loop_inv ltac:(lia) H_j H_j_2) as Hkeep.
    pose proof (analyze_minimize_loop_inv_transport__analyze
      anz_n Mmin_2 Mpost words_uip
      (kept_2 ++ Znth i words_min_2 0 :: nil) removed_2
      (replace_Znth j (Znth i words_min_2 0) words_min_2) T_2
      (i + 1) (j + 1) Hequiv' Etags Etagged Hkeep) as Hkeep'.
    assert (Hcur : In (Znth i words_min_2 0) words_min_2).
    { apply Znth_In. lia. }
    pose proof (replace_Znth_incl_self__analyze
      words_min_2 j (Znth i words_min_2 0) ltac:(lia) Hcur) as Hincl.
    pose proof (incl_map_of_incl__analyze lit_var_c _ _ Hincl)
      as Hmap.
    assert (Hinc_tag : incl
      (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
      (ms_tagged Mpost)).
    { rewrite Etagged. intros x Hx. apply H_incl_2, Hmap, Hx. }
    assert (Ecore : ms_core Mpost = ms_core Mmin_2).
    { unfold analysis_core_equiv in Hequiv'. tauto. }
    assert (Hinc_trail : incl
      (map lit_var_c (replace_Znth j (Znth i words_min_2 0) words_min_2))
      (map lit_var_c (mt_trail (ms_core Mpost)))).
    { rewrite Ecore. intros x Hx. apply H_incl, Hmap, Hx. }
    assert (Hwfwords : Forall (lit_wf_c anz_n)
      (replace_Znth j (Znth i words_min_2 0) words_min_2)).
    { apply Forall_replace_Znth; [exact H_Forall|].
      eapply Forall_Znth_elim; [exact H_Forall|lia]. }
    assert (Hbound : i + 1 <=
      Zlength (replace_Znth j (Znth i words_min_2 0) words_min_2)).
    { rewrite Zlength_replace_Znth. lia. }
    assert (Hcert : analyze_clause_cert anz_n anz_F Mpost words_uip).
    { eapply analyze_clause_cert_transport__analyze; eauto. }
    assert (Htagsexact :
      analysis_tags_exact anz_n (ms_tags Mpost) (ms_tagged Mpost)).
    { rewrite Etags, Etagged. exact H_analysis_tags_exact. }
    assert (Hcore : analysis_core_equiv M0 Mpost).
    { eapply analysis_core_equiv_trans__analyze; eauto. }
    sep_apply (solver_rep_analyze_at_shape__analyze
      s_pre Mpost reasons levels_ptr trail tags anz_wl).
    Intros.
    Exists cap_min_2 (kept_2 ++ Znth i words_min_2 0 :: nil)
      removed_2 (replace_Znth j (Znth i words_min_2 0) words_min_2)
      T_2 Mpost.
    entailer_with ltac:(lia).
    unfold IntArray.full, veci_rep_at, veci_size_addr,
      veci_cap_addr, veci_ptr_addr.
    rewrite Zlength_replace_Znth. entailer_with ltac:(int_auto).
  - lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_27_3 : solver_analyze_entail_wit_27_3.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mmin_2 anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_2 words_uip kept_2 removed_2 words_min_2 T_2 i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( incl (map lit_var_c words_min_2) (map lit_var_c (mt_trail (ms_core Mmin_2))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min_2) (ms_tagged Mmin_2) ) as H_incl_2.
  unfold solver_lit_removable_post.
  Intros Mpost.
  Intros.
  destruct H as
    (Hready' & Hseed' & Hequiv' & Htagcap' & Hstackcap' & Hret).
  destruct Hret as [(Hret & Etags & Etagged) | (Hret & Hstack & Hfresh)].
  - lia.
  - destruct Hfresh as [fresh [Etagged [Htags' [Hwit Hbelow]]]].
    replace (i - 0) with i in * by lia.
    pose proof (analyze_minimize_remove__analyze
      anz_n anz_F anz_A_arr K anz_focus Mmin_2 Mpost words_uip kept_2 removed_2
      words_min_2 T_2 i j fresh H_analyze_minimize_loop_inv ltac:(lia) H_analysis_cancel_ready Hequiv'
      Etagged Htags' Hwit Hbelow) as Hremove.
    assert (Ecore : ms_core Mpost = ms_core Mmin_2).
    { unfold analysis_core_equiv in Hequiv'. tauto. }
    assert (Hinc_trail : incl (map lit_var_c words_min_2)
      (map lit_var_c (mt_trail (ms_core Mpost)))).
    { rewrite Ecore. exact H_incl. }
    assert (Hinc_tag : incl (map lit_var_c words_min_2)
      (ms_tagged Mpost)).
    { rewrite Etagged. intros x Hx. apply in_or_app. left.
      exact (H_incl_2 x Hx). }
    assert (Hcert : analyze_clause_cert anz_n anz_F Mpost words_uip).
    { eapply analyze_clause_cert_transport__analyze; eauto. }
    assert (Hcore : analysis_core_equiv M0 Mpost).
    { eapply analysis_core_equiv_trans__analyze; eauto. }
    sep_apply (solver_rep_analyze_at_shape__analyze
      s_pre Mpost reasons levels_ptr trail tags anz_wl).
    Intros.
    Exists cap_min_2 kept_2
      (removed_2 ++ Znth i words_min_2 0 :: nil) words_min_2
      (T_2 ++ lit_var_c (Znth i words_min_2 0) :: fresh) Mpost.
    entailer_with ltac:(lia).
    unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_30 : solver_analyze_entail_wit_30.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mstats_upd anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert anz_n anz_F Mstats_upd words_uip ) as H_analyze_clause_cert.
  bind_fact ( analyze_minimize_loop_inv anz_n Mstats_upd words_uip kept_done removed_done words_done T_done i j ) as
      H_analyze_minimize_loop_inv.
  bind_fact ( Zlength (sublist 0 j words_done) = j ) as H_Zlength.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin words_uip kept removed words_min T i j ) as
      H_analyze_minimize_loop_inv_2.
  assert (Horiglen : Zlength words_min = Zlength words_uip).
  { unfold analyze_minimize_loop_inv in H_analyze_minimize_loop_inv_2. tauto. }
  assert (Hdone : Zlength words_uip <= i) by lia.
  pose proof (analyze_minimize_finish__analyze
    anz_n anz_F anz_A_arr K Mstats_upd anz_focus words_uip kept_done removed_done
    words_done T_done i j H_analysis_cancel_ready H_analyze_clause_cert H_analyze_minimize_loop_inv Hdone) as Hfinish.
  destruct Hfinish as [Hpositive [Hbounded [Hwf [Hnodup Hcert]]]].
  assert (Hcompactcap : Zlength (sublist 0 j words_done) <= cap_done).
  { rewrite H_Zlength. unfold analyze_minimize_loop_inv in H_analyze_minimize_loop_inv. lia. }
  Exists (sublist 0 j words_done) Mstats_upd.
  entailer_with ltac:(lia).
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_analyze partial_solve wits (13 proofs) ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_28_pure : solver_analyze_partial_solve_wit_28_pure.
Proof.
  LLM_pre_process ltac:(lia). split_pures; msat_analyze_cancel_heap_tail_p2.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_29_pure : solver_analyze_partial_solve_wit_29_pure.
Proof.
  LLM_pre_process ltac:(lia). split_pures; msat_analyze_cancel_heap_tail_p2.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_31_pure : solver_analyze_partial_solve_wit_31_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( reason_target_wf anz_n Mcur_2 x c Ccur_2 ) as H_reason_target_wf.
  split_pures.
  all: dump_pre_spatial;
       unfold reason_target_wf, lit_wf_c in H_reason_target_wf;
       unfold msat_true in *;
       destruct H_reason_target_wf as
         [_ [_ [_ [_ [[_ [_ Hwf]] | [co [Hfalse _]]]]]]];
       try lia;
       congruence.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_35_pure : solver_analyze_partial_solve_wit_35_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_35_pure, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  (* The three clause-store positivity facts are extracted ONCE, from a single
     bundled entailment and above the pure split: each `prop_apply_p` re-normalises
     and re-lifts the whole 55-atom precondition, so three separate calls paid that
     traversal three times. *)
  prop_apply_p
    (ms_analyze_db_triple_positive_part2
       (ms_prob Mcur) (ms_learnt Mcur) (ms_binary Mcur) (ms_binary_lits Mcur)).
  Intros_p Hpos.
  destruct Hpos as [Hprob_pos [Hlearnt_pos Hbinary_pos]].
  split_pures.
  - dump_pre_spatial. exact H_analyze_resolution_loop_inv.
  - dump_pre_spatial. exact H_is_tag.
  - dump_pre_spatial.
    unfold msat_false in H_is_tag.
    destruct (analyze_resolution_real_ptr_source__analyze
      anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p H_analyze_resolution_loop_inv H_is_tag)
      as [Hbinary | [co Hin]].
    + rewrite Hbinary. exact Hbinary_pos.
    + unfold msolver_db in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * rewrite Forall_forall in Hprob_pos.
        exact (Hprob_pos (c, co) Hin).
      * rewrite Forall_forall in Hlearnt_pos.
        exact (Hlearnt_pos (c, co) Hin).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_36_pure : solver_analyze_partial_solve_wit_36_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_36_pure, solver_analyze_open_at.
  Unfold.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_37_pure : solver_analyze_partial_solve_wit_37_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_37_pure, solver_analyze_open_at.
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

Lemma proof_of_solver_analyze_partial_solve_wit_38_learnt_pure : solver_analyze_partial_solve_wit_38_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_38_learnt_pure, solver_analyze_open_at.
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

Lemma proof_of_solver_analyze_partial_solve_wit_44_learnt_pure : solver_analyze_partial_solve_wit_44_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_44_learnt_pure, solver_analyze_open_at.
  Unfold.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_45_learnt_pure : solver_analyze_partial_solve_wit_45_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_45_learnt_pure, solver_analyze_open_at.
  Unfold.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_46_learnt_pure : solver_analyze_partial_solve_wit_46_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_46_learnt_pure, solver_analyze_open_at.
  Unfold.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_47_learnt_pure : solver_analyze_partial_solve_wit_47_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_47_learnt_pure, solver_analyze_open_at.
  Unfold.
  msat_analyze_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_56_learnt_pure : solver_analyze_partial_solve_wit_56_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_56_learnt_pure, solver_analyze_open_at.
  LLM_pre_process ltac:(lia). bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  split_pures; msat_analyze_learnt_lit_range_tail_p2 H_Forall anz_n clause_words2 j.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_57_learnt_pure : solver_analyze_partial_solve_wit_57_learnt_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_57_learnt_pure, solver_analyze_open_at.
  LLM_pre_process ltac:(lia). bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  split_pures; msat_analyze_learnt_lit_range_tail_p2 H_Forall anz_n clause_words2 j.
Qed.

(* ===== solver_analyze which_implies wits (3 proofs) ===== *)
Lemma proof_of_solver_analyze_which_implies_wit_42 : solver_analyze_which_implies_wit_42.
Proof.
  aggressive_pre_process.
  all: bind_fact ( Forall (lit_wf_c anz_n) words_compact ) as H_Forall.
  - intros. pose proof (Forall_Znth_elim _ _ words_compact 0 i H_Forall ltac:(lia)) as Hwf.
    replace (i - 0) with i by lia.
    exact (proj2 (lit_var_c_in_range anz_n _ Hwf)).
  - intros. pose proof (Forall_Znth_elim _ _ words_compact 0 i H_Forall ltac:(lia)) as Hwf.
    replace (i - 0) with i by lia.
    exact (proj1 (lit_var_c_in_range anz_n _ Hwf)).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_43 : solver_analyze_which_implies_wit_43.
Proof.
  Unfold. left. intros.
  unfold veci_rep_at.
  prop_apply_p (IntArray.full_Zlength lits len_sw words_sw).
  Intros_p Hlen.
  prop_apply_p (IntArray.undef_seg_valid lits len_sw cap_sw).
  Intros_p Hvalid.
  prop_apply_p (store_int_range (&(learnt # "veci_t" ->ₛ "size")) len_sw).
  Intros_p Hlenrange.
  prop_apply_p (store_int_range (&(learnt # "veci_t" ->ₛ "cap")) cap_sw).
  Intros_p Hcaprange.
  change (-2147483648 <= len_sw <= 2147483647) in Hlenrange.
  change (-2147483648 <= cap_sw <= 2147483647) in Hcaprange.
  pose proof (Zlength_nonneg words_sw) as Hnonneg.
  rewrite Hlen.
  sep_apply_l_atomic (IntArray.full_to_seg lits len_sw words_sw).
  split_pure_spatial.
  - unfold veci_size_addr, veci_cap_addr, veci_ptr_addr. cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_45 : solver_analyze_which_implies_wit_45.
Proof.
  aggressive_pre_process.
  apply solver_rep_analyze_join_levels_at.
Qed.


(* ===== solver_dlevel return wits (1 proofs) ===== *)
Lemma proof_of_solver_dlevel_return_wit_1 : solver_dlevel_return_wit_1.
Proof.
  Unfold.
  right.
  intros lim_cap lim retval PreH1 PreH2 PreH3 PreH4 PreH5.
  bind_fact ( retval = Zlength lim ) as H_retval.
  assert (Hnil : lim = z_nil -> retval = 0).
  { intros H. subst lim. unfold z_nil in H_retval.
    rewrite Zlength_nil in H_retval. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_lit_removable entail wits (12 proofs) ===== *)
Lemma proof_of_solver_lit_removable_entail_wit_6_1 : solver_lit_removable_entail_wit_6_1.
Proof.
  Unfold.
  pre_process_default.
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
  msat_veci_tagged_addr_facts_p2 s_pre.
  msat_veci_stack_addr_facts_p2 s_pre.
  sep_apply_l_atomic (store_int_undef_store_int (&( "v")) retval_8).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "c"))
    (Znth (Znth (Zlength stack_now - 1) stack_now 0)
      (ms_reason_words M0) 0)).
  sep_apply_l_atomic (store_int_undef_store_int (&( "v"))
    (Znth (Zlength stack_now - 1) stack_now 0)).
  sep_apply_l_atomic
    (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr).
  sep_apply_l_atomic
    (store_ptr_undef_store_ptr (&( "levels")) levels_ptr).
  prop_apply_p
    (ptrarray_missing_i_index_range__lit_removable
      reasons_ptr retval_8 0 lrm_n (ms_reason_words M0)).
  Intros_p Hidx. destruct Hidx as [Hidx0 Hidxn].
  try change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply (PtrArray.missing_i_merge_to_full reasons_ptr retval_8 lrm_n
    (Znth retval_8 (ms_reason_words M0) 0) (ms_reason_words M0)
    ltac:(lia)).
  sep_apply (IntArray.missing_i_merge_to_full levels_ptr retval_8 lrm_n
    (Znth retval_8 (mt_levels (ms_core M0)) 0) (mt_levels (ms_core M0))
    ltac:(lia)).
  sep_apply (CharArray.missing_i_merge_to_full tags_ptr retval_8 lrm_n
    (Znth retval_8 tags_now 0) tags_now ltac:(lia)).
  rewrite ?replace_Znth_Znth.
  sep_apply PtrArray.full_to_seg.
  sep_apply IntArray.full_to_seg.
  sep_apply CharArray.full_to_seg.
  destruct (Z_lt_ge_dec top (Zlength tagged_now)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth top tagged_now 0 < lrm_n).
    { unfold analysis_tags_exact in H_analysis_tags_exact.
      destruct H_analysis_tags_exact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists tags_now.
    unfold veci_rep, veci_rep_at. Exists p.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr,
      <- Hstack_size, <- Hstack_cap, <- Hstack_ptr.
    entailer_with ltac:(lia).
  - assert (Htople : top <= Zlength tagged_now).
    { unfold removable_rollback_inv in Hrollback. tauto. }
    assert (Htopeq : top = Zlength tagged_now) by lia.
    Right. Exists tags_now.
    unfold veci_rep, veci_rep_at. Exists p.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr,
      <- Hstack_size, <- Hstack_cap, <- Hstack_ptr.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_6_2 : solver_lit_removable_entail_wit_6_2.
Proof.
  Unfold.
  pre_process_default.
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
  (* Merge the three read-back cells once before choosing the rollback branch.
     The generated literal bounds supply their shared index range. *)
  assert (Hr8 : 0 <= retval_8 < lrm_n).
  { rewrite H_retval_8, H_retval_7. split; [exact H_lit_var_c | exact H_lit_var_c_2]. }
  msat_veci_tagged_addr_facts_p2 s_pre.
  msat_veci_stack_addr_facts_p2 s_pre.
  sep_apply_l_atomic (store_int_undef_store_int (&( "v")) retval_8).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "c"))
    (Znth (Znth (Zlength stack_now - 1) stack_now 0)
      (ms_reason_words M0) 0)).
  sep_apply_l_atomic (store_int_undef_store_int (&( "v"))
    (Znth (Zlength stack_now - 1) stack_now 0)).
  sep_apply_l_atomic
    (store_ptr_undef_store_ptr (&( "reasons")) reasons_ptr).
  sep_apply_l_atomic
    (store_ptr_undef_store_ptr (&( "levels")) levels_ptr).
  try change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply (PtrArray.missing_i_merge_to_full reasons_ptr retval_8 lrm_n
    (Znth retval_8 (ms_reason_words M0) 0) (ms_reason_words M0)
    Hr8).
  sep_apply (IntArray.missing_i_merge_to_full levels_ptr retval_8 lrm_n
    (Znth retval_8 (mt_levels (ms_core M0)) 0) (mt_levels (ms_core M0))
    Hr8).
  sep_apply (CharArray.missing_i_merge_to_full tags_ptr retval_8 lrm_n
    (Znth retval_8 tags_now 0) tags_now Hr8).
  rewrite ?replace_Znth_Znth.
  sep_apply PtrArray.full_to_seg.
  sep_apply IntArray.full_to_seg.
  sep_apply CharArray.full_to_seg.
  destruct (Z_lt_ge_dec top (Zlength tagged_now)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth top tagged_now 0 < lrm_n).
    { unfold analysis_tags_exact in H_analysis_tags_exact.
      destruct H_analysis_tags_exact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists tags_now.
    unfold veci_rep, veci_rep_at. Exists p.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr,
      <- Hstack_size, <- Hstack_cap, <- Hstack_ptr.
    entailer_with ltac:(lia).
  - assert (Htople : top <= Zlength tagged_now).
    { unfold removable_rollback_inv in Hrollback. tauto. }
    assert (Htopeq : top = Zlength tagged_now) by lia.
    Right. Exists tags_now.
    unfold veci_rep, veci_rep_at. Exists p.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr,
      <- Hstack_size, <- Hstack_cap, <- Hstack_ptr.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_7 : solver_lit_removable_entail_wit_7.
Proof.
  Unfold.
  pre_process_default.
  replace (j - 0) with j in * by lia.
  assert (Hstep : removable_rollback_inv lrm_n top (j + 1) (ms_tagged M0)
    (ms_tags M0) tags_now tagged_now
    (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2)).
  { eapply removable_rollback_step__lit_removable; eauto. }
  msat_veci_tagged_addr_facts_p2 s_pre.
  destruct (Z_lt_ge_dec (j + 1) (Zlength tagged_now)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth (j + 1) tagged_now 0 < lrm_n).
    { assert (Hexact : analysis_tags_exact lrm_n tags_now tagged_now).
      { unfold removable_rollback_inv in Hstep. tauto. }
      unfold analysis_tags_exact in Hexact.
      destruct Hexact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2).
    entailer_with ltac:(lia).
    unfold veci_rep_at.
    sep_apply_l_atomic
      (CharArray.missing_i_merge_to_full tags_ptr
        (Znth j tagged_now 0) lrm_n 0 tags_rollback_2).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.full_to_seg tags_ptr lrm_n
          (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2)).
      rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr.
      cancel.
      entailer_with ltac:(lia).
  - assert (Hjle : j + 1 <= Zlength tagged_now).
    { unfold removable_rollback_inv in Hstep. tauto. }
    assert (Hjeq : j + 1 = Zlength tagged_now) by lia.
    Right. Exists (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2).
    entailer_with ltac:(lia).
    unfold veci_rep_at.
    sep_apply_l_atomic
      (CharArray.missing_i_merge_to_full tags_ptr
        (Znth j tagged_now 0) lrm_n 0 tags_rollback_2).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.full_to_seg tags_ptr lrm_n
          (replace_Znth (Znth j tagged_now 0) 0 tags_rollback_2)).
      rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr.
      cancel.
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_8 : solver_lit_removable_entail_wit_8.
Proof.
  Unfold.
  pre_process_default.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now - 1) stack_now 0) (ms_reason_words M0) 0) = msat_false ) as
      H_is_tag.
  bind_fact ( Cnext = lits_denote clause_words ) as H_Cnext.
  bind_fact ( Forall (lit_wf_c lrm_n) clause_words ) as H_Forall.
  bind_fact ( stack_after = sublist 0 (Zlength stack_now - 1) stack_now ) as H_stack_after.
  bind_fact ( stack_now = stack_after +:: Znth (Zlength stack_now - 1) stack_now 0 ) as H_stack_now.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now - 1) stack_now 0) (Znth (Znth (Zlength
      stack_now - 1) stack_now 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( incl stack_now (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now tagged_now stack_now done ) as
      H_removable_dfs_loop_inv.
  replace (retval_5 - 1) with (Zlength stack_now - 1) in * by lia.
  set (v_now := Znth (Zlength stack_now - 1) stack_now 0) in *.
  set (stack_prefix := sublist 0 (Zlength stack_now - 1) stack_now) in *.
  rewrite H_stack_after in H_stack_now.
  assert (Hshape : stack_now = stack_prefix ++ v_now :: nil) by exact H_stack_now.
  assert (Hstack : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_now tagged_now (v_now :: stack_prefix) done).
  { eapply removable_dfs_loop_inv_stack_perm__lit_removable
      with (stack := stack_now).
    - rewrite Hshape.
      pose proof (Permutation_middle stack_prefix nil v_now) as Hperm.
      rewrite app_nil_r in Hperm. exact (Permutation_sym Hperm).
    - exact H_removable_dfs_loop_inv. }
  assert (HCnonempty : 1 <= Zlength Cnext).
  { pose proof H_removable_reason_focus as Htarget.
    unfold removable_reason_focus, reason_target_wf in Htarget.
    destruct Htarget as [Hvrange [Hp [Hpnonzero [Hreason Hkind]]]].
    destruct Hkind as [[Htag [Hpositive Hwf]] |
      [co [Htag [Hbinary [Hin HC]]]]].
    - assert (Hclause_shape : Cnext =
        lit_denote (trail_lit_of (ms_core M0) v_now) ::
        literal_neg
          (lit_denote (tag_lit (Znth v_now (ms_reason_words M0) 0))) :: nil).
      { eapply reason_target_wf_tag_shape__lit_removable.
        + exact H_analysis_cancel_ready.
        + exact H_removable_reason_focus.
        + exact Htag. }
      rewrite Hclause_shape, Zlength_cons, Zlength_cons, Zlength_nil. lia.
    - rewrite HC.
      destruct
        (analysis_cancel_ready_semantic_core__lit_removable
          lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready)
        as [_ [_ [_ [Hdb _]]]].
      destruct (db_wf_obj lrm_n (msolver_db M0)
        (Znth v_now (ms_reason_words M0) 0) co Hdb Hin)
        as [Hlen _].
      unfold denote_obj. rewrite lits_denote_length. lia. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done stack_prefix tags_now tagged_now Cnext v_now
    (Znth v_now (ms_reason_words M0) 0) 1).
  { unfold removable_reason_scan_inv.
    split; [exact Hstack|].
    split; [exact H_removable_reason_focus|].
    split.
    - rewrite H_Cnext, lits_denote_length in HCnonempty.
      rewrite H_Cnext, lits_denote_length.
      split; [lia | exact HCnonempty].
    - split.
      + rewrite H_Cnext. apply lits_denote_wf. exact H_Forall.
      + intros k Hk. lia. }
  pose proof HCnonempty as Hwords_nonempty.
  rewrite H_Cnext, lits_denote_length in Hwords_nonempty.
  assert (Hincl : incl (v_now :: stack_prefix)
    (map lit_var_c (mt_trail (ms_core M0)))).
  { intros x [<- | Hx].
    - apply H_incl. rewrite Hshape. apply in_or_app. right.
      simpl. auto.
    - apply H_incl. rewrite Hshape. apply in_or_app. left. exact Hx. }
  assert (Hmod : Znth v_now (ms_reason_words M0) 0 mod 2 = 0).
  { assert (Heven : Z.even (Znth v_now (ms_reason_words M0) 0) = true).
    { unfold msat_false, is_tag in H_is_tag.
      rewrite <- Z.negb_even in H_is_tag.
      destruct (Z.even (Znth v_now (ms_reason_words M0) 0)) eqn:Heven.
      - reflexivity.
      - simpl in H_is_tag. discriminate. }
    exact (clause_ptr_mod2 _ Heven). }
  Exists stack_cap_now tagged_cap_now done stack_prefix tags_now tagged_now.
  entailer_with ltac:(lia).
  unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr,
    veci_ptr_addr. Exists p. entailer_with ltac:(lia).
  - csimpl; cancel.
  - apply Z.rem_divide; [lia |].
    apply Z.mod_divide; [lia | exact Hmod].
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_9 : solver_lit_removable_entail_wit_9.
Proof.
  Unfold.
  right; intros.
  (* The two range side conditions are left on the call's return value while the
          hypotheses state them at `Znth (i - 0)`; normalise the index in the hypotheses as
          well as in the goal so `lia` sees one atom. *)
  replace (i - 0) with i in * by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_10_1 : solver_lit_removable_entail_wit_10_1.
Proof.
  msat_lit_removable_rollback_p2 Htop Hlits Htags Hscan lrm_n M0 l_pre minl_pre top lits
    tags_scan tagged_scan done_scan stack_scan Cnext v c i retval_3 reasons_ptr levels_ptr retval.
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_10_2 : solver_lit_removable_entail_wit_10_2.
Proof.
  msat_lit_removable_rollback_p2 Htop Hlits Htags Hscan lrm_n M0 l_pre minl_pre top lits
    tags_scan tagged_scan done_scan stack_scan Cnext v c i retval_3 reasons_ptr levels_ptr retval.
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_11 : solver_lit_removable_entail_wit_11.
Proof.
  Unfold.
  pre_process_default.
  replace (j - 0) with j in * by lia.
  assert (Hstep : removable_rollback_inv lrm_n top (j + 1) (ms_tagged M0)
    (ms_tags M0) tags_scan tagged_scan
    (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2)).
  { eapply removable_rollback_step__lit_removable; eauto. }
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_full tags_ptr
      (Znth j tagged_scan 0) lrm_n 0 tags_rollback_2).
  { dump_pre_spatial. lia. }
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2)).
  csimpl.
  destruct (Z_lt_ge_dec (j + 1) (Zlength tagged_scan)) as [Hlt | Hge].
  - assert (Htagvar : 0 <= Znth (j + 1) tagged_scan 0 < lrm_n).
    { assert (Hexact : analysis_tags_exact lrm_n tags_scan tagged_scan).
      { unfold removable_rollback_inv in Hstep. tauto. }
      unfold analysis_tags_exact in Hexact.
      destruct Hexact as [_ [_ [Hbounds _]]].
      eapply Forall_Znth_elim; [exact Hbounds | lia]. }
    Left. Exists (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2).
    entailer_with ltac:(lia).
    cancel.
    entailer_with ltac:(lia).
    csimpl.
    entailer_with ltac:(lia).
  - assert (Hjle : j + 1 <= Zlength tagged_scan).
    { unfold removable_rollback_inv in Hstep. tauto. }
    assert (Hjeq : j + 1 = Zlength tagged_scan) by lia.
    Right. Exists (replace_Znth (Znth j tagged_scan 0) 0 tags_rollback_2).
    entailer_with ltac:(lia).
    cancel.
    entailer_with ltac:(lia).
    csimpl.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_12_1 : solver_lit_removable_entail_wit_12_1.
Proof.
  Unfold.
  pre_process_default.
  bind_fact ( retval_3 = lit_var_c (Znth (i - 0) clause_words 0) ) as H_retval_3.
  bind_fact ( Znth retval_2 tags_scan_2 0 = 0 ) as H_Znth.
  bind_fact ( reason_target_wf lrm_n M0 retval_2 (Znth retval_2 (ms_reason_words M0) 0) Cpush ) as H_reason_target_wf.
  bind_fact ( retval_2 = lit_var_c (Znth (i - 0) clause_words 0) ) as H_retval_2.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( incl (v :: stack_scan_2) (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( In (lit_var_c l_pre) (ms_tagged M0) ) as H_In.
  bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan_2 stack_scan_2 tags_scan_2
      tagged_scan_2 Cnext v c i ) as H_removable_reason_scan_inv.
  bind_fact ( Cnext = lits_denote clause_words ) as H_Cnext.
  replace (i - 0) with i in * by lia.
  assert (Hsame : retval_3 = retval_2) by congruence.
  assert (Hxdef : retval_2 = literal_var (Znth i Cnext (Pos 0))).
  { rewrite H_Cnext. unfold lits_denote.
    rewrite (Znth_map Z literal lit_denote clause_words i 0 (Pos 0)) by lia.
    rewrite lit_var_c_denote. exact H_retval_2. }
  assert (Hneq : literal_var (Znth i Cnext (Pos 0)) <> v).
  { eapply removable_reason_scan_side_neq_untagged__lit_removable;
      [exact H_removable_reason_scan_inv | exact H_In | |].
    - rewrite <- Hxdef. lia.
    - rewrite <- Hxdef. exact H_Znth. }
  assert (Hbelow : assigned_below_current (msolver_view lrm_n M0) retval_2).
  { rewrite Hxdef.
    eapply removable_reason_scan_side_assigned_below__lit_removable;
      [exact H_analysis_cancel_ready | exact H_removable_reason_scan_inv | | exact Hneq].
    rewrite H_Cnext, lits_denote_length. lia. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_scan_2 (stack_scan_2 ++ retval_2 :: nil)
    (replace_Znth retval_2 1 tags_scan_2)
    (tagged_scan_2 ++ retval_2 :: nil) Cnext v c (i + 1)).
  { eapply removable_reason_scan_push_pending__lit_removable
      with (q := Znth retval_2 (ms_reason_words M0) 0) (Cx := Cpush).
    - exact H_removable_reason_scan_inv.
    - exact H_In.
    - rewrite H_Cnext, lits_denote_length. lia.
    - exact Hxdef.
    - lia.
    - exact H_Znth.
    - exact Hbelow.
    - exact H_reason_target_wf. }
  assert (Hincl : incl (v :: stack_scan_2 ++ retval_2 :: nil)
    (map lit_var_c (mt_trail (ms_core M0)))).
  { intros x [<- | Hx].
    - apply H_incl. left. reflexivity.
    - apply in_app_or in Hx. destruct Hx as [Hx | [<- | []]].
      + apply H_incl. right. exact Hx.
      + eapply assigned_below_in_trail__lit_removable.
        exact Hbelow. }
  assert (Htags : analysis_tags_exact lrm_n
    (replace_Znth retval_2 1 tags_scan_2)
    (tagged_scan_2 ++ retval_2 :: nil)).
  { unfold removable_reason_scan_inv in Hscan.
    destruct Hscan as [Hdfs _].
    unfold removable_dfs_loop_inv in Hdfs.
    destruct Hdfs as [fresh [_ [Hexact _]]].
    exact Hexact. }
  subst retval_3.
  Exists cap_prime cap_prime_2 done_scan_2
    (stack_scan_2 ++ retval_2 :: nil)
    (replace_Znth retval_2 1 tags_scan_2)
    (tagged_scan_2 ++ retval_2 :: nil).
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth retval_2 1 tags_scan_2)).
  entailer_with ltac:(lia).
  unfold veci_rep, veci_rep_at.
  repeat rewrite replace_Znth_Znth.
  rewrite Hsame.
  msat_veci_tagged_addr_facts_p2 s_pre.
  msat_veci_stack_addr_facts_p2 s_pre.
  Exists p_prime_2 p_prime.
  rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr,
    <- Hstack_size, <- Hstack_cap, <- Hstack_ptr.
  entailer_with ltac:(lia).
  - apply Zlength_nonneg.
  - match goal with
    | Hcap : Zlength
        (stack_scan_2 +:: lit_var_c (Znth i clause_words 0)) <= cap_prime
      |- _ => rewrite <- Hsame; exact Hcap
    end.
  - apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_12_2 : solver_lit_removable_entail_wit_12_2.
Proof.
  Unfold.
  pre_process_default.
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
  Exists stack_cap_scan_2 tagged_cap_scan_2 done_scan_2 stack_scan_2
    tags_scan_2 tagged_scan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_12_3 : solver_lit_removable_entail_wit_12_3.
Proof.
  Unfold.
  pre_process_default.
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
  assert (Hbelow : assigned_below_current (msolver_view lrm_n M0) retval_2).
  { rewrite Hxdef.
    eapply removable_reason_scan_side_assigned_below__lit_removable;
      [exact H_analysis_cancel_ready | exact H_removable_reason_scan_inv | | exact Hneq].
    rewrite H_Cnext, lits_denote_length. lia. }
  destruct (analysis_cancel_ready_semantic_core__lit_removable
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Htrail Hsemantic].
  assert (Hlevel : level_of (msolver_view lrm_n M0) retval_2 = Some 0).
  { eapply assigned_below_level_word_zero__lit_removable;
      eauto. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_scan_2 stack_scan_2 tags_scan_2 tagged_scan_2
    Cnext v c (i + 1)).
  { eapply removable_reason_scan_advance_level0__lit_removable.
    - exact H_removable_reason_scan_inv.
    - rewrite H_Cnext, lits_denote_length. lia.
    - rewrite <- Hxdef. exact Hlevel. }
  Exists stack_cap_scan_2 tagged_cap_scan_2 done_scan_2 stack_scan_2
    tags_scan_2 tagged_scan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_entail_wit_13_1 : solver_lit_removable_entail_wit_13_1.
Proof.
  Unfold.
  pre_process_default.
  bind_fact ( Znth retval_7 tags_now_2 0 = 0 ) as H_Znth.
  bind_fact ( reason_target_wf lrm_n M0 retval_7 (Znth retval_7 (ms_reason_words M0) 0) Cpush ) as H_reason_target_wf.
  bind_fact ( retval_7 = lit_var_c retval_6 ) as H_retval_7.
  bind_fact ( retval_6 = tag_lit (Znth (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) ) as
      H_retval_6.
  bind_fact ( is_tag (Znth (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) = msat_true ) as
      H_is_tag.
  bind_fact ( stack_after = sublist 0 (Zlength stack_now_2 - 1) stack_now_2 ) as H_stack_after.
  bind_fact ( stack_now_2 = stack_after +:: Znth (Zlength stack_now_2 - 1) stack_now_2 0 ) as H_stack_now_2.
  bind_fact ( removable_reason_focus lrm_n M0 (Znth (Zlength stack_now_2 - 1) stack_now_2 0) (Znth (Znth (Zlength
      stack_now_2 - 1) stack_now_2 0) (ms_reason_words M0) 0) Cnext ) as H_removable_reason_focus.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( incl stack_now_2 (map lit_var_c (mt_trail (ms_core M0))) ) as H_incl.
  bind_fact ( In (lit_var_c l_pre) (ms_tagged M0) ) as H_In.
  bind_fact ( removable_dfs_loop_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) tags_now_2 tagged_now_2 stack_now_2
      done_2 ) as H_removable_dfs_loop_inv.
  replace (retval_4 - 1) with (Zlength stack_now_2 - 1) in * by lia.
  replace (retval_7 - 0) with retval_7 in * by lia.
  set (v_now := Znth (Zlength stack_now_2 - 1) stack_now_2 0) in *.
  set (stack_prefix := sublist 0 (Zlength stack_now_2 - 1) stack_now_2) in *.
  rewrite H_stack_after in H_stack_now_2.
  assert (Hshape_stack : stack_now_2 = stack_prefix ++ v_now :: nil)
    by exact H_stack_now_2.
  assert (Hstack : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) tags_now_2 tagged_now_2 (v_now :: stack_prefix) done_2).
  { eapply removable_dfs_loop_inv_stack_perm__lit_removable
      with (stack := stack_now_2).
    - rewrite Hshape_stack.
      pose proof (Permutation_middle stack_prefix nil v_now) as Hperm.
      rewrite app_nil_r in Hperm. exact (Permutation_sym Hperm).
    - exact H_removable_dfs_loop_inv. }
  assert (Hfocus : reason_target_wf lrm_n M0 v_now
    (Znth v_now (ms_reason_words M0) 0) Cnext) by exact H_removable_reason_focus.
  pose proof
    (reason_target_wf_tag_shape__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus v_now
      (Znth v_now (ms_reason_words M0) 0) Cnext
      H_analysis_cancel_ready Hfocus H_is_tag) as Hshape_reason.
  assert (Hclause_wf : Forall (literal_wf lrm_n) Cnext).
  { rewrite Hshape_reason. constructor.
    - apply lit_denote_wf. apply trail_lit_of_wf. lia.
    - constructor.
      + unfold literal_wf, var_in_range.
        rewrite literal_var_neg, lit_var_c_denote. lia.
      + constructor. }
  assert (Hscan : removable_reason_scan_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) done_2 stack_prefix tags_now_2 tagged_now_2
    Cnext v_now (Znth v_now (ms_reason_words M0) 0) 1).
  { unfold removable_reason_scan_inv.
    split; [exact Hstack|].
    split; [exact H_removable_reason_focus|].
    split; [rewrite Hshape_reason;
      rewrite !Zlength_cons; rewrite Zlength_nil; lia|].
    split; [exact Hclause_wf|].
    intros k Hk. lia. }
  assert (Hnew_dfs : removable_dfs_loop_inv lrm_n M0 l_pre minl_pre
    (ms_tagged M0) (replace_Znth retval_7 1 tags_now_2)
    (tagged_now_2 ++ retval_7 :: nil)
    (stack_prefix ++ retval_7 :: nil) (v_now :: done_2)).
  { eapply removable_dfs_tagged_push__lit_removable
      with (F := lrm_F) (A_arr := lrm_A_arr) (K := lrm_K) (focus := lrm_focus)
        (C := Cnext) (p := Znth v_now (ms_reason_words M0) 0)
        (q := Znth retval_7 (ms_reason_words M0) 0) (Cx := Cpush).
    (* One closing tactic per premise of removable_dfs_tagged_push, in the
       order the lemma states them: cancel-ready, scan invariant, focus
       membership, tag flag, the tag/variable identity, the tagged
       variable's range, the fresh-tag read-back, and the pushed
       target's shape. *)
    - exact H_analysis_cancel_ready.
    - exact Hscan.
    - exact H_In.
    - exact H_is_tag.
    - rewrite H_retval_7, H_retval_6. reflexivity.
    - lia.
    - exact H_Znth.
    - exact H_reason_target_wf. }
  assert (Hnew_incl : incl (stack_prefix ++ retval_7 :: nil)
    (map lit_var_c (mt_trail (ms_core M0)))).
  { intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | [<- | []]].
    - apply H_incl. rewrite Hshape_stack. apply in_or_app. left. exact Hy.
    - apply assigned_below_in_trail__lit_removable with (n := lrm_n).
      unfold removable_dfs_loop_inv in Hnew_dfs.
      destruct Hnew_dfs as [fresh [_ [_ [_ [_ [Hpart [Hassigned _]]]]]]].
      apply Hassigned.
      eapply Permutation_in; [exact Hpart|].
      apply in_or_app. right. apply in_or_app. right.
      simpl. auto. }
  assert (Htags : analysis_tags_exact lrm_n
    (replace_Znth retval_7 1 tags_now_2)
    (tagged_now_2 ++ retval_7 :: nil)).
  { unfold removable_dfs_loop_inv in Hnew_dfs.
    destruct Hnew_dfs as [fresh [_ [Hexact _]]].
    exact Hexact. }
  Exists cap_prime cap_prime_2 (v_now :: done_2)
    (stack_prefix ++ retval_7 :: nil)
    (replace_Znth retval_7 1 tags_now_2)
    (tagged_now_2 ++ retval_7 :: nil).
  (* The same-value writes of the read-back cells stay explicit in the obligation, so
          the three arrays arrive carrying an identity `replace_Znth i (Znth i l 0) l`;
          collapse it before the segment folds below can match. *)
  rewrite !replace_Znth_Znth.
  sep_apply_l_atomic
    (CharArray.full_to_seg tags_ptr lrm_n
      (replace_Znth retval_7 1 tags_now_2)).
  entailer_with ltac:(lia).
  unfold veci_rep, veci_rep_at.
  msat_veci_tagged_addr_facts_p2 s_pre.
  msat_veci_stack_addr_facts_p2 s_pre.
  Exists p_prime_2 p_prime.
  rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr,
    <- Hstack_size, <- Hstack_cap, <- Hstack_ptr.
  (* The popped stack is spelled `stack_after +:: v_now` on the left while the loop
          invariant on the right uses the prefix; identify the two spellings once and reuse
          that identification for the capacity bound at the end. *)
  assert (Hstack_sub :
    sublist 0 (Zlength stack_now_2 - 1) (stack_after +:: v_now) = stack_prefix)
    by (rewrite H_stack_after, <- Hshape_stack; reflexivity).
  rewrite Hstack_sub.
  entailer_with ltac:(int_auto).
  (* Three residual side conditions, closed one per bullet: the two capacity
     bounds are plain list-length facts, the middle one is the popped-stack
     re-spelling identified above. *)
  - apply Zlength_nonneg.
  - rewrite <- Hstack_sub. assumption.
  - apply Zlength_nonneg.
Qed.

(* ===== solver_propagate entail wits (18 proofs) ===== *)
Lemma proof_of_solver_propagate_entail_wit_1 : solver_propagate_entail_wit_1.
Proof.
  unfold solver_propagate_entail_wit_1.
  unfold solver_propagate_open_at, stats_propagations, stats_inspects.
  left; intros.
  pose proof (minisat_propagation_reuse_loop_initial__api_reentry n M0)
    as Hreuse_initial.
  Exists rsn_2 trl_2 M0.
  split_pure_spatial.
  - set_String_name; sepcon_assoc_change; sepcon_cancel; subst_all_strings.
  - split_pures; dump_pre_spatial; try assumption.
    unfold solver_propagation_loop_inv, propagation_caller_frame.
    intuition.
Qed.

Lemma proof_of_solver_propagate_entail_wit_2_1 : solver_propagate_entail_wit_2_1.
Proof.
  unfold solver_propagate_entail_wit_2_1.
  msat_propagate_entail_wit_2_shared_p2
    Hshape Hwm Hwcaps Hzlen Hinv Hcallfr Hqtail Hcf Hseed Hzlen2 Hreuse_loop.
Qed.

Lemma proof_of_solver_propagate_entail_wit_2_2 : solver_propagate_entail_wit_2_2.
Proof.
  unfold solver_propagate_entail_wit_2_2.
  msat_propagate_entail_wit_2_shared_p2
    Hshape Hwm Hwcaps Hzlen Hinv Hcallfr Hqtail Hcf Hseed Hzlen2 Hreuse_loop.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_22_real_satisfied : solver_propagate_entail_wit_22_22_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_22_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_23_real_satisfied : solver_propagate_entail_wit_22_23_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_23_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_22_24_real_satisfied : solver_propagate_entail_wit_22_24_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_22_24_real_satisfied.
  unfold stats_propagations, stats_inspects.
  assert (Hassert_true : (1 : Z) <> 0) by lia.
  msat_real_satisfied_close.
Qed.

Lemma proof_of_solver_propagate_entail_wit_23_unit_success : solver_propagate_entail_wit_23_unit_success.
Proof.
  unfold solver_propagate_entail_wit_23_unit_success.
  unfold stats_propagations, stats_inspects.
  aggressive_pre_process.
  bind_fact ( db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents
      (propagation_normalized_clause watch0 (lit_neg_c p) clause_contents) prob_route learnt_route ) as
      H_db_pair_lits_update.
  bind_fact ( propagation_unit_success_transition n F A_arr K Mscan p watch0 scan_current
      (propagation_normalized_clause watch0 (lit_neg_c p) clause_contents) prob_route learnt_route retained_route
      rest_route Mroute ) as H_propagation_unit_success_transitio.
  bind_fact ( propagation_scan_keep_step source_words retained moved rest watch_memory ii jj scan_current
      retained_route rest_route garbage_route memory_route ) as H_propagation_scan_keep_step.
  bind_fact ( msolver_seed_shadow Mscan ) as H_msolver_seed_shadow.
  bind_fact ( propagation_caller_frame M0 Mscan ) as H_propagation_caller_frame.
  bind_fact ( propagation_scan_frontier Mentry Mscan p ) as H_propagation_scan_frontier.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( confl = 0 ) as H_confl.
  bind_fact ( candidate_post_memory = watch_memory ) as H_candidate_post_memory.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  unfold enqueue_post_at.
  Intros qtail_after assigns_after levels_after reasons_after trail_after.
  unfold enqueue_state_at.
  Intros rsn_route trl_route.
  rename H into Henq.
  unfold propagation_unit_success_transition in H_propagation_unit_success_transitio.
  cbn in H_propagation_unit_success_transitio.
  destruct H_propagation_unit_success_transitio as [HMroute Hsem].
  pose proof HMroute as HMroute_original.
  unfold propagation_scan_keep_step in H_propagation_scan_keep_step.
  destruct H_propagation_scan_keep_step as [Hrest [Hretained [Hmemory Hphysical]]].
  assert (Hphysical_route : propagation_watch_scan_physical source_words
      retained_route moved rest_route garbage_route memory_route
      (ii + 1) (jj + 1)) by exact Hphysical.
  assert (Hmemory_length : Zlength memory_route = Zlength source_words).
  { unfold propagation_watch_scan_physical in Hphysical_route. intuition. }
  assert (Hlogical : logical_words = retained_route ++ rest_route).
  { rewrite H_logical_words, Hretained, Hrest. rewrite <- app_assoc. reflexivity. }
  assert (Hsem_confl : solver_propagation_scan_semantics n F A_arr K
      Mroute p confl retained_route rest_route).
  { rewrite H_confl. exact Hsem. }
  assert (Hreuse_confl : minisat_propagation_reuse_scan M0 Mroute p confl rest_route).
  { rewrite H_confl. assumption. }
  (* Shape and trail well-formedness of both solvers come from the same live
     scan-semantics projection. *)
  destruct (msat_propagate_scan_live_core_p2 n F A_arr K Mroute p
    retained_route rest_route Hsem) as [Hshape_route _].
  destruct (msat_propagate_scan_live_core_p2 n F A_arr K Mscan p retained rest
    H_solver_propagation_scan_semantics) as [Hshape_scan Hwf_scan].
  assert (Htrail_len : Zlength (mt_trail (ms_core Mscan)) = ms_qtail Mscan)
    by (unfold solver_shape in Hshape_scan; intuition).
  unfold enqueue_transition in Henq.
  destruct Henq as [Hsame | [Hconflict | Hfresh]].
  - destruct Hsame as
      [Hassigned [_ [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]].
    assert (Hnonzero :
      Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <> 0)
      by (pose proof (lit_sig_nonzero watch0); congruence).
    assert (Htest :
      (Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 =? 0)%Z
      = false) by (apply Z.eqb_neq; exact Hnonzero).
    msat_propagate_enqueue_route_shape_p2 Htest HMroute assigns_after
      levels_after reasons_after trail_after qtail_after.
    assert (Hfrontier_route : propagation_scan_frontier Mentry Mroute p)
      by (rewrite HMroute;
        unfold propagation_scan_frontier in H_propagation_scan_frontier |- *;
        cbn; exact H_propagation_scan_frontier).
    msat_propagate_unit_route_facts_p2 HMroute HMroute_original
      H_msolver_seed_shadow H_propagation_caller_frame H_db_pair_lits_update
      Mroute Mscan M0 s_pre.
    Left.
    Exists trl_route rsn_route prop_count simp_count
      scan_caps_pre scan_wcap scan_caps_post scan_wm_pre scan_wm_post
      logical_words source_words moved garbage_route memory_route
      (ii + 1) (jj + 1) retained_route rest_route Mentry.
    Exists Mroute levels_entry.
    split_pure_spatial.
    msat_propagate_unit_scan_refold_p2 H_candidate_post_memory Hmemory
      Hbinary Hframe HMroute prop_count s_pre Mscan.
    msat_propagate_unit_pure_close_p2 Hshape_route Hseed_route Hcaller_route
      Hfrontier_route Hsem_confl Hphysical_route Hlogical Hmemory_length
      HMroute.
  - destruct Hconflict as [_ [_ [Hret _]]]. lia.
  - destruct Hfresh as
      [Hzero [_ [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]].
    assert (Htest :
      (Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 =? 0)%Z
      = true) by (apply Z.eqb_eq; exact Hzero).
    assert (Hfrontier_route : propagation_scan_frontier Mentry Mroute p)
      by (eapply msat_propagate_scan_frontier_push_p2;
        [ exact Hwf_scan | exact Htrail_len | exact Hzero
        | exact HMroute_original | exact H_propagation_scan_frontier ]).
    msat_propagate_enqueue_route_shape_p2 Htest HMroute assigns_after
      levels_after reasons_after trail_after qtail_after.
    msat_propagate_unit_route_facts_p2 HMroute HMroute_original
      H_msolver_seed_shadow H_propagation_caller_frame H_db_pair_lits_update
      Mroute Mscan M0 s_pre.
    Left.
    Exists trl_route rsn_route prop_count simp_count
      scan_caps_pre scan_wcap scan_caps_post scan_wm_pre scan_wm_post
      logical_words source_words moved garbage_route memory_route
      (ii + 1) (jj + 1) retained_route rest_route Mentry.
    Exists Mroute levels_entry.
    split_pure_spatial.
    msat_propagate_unit_scan_refold_p2 H_candidate_post_memory Hmemory
      Hbinary Hframe HMroute prop_count s_pre Mscan.
    msat_propagate_unit_pure_close_p2 Hshape_route Hseed_route Hcaller_route
      Hfrontier_route Hsem_confl Hphysical_route Hlogical Hmemory_length
      HMroute.
Qed.

Lemma proof_of_solver_propagate_entail_wit_24_scan_same : solver_propagate_entail_wit_24_scan_same.
Proof.
  unfold solver_propagate_entail_wit_24_scan_same.
  unfold stats_propagations.
  Unfold.
  intros.
  bind_fact ( stop = lits + Zlength clause_contents * sizeof ( INT ) ) as H_stop.
  bind_fact ( k = lits + offset * sizeof ( INT ) ) as H_k.
  exfalso.
  rewrite sizeof_int in H_stop, H_k.
  lia.
Qed.

Lemma proof_of_solver_propagate_entail_wit_25_real_migrated : solver_propagate_entail_wit_25_real_migrated.
Proof.
  unfold solver_propagate_entail_wit_25_real_migrated.
  unfold stats_propagations.
  aggressive_pre_process.
  bind_fact (minisat_propagation_reuse_scan M0 Mroute p 0 rest_route)
    as Hreuse_route.
  bind_fact ( db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents
      (propagation_migrated_clause watch0 (Znth (offset - 2) (replace_Znth (offset - 2) candidate (sublist 2
      (Zlength clause_contents) clause_contents)) 0) (lit_neg_c p) offset clause_contents) prob_route learnt_route )
      as H_db_pair_lits_update.
  bind_fact ( propagation_real_migrated_exit_carrier n F A_arr K M0 Mentry Mscan Mroute p prob_route learnt_route
      scan_wm_pre scan_wm_post scan_caps_pre scan_caps_post scan_wcap destination_cap (Znth (offset - 2)
      (replace_Znth (offset - 2) candidate (sublist 2 (Zlength clause_contents) clause_contents)) 0) scan_current
      source_words retained moved rest watch_memory ii jj moved_route rest_route garbage_route (replace_Znth ii
      (Znth ii candidate_post_memory 0) candidate_post_memory) simp_count prop_count ) as
      H_propagation_real_migrated_exit_car.
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  bind_fact ( confl = 0 ) as H_confl.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( candidate_post_memory = watch_memory ) as H_candidate_post_memory.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
  set (new_pre_words := propagation_split_pre_words
    (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
    (wlists_split_target_words
      (Zlength scan_wm_pre) (lit_neg_c candidate)
      scan_wm_pre scan_wm_post ++ (scan_current :: nil))).
  set (new_post_words := propagation_split_post_words
    (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_post
    (wlists_split_target_words
      (Zlength scan_wm_pre) (lit_neg_c candidate)
      scan_wm_pre scan_wm_post ++ (scan_current :: nil))).
  set (new_pre_caps := propagation_split_pre_caps
    (Zlength scan_wm_pre) (lit_neg_c candidate)
    scan_caps_pre destination_cap).
  set (new_post_caps := propagation_split_post_caps
    (Zlength scan_wm_pre) (lit_neg_c candidate)
    scan_caps_post destination_cap).
  assert (Hcandidate_route :
      Znth (offset - 2)
        (replace_Znth (offset - 2) candidate
          (sublist 2 (Zlength clause_contents) clause_contents)) 0 =
      candidate).
  { apply Znth_replace_Znth_Same.
    rewrite Zlength_sublist by
      (pose proof (Zlength_nonneg clause_contents); lia).
    lia. }
  rewrite Hcandidate_route in H_propagation_real_migrated_exit_car.
  unfold propagation_real_migrated_exit_carrier in H_propagation_real_migrated_exit_car.
  destruct H_propagation_real_migrated_exit_car as [HMroute [Htransition [Hstep [Hshape [Hseed
    [Hframe_route [Hfrontier [Hsem [Hsimp [Hprop [Hmemory
    [Hphysical [Hwm [Hcaps [Hwmlen Hcapslen]]]]]]]]]]]]]]].
  assert (Hwmlen_new : Zlength new_pre_words = p).
  { unfold new_pre_words. exact Hwmlen. }
  assert (Hcapslen_new : Zlength new_pre_caps = p).
  { unfold new_pre_caps. exact Hcapslen. }
  assert (Hwm_new : ms_wm Mroute =
      new_pre_words ++ (retained ++ rest_route) :: new_post_words).
  { unfold new_pre_words, new_post_words. exact Hwm. }
  assert (Hcaps_new : ms_wcaps Mroute =
      new_pre_caps ++ scan_wcap :: new_post_caps).
  { unfold new_pre_caps, new_post_caps. exact Hcaps. }
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
  (* The LHS spells the moved watch as a read-back from the (self-)replaced watch
          memory rather than as `scan_current`; this identifies the two. *)
  assert (Hcur2 : Znth (Zlength raw_prefix)
      (replace_Znth (Zlength raw_prefix)
         (Znth (Zlength raw_prefix) watch_memory 0) watch_memory) 0
      = scan_current).
  { rewrite Znth_replace_Znth_Same by
      (rewrite H_watch_memory, Zlength_app, Zlength_cons;
       pose proof (Zlength_nonneg raw_prefix);
       pose proof (Zlength_nonneg raw_suffix); lia).
    rewrite H_Zlength, <- H_candidate_post_memory. exact H_Znth. }
  Left.
  Exists trl_scan rsn_scan prop_count simp_count
    new_pre_caps scan_wcap new_post_caps new_pre_words new_post_words
    (retained ++ rest_route) source_words moved_route garbage_route
    (replace_Znth ii (Znth ii candidate_post_memory 0)
      candidate_post_memory)
    (ii + 1) jj retained rest_route Mentry.
  Exists Mroute levels_entry.
  split_pure_spatial.
  - fold new_pre_words new_post_words new_pre_caps new_post_caps.
    (* The LHS carrier arguments arrive re-spelled: the raw clause read for `candidate`,
              the watch read-back for `scan_current`, and `p` for `Zlength scan_wm_pre`.
              Restore the carrier's spelling before cancelling -- QCP cancellation is syntactic. *)
    try rewrite Hcur2.
    try rewrite <- H_candidate.
    rewrite Hwmlen_new.
    try rewrite <- H_Zlength_2.
    fold new_pre_words new_post_words new_pre_caps new_post_caps.
    unfold solver_propagation_scan_core_at.
    rewrite Hbinary, Hframe, HMroute.
    unfold msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update.
    cbn. unfold PtrArray.seg, stats_propagate_scan.
    set_String_name. sepcon_assoc_change. sepcon_cancel.
    subst_all_strings.
    unfold Znth; cbn; csimpl.
    intros m Hm. exact Hm.
  - split_pures; dump_pre_spatial.
    (* Preserve the named semantic packages. The remaining goals are field
       read-backs or arithmetic bounds of the explicit route update. *)
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
            cbn [msolver_propagation_db_wmap_update
              msolver_propagation_overlay msolver_propagation_update];
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

Lemma proof_of_solver_propagate_entail_wit_26_1_binary_keep : solver_propagate_entail_wit_26_1_binary_keep.
Proof.
  unfold solver_propagate_entail_wit_26_1_binary_keep.
  unfold stats_propagations, stats_inspects.
  msat_propagate_next_join_p2 H_lvl_next lvl_next levels_entry trl_next
    rsn_next prop_count_next simp_count_next next_caps_pre next_wcap
    next_caps_post next_wm_pre next_wm_post logical_next source_words_next
    moved_next garbage_next memory_next ii_next jj_next retained_next
    rest_next Mentry_next Mnext Left.
Qed.

Lemma proof_of_solver_propagate_entail_wit_26_2_binary_keep : solver_propagate_entail_wit_26_2_binary_keep.
Proof.
  unfold solver_propagate_entail_wit_26_2_binary_keep.
  unfold stats_propagations, stats_inspects.
  msat_propagate_next_join_p2 H_lvl_next lvl_next levels_entry trl_next
    rsn_next simp_count_next prop_count_next next_caps_pre next_wcap
    next_caps_post next_wm_pre next_wm_post logical_next source_words_next
    moved_next garbage_next memory_next ii_next jj_next retained_next
    rest_next Mentry_next Mnext Right.
Qed.

Lemma proof_of_solver_propagate_entail_wit_27_1_real_satisfied : solver_propagate_entail_wit_27_1_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_27_1_real_satisfied.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_26_1_binary_keep.
Qed.

Lemma proof_of_solver_propagate_entail_wit_27_2_real_satisfied : solver_propagate_entail_wit_27_2_real_satisfied.
Proof.
  unfold solver_propagate_entail_wit_27_2_real_satisfied.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_26_2_binary_keep.
Qed.

Lemma proof_of_solver_propagate_entail_wit_28_1_unit_success : solver_propagate_entail_wit_28_1_unit_success.
Proof.
  unfold solver_propagate_entail_wit_28_1_unit_success.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_26_1_binary_keep.
Qed.

Lemma proof_of_solver_propagate_entail_wit_28_2_unit_success : solver_propagate_entail_wit_28_2_unit_success.
Proof.
  unfold solver_propagate_entail_wit_28_2_unit_success.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_26_2_binary_keep.
Qed.

Lemma proof_of_solver_propagate_entail_wit_29_1_scan_same : solver_propagate_entail_wit_29_1_scan_same.
Proof.
  unfold solver_propagate_entail_wit_29_1_scan_same.
  unfold stats_propagations, stats_inspects.
  exact proof_of_solver_propagate_entail_wit_26_1_binary_keep.
Qed.

Lemma proof_of_solver_propagate_entail_wit_29_2_scan_same : solver_propagate_entail_wit_29_2_scan_same.
Proof.
  unfold solver_propagate_entail_wit_29_2_scan_same.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_26_2_binary_keep.
Qed.

Lemma proof_of_solver_propagate_entail_wit_30_1_real_migrated : solver_propagate_entail_wit_30_1_real_migrated.
Proof.
  unfold solver_propagate_entail_wit_30_1_real_migrated.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_26_1_binary_keep.
Qed.

(* ===== solver_propagate safety wits (3 proofs) ===== *)
Lemma proof_of_solver_propagate_safety_wit_213_scan_same : solver_propagate_safety_wit_213_scan_same.
Proof.
  unfold solver_propagate_safety_wit_213_scan_same.
  unfold stats_propagations.
  msat_propagate_safety_signed_range_p2 retval.
Qed.

Lemma proof_of_solver_propagate_safety_wit_214_scan_same : solver_propagate_safety_wit_214_scan_same.
Proof.
  unfold solver_propagate_safety_wit_214_scan_same.
  unfold stats_propagations.
  msat_propagate_safety_signed_range_p2 retval.
Qed.

Lemma proof_of_solver_propagate_safety_wit_222_capacity_copy : solver_propagate_safety_wit_222_capacity_copy.
Proof.
  aggressive_pre_process;
    dump_pre_spatial;
    unfold propagation_scan_open, solver_shape in PreH13;
    lia.
Qed.

(* ===== solver_propagate which_implies wits (17 proofs) ===== *)
Lemma proof_of_solver_propagate_which_implies_wit_2 : solver_propagate_which_implies_wit_2.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( solver_propagation_loop_inv n F A_arr K M0 M1 cf ) as H_solver_propagation_loop_inv.
  unfold solver_propagation_loop_inv in H_solver_propagation_loop_inv.
  destruct H_solver_propagation_loop_inv as [Hframe [[_ Hinv] | [Hconflict _]]].
  - entailer_with ltac:(lia).
  - lia.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_3 : solver_propagate_which_implies_wit_3.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  bind_fact ( p = Znth (mt_qhead (ms_core M0)) (mt_trail (ms_core M0)) 0 ) as H_p.
  destruct H_solver_propagation_inv as [_ Hprop].
  destruct K as [A_inst | A_proc].
  - destruct Hprop as [Hweak _ _ _ _].
    pose proof (msw_trail_wf Hweak) as Hwf.
    pose proof (msw_shape Hweak) as Hshape.
    assert (Hidx :
      0 <= mt_qhead (ms_core M0) < Zlength (mt_trail (ms_core M0))).
    { unfold solver_shape in Hshape. lia. }
    pose proof (Forall_Znth_elim _ _ _ 0 _ (mtw_trail_lits Hwf) Hidx)
      as Hlit.
    rewrite <- H_p in Hlit.
    unfold lit_wf_c in Hlit.
    unfold solver_wlists_handle.
    entailer_with ltac:(lia).
  - destruct Hprop as [Hweak _ _ _ _].
    pose proof (msa_trail_wf Hweak) as Hwf.
    pose proof (msa_shape Hweak) as Hshape.
    assert (Hidx :
      0 <= mt_qhead (ms_core M0) < Zlength (mt_trail (ms_core M0))).
    { unfold solver_shape in Hshape. lia. }
    pose proof (Forall_Znth_elim _ _ _ 0 _ (mtw_trail_lits Hwf) Hidx)
      as Hlit.
    rewrite <- H_p in Hlit.
    unfold lit_wf_c in Hlit.
    unfold solver_wlists_handle.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_4 : solver_propagate_which_implies_wit_4.
Proof.
  Unfold.
  left.
  intros.
  unfold solver_wlists_handle.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_5 : solver_propagate_which_implies_wit_5.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( ws = vecp_slot wlists_entry p ) as H_ws.
  pose proof (wlists_rep_from_split_at__clause_new wlists_entry) as Hsplit.
  unfold wlists_rep.
  apply coq_prop_andp_left. intros [Hwm Hcaps].
  assert (Hpwm : 0 <= p < Zlength (ms_wm M0)) by lia.
  assert (Hpcaps : 0 <= p < Zlength (ms_wcaps M0)) by lia.
  pose proof (list_Znth_split (@nil Z) (ms_wm M0) p Hpwm) as Hwm_split.
  pose proof (list_Znth_split 1 (ms_wcaps M0) p Hpcaps) as Hcaps_split.
  rewrite Hwm_split at 1.
  rewrite Hcaps_split at 1.
  unfold wlists_focus_at.
  Exists (sublist 0 p (ms_wm M0)) (Znth p (ms_wm M0) nil)
    (sublist (p + 1) (Zlength (ms_wm M0)) (ms_wm M0))
    (sublist 0 p (ms_wcaps M0)) (Znth p (ms_wcaps M0) 1)
    (sublist (p + 1) (Zlength (ms_wcaps M0)) (ms_wcaps M0)).
  unfold wlists_focus_rep.
  sep_apply (Hsplit
    0 (sublist 0 p (ms_wm M0)) (Znth p (ms_wm M0) nil)
    (sublist (p + 1) (Zlength (ms_wm M0)) (ms_wm M0))
    (sublist 0 p (ms_wcaps M0)) (Znth p (ms_wcaps M0) 1)
    (sublist (p + 1) (Zlength (ms_wcaps M0)) (ms_wcaps M0))
    ltac:(rewrite !Zlength_sublist by lia; lia)).
  rewrite !Zlength_sublist by lia.
  unfold vecp_slot in H_ws.
  unfold vecp_slot.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_6 : solver_propagate_which_implies_wit_6.
Proof.
  Unfold.
  left.
  intros.
  unfold wlists_focus_at.
  Intros wm_pre words wm_post caps_pre wcap caps_post.
  destruct H as [Hwm [Hcaps [Hpre [Hcapspre Hws]]]].
  Exists caps_pre wcap caps_post wm_pre words wm_post.
  unfold wlists_focus_rep, wlists_source_hole_handle,
    solver_wlists_handle.
  rewrite Hpre, Hws.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_7 : solver_propagate_which_implies_wit_7.
Proof.
  Unfold.
  right. intros.
  subst.
  reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_9 : solver_propagate_which_implies_wit_9.
Proof.
  Unfold.
  intros.
  prop_apply (PtrArray.full_Zlength begin (Zlength source_words) watch_memory).
  Intros.
  pose proof (list_Znth_split 0 watch_memory ii ltac:(lia)) as Hsplit.
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
    rewrite Hsplit at 1.
    sep_apply (Hdecomp begin 0 (Zlength source_words)
      (sublist 0 ii watch_memory) (Znth ii watch_memory 0)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      ltac:(rewrite Zlength_sublist by lia; lia)).
    rewrite !Zlength_sublist by lia.
    replace (0 + (ii - 0)) with ii by lia.
    replace (ii + 1) with (0 + ii + 1) by lia.
    PtrArray.ArraySimplify.
    prop_apply (valid_store_ptr
      (begin + (0 + ii) * sizeof(PTR)) (Znth ii watch_memory 0)).
    Intros.
    (* valid_store_ptr yields valid_ptr_value v, i.e.
       0 <= v <= addr_max_unsigned; unfold it, since micromega cannot
       see inside the definition and the range side-condition would
       otherwise stay open. *)
    unfold valid_ptr_value in *.
    entailer_with ltac:(lia).
  - Left.
    Exists (sublist 0 ii watch_memory)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      (Znth ii watch_memory 0).
    unfold propagation_ptr_segment.
    sep_apply (PtrArray.full_to_seg begin (Zlength source_words) watch_memory).
    rewrite Hsplit at 1.
    sep_apply (Hdecomp begin 0 (Zlength source_words)
      (sublist 0 ii watch_memory) (Znth ii watch_memory 0)
      (sublist (ii + 1) (Zlength watch_memory) watch_memory)
      ltac:(rewrite Zlength_sublist by lia; lia)).
    rewrite !Zlength_sublist by lia.
    replace (0 + (ii - 0)) with ii by lia.
    replace (ii + 1) with (0 + ii + 1) by lia.
    PtrArray.ArraySimplify.
    prop_apply (valid_store_ptr
      (begin + (0 + ii) * sizeof(PTR)) (Znth ii watch_memory 0)).
    Intros.
    (* valid_store_ptr yields valid_ptr_value v, i.e.
       0 <= v <= addr_max_unsigned; unfold it, since micromega cannot
       see inside the definition and the range side-condition would
       otherwise stay open. *)
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
    msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_10 : solver_propagate_which_implies_wit_10.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  assert (Hjj : jj = ii) by lia.
  subst jj.
  assert (Hreplace : replace_Znth ii scan_current watch_memory = watch_memory).
  {
    rewrite <- H_raw_prefix.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (ii - Zlength raw_prefix) with 0 by lia.
    reflexivity.
  }
  rewrite Hreplace.
  rewrite <- H_raw_prefix.
  unfold propagation_ptr_segment.
  prop_apply (PtrArray.seg_valid begin 0 ii raw_prefix).
  Intros.
  prop_apply (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    raw_prefix (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words) (raw_prefix ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  (* The stride cancels for any pointer width
     (0 * n = 0), so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  replace ((raw_prefix ++ scan_current :: nil) ++ raw_suffix) with
    (raw_prefix ++ scan_current :: raw_suffix) by
    (rewrite <- app_assoc; reflexivity).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_11 : solver_propagate_which_implies_wit_11.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  pose proof (list_Znth_split 0 raw_prefix jj ltac:(lia)) as Hsplit.
  assert (Hreplace_prefix :
    replace_Znth jj scan_current raw_prefix =
      sublist 0 jj raw_prefix ++
        scan_current :: sublist (jj + 1) ii raw_prefix).
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
    rewrite H_Zlength.
    reflexivity.
  }
  rewrite <- H_raw_prefix.
  rewrite replace_Znth_app_l by lia.
  rewrite Hreplace_prefix.
  unfold propagation_ptr_segment.
  prop_apply (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin jj scan_current).
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj raw_prefix) (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
    (sublist 0 jj raw_prefix ++ scan_current :: nil)
    (sublist (jj + 1) ii raw_prefix) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    ((sublist 0 jj raw_prefix ++ scan_current :: nil) ++
      sublist (jj + 1) ii raw_prefix)
    (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (((sublist 0 jj raw_prefix ++ scan_current :: nil) ++
      sublist (jj + 1) ii raw_prefix) ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  (* The stride cancels for any pointer width
     (0 * n = 0), so this rewrite is arch-blind. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite <- !app_assoc.
  simpl.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_13 : solver_propagate_which_implies_wit_13.
Proof.
  Unfold.
  right.
  intros.
  subst i.
  sep_apply (PtrArray.full_split_to_missing_i begin ii
    (Zlength source_words) tagged_memory 0 ltac:(lia)).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_14 : solver_propagate_which_implies_wit_14.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( enqueue_input (ms_size Mscan) (tag_lit scan_current) (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan) (mt_trail (ms_core Mscan)) ) as
      H_enqueue_input.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as
    [_ [_ [Hassigns [Hlevels [Hreasons [Htrail [Hqtail _]]]]]]].
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_29 : solver_propagate_which_implies_wit_29.
Proof.
  exact proof_of_solver_propagate_which_implies_wit_10.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_30 : solver_propagate_which_implies_wit_30.
Proof.
  exact proof_of_solver_propagate_which_implies_wit_11.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_31 : solver_propagate_which_implies_wit_31.
Proof.
  Unfold.
  left; intros.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_entry.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( clause_lits_pointer scan_current lits ) as H_clause_lits_pointer.
  bind_fact ( 3 <= Zlength clause_contents ) as H_Zlength.
  bind_fact ( real_watch_pair (Zlength scan_wm_pre) clause_contents ) as H_real_watch_pair.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  bind_fact ( watch0_2 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0_2.
  bind_fact ( sig = 1 - 2 * lit_sign_c watch0_2 ) as H_sig.
  bind_fact ( Znth (lit_var_c watch0_2) (mt_assigns (ms_core Mscan)) 0 = sig ) as H_Znth.
  destruct H_solver_propagation_scan_semantics as [Hlive | Hdead].
  2: { destruct Hdead as [Hnz _]; lia. }
  destruct Hlive as [_ [Hweak [Hprop [Hheapready [Hheapcovers
    [Hreasonless [Hlevel [Hp [Hprocessed [Hfrontier Hscan]]]]]]]]]].
  rewrite H_rest in Hscan, Hreuse_entry.
  assert (Htrail_wf : mtrail_wf n (ms_core Mscan)).
  { destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak)
      as (_ & _ & _ & _ & Htrail). exact Htrail. }
  pose proof (level_of_msolver_view_levels__analyze n Mscan (lit_var_c p)
    (Zlength (mt_lim (ms_core Mscan))) Htrail_wf Hlevel) as Hfocus_cell.
  assert (Hother_true : lit_true (mt_assigns (ms_core Mscan)) watch0_2).
  { unfold lit_true. rewrite H_Znth, H_sig.
    unfold lit_sig, lit_sign_c. destruct (Z.odd watch0_2); reflexivity. }
  rewrite H_Zlength_2 in H_real_watch_pair.
  (* db_wf projected by solver_propagation_weak_core_facts__propagate instead
     of a hand destruct of solver_propagation_weak. *)
  assert (Hdbwf : db_wf n (msolver_db Mscan))
    by (destruct (solver_propagation_weak_core_facts__propagate
          n F A_arr K Mscan Hweak) as [_ [_ [Hdb _]]]; exact Hdb).
  destruct (msat_propagate_scan_keep_step_p2 source_words retained moved rest
    garbage watch_memory ii jj scan_current raw_suffix
    H_propagation_watch_scan_physical H_rest) as [garbage_route Hkeep].
  unfold clause_db_pair_frame. Intros is_learnt.
  unfold clause_db_pair_remainder. Split.
  - Intros co pre post. coq_prop_lift.
    destruct H as [Hprob [Hlits Hlearnt]].
    assert (Hin : In (scan_current, co) (msolver_db Mscan)).
    { unfold msolver_db. apply in_or_app. left. rewrite Hprob.
      apply in_or_app. right. simpl. auto. }
    pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin)
      as Hobj.
    unfold obj_wf in Hobj. rewrite Hlits in Hobj.
    destruct Hobj as [Hlen _].
    destruct clause_contents as [|a0 tail0]; cbn in Hlen; [lia|].
    destruct tail0 as [|a1 tail]; cbn in Hlen; [lia|].
    assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail)
      = tail) by (apply msat_sublist_two_tail_p2).
    set (new_lits := propagation_normalized_clause watch0_2 false_lit
      (a0 :: a1 :: tail)).
    set (co_new := clause_obj_with_lits co new_lits).
    set (prob_route := pre ++ (scan_current, co_new) :: post).
    set (learnt_route := ms_learnt Mscan).
    set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
      learnt_route (ms_wm Mscan) (ms_wcaps Mscan)).
    assert (Hupdate : db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan)
        scan_current (a0 :: a1 :: tail) new_lits prob_route learnt_route).
    { left. exists co, pre, post. repeat split; try assumption;
        try reflexivity. }
    assert (Hdb : msolver_db Mscan =
        pre ++ (scan_current, co) :: (post ++ ms_learnt Mscan)).
    { unfold msolver_db. rewrite Hprob, <- app_assoc. reflexivity. }
    assert (Hdb2 : prob_route ++ learnt_route =
        pre ++ (scan_current, co_new) :: (post ++ ms_learnt Mscan)).
    { unfold prob_route, learnt_route. rewrite <- app_assoc. reflexivity. }
    destruct (msat_propagate_clause_watch_facts_p2 n Mscan p scan_current co
      a0 a1 tail new_lits co_new false_lit watch0_2 sig Hdbwf Hin Hlits
      H_Zlength H_real_watch_pair H_watch0_2 H_false_lit H_sig H_Znth Hp
      Hprocessed ltac:(reflexivity) ltac:(reflexivity)) as
      [Hperm [Hentryold [Hentrynew [Honewsafe
        [Hentryperm [Hswap Hhead]]]]]].
    pose proof (msat_propagate_route_facts_p2 n F A_arr K Mscan Mroute p
      scan_current co co_new a0 a1 tail new_lits prob_route learnt_route
      pre (post ++ ms_learnt Mscan) retained raw_suffix Hdb Hdb2 Hupdate
      ltac:(reflexivity) Hdbwf Hin Hperm Hentryold Hentrynew Honewsafe
      Hentryperm Hswap Hhead Hweak Hprop Hheapready Hheapcovers Hreasonless
      Hlevel Hp Hprocessed Hfrontier Hscan) as Htransition.
    assert (Hcases : (a0 = lit_neg_c p /\ watch0_2 = a1) \/
      (a1 = lit_neg_c p /\ watch0_2 = a0)).
    { pose proof H_real_watch_pair as Hpair. pose proof H_watch0_2 as Hsum.
      change (a0 = lit_neg_c p \/ a1 = lit_neg_c p) in Hpair.
      change (watch0_2 + false_lit = a0 + a1) in Hsum.
      rewrite H_false_lit in Hsum. destruct Hpair; [left|right]; split; lia. }
    assert (Hreal : is_tag scan_current = false).
    { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan) scan_current co Hdbwf Hin). }
    assert (Hdbnew : db_wf n (prob_route ++ learnt_route)).
    { pose proof (proj2 Htransition) as Hsem_new.
      destruct Hsem_new as [Hlive_new|[Hnonzero _]]; [|contradiction].
      destruct Hlive_new as (_ & Hweak_new & _).
      destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mroute Hweak_new)
        as (_ & _ & Hdb_new & _). exact Hdb_new. }
    assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mroute p 0 raw_suffix).
    { unfold Mroute.
      eapply minisat_propagation_reuse_real_satisfied__api_reentry;
        [exact Hdbnew|exact Htrail_wf| |exact Hcases|exact Hreal|
         exact Hfocus_cell|exact Hother_true|exact Hreuse_entry].
      unfold new_lits in Hupdate. rewrite H_false_lit in Hupdate. exact Hupdate. }
    Exists garbage_route (replace_Znth jj scan_current watch_memory)
      Mroute raw_suffix (retained ++ scan_current :: nil) watch0_2
      prob_route learnt_route.
    split_pure_spatial.
    + unfold prob_route.
      msat_propagate_db_entry_spatial_p2 pre post scan_current co_new
        new_lits Htail Hlearnt H_clause_lits_pointer lits tail.
    + split_pures; apply derivable1s_coq_prop_r;
        try exact Hupdate; try exact Htransition; try exact Hkeep; try exact Hreuse_next;
        try reflexivity.
  - Intros co pre post. coq_prop_lift.
    destruct H as [Hlearntsplit [Hlits Hcolearnt]].
    assert (Hin : In (scan_current, co) (msolver_db Mscan)).
    { unfold msolver_db. apply in_or_app. right. rewrite Hlearntsplit.
      apply in_or_app. right. simpl. auto. }
    pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin)
      as Hobj.
    unfold obj_wf in Hobj. rewrite Hlits in Hobj.
    destruct Hobj as [Hlen _].
    destruct clause_contents as [|a0 tail0]; cbn in Hlen; [lia|].
    destruct tail0 as [|a1 tail]; cbn in Hlen; [lia|].
    assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail)
      = tail) by (apply msat_sublist_two_tail_p2).
    set (new_lits := propagation_normalized_clause watch0_2 false_lit
      (a0 :: a1 :: tail)).
    set (co_new := clause_obj_with_lits co new_lits).
    set (prob_route := ms_prob Mscan).
    set (learnt_route := pre ++ (scan_current, co_new) :: post).
    set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
      learnt_route (ms_wm Mscan) (ms_wcaps Mscan)).
    assert (Hupdate : db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan)
        scan_current (a0 :: a1 :: tail) new_lits prob_route learnt_route).
    { right. exists co, pre, post. repeat split; try assumption;
        try reflexivity. }
    assert (Hdb : msolver_db Mscan =
        (ms_prob Mscan ++ pre) ++ (scan_current, co) :: post).
    { unfold msolver_db. rewrite Hlearntsplit, app_assoc. reflexivity. }
    assert (Hdb2 : prob_route ++ learnt_route =
        (ms_prob Mscan ++ pre) ++ (scan_current, co_new) :: post).
    { unfold prob_route, learnt_route. rewrite app_assoc. reflexivity. }
    destruct (msat_propagate_clause_watch_facts_p2 n Mscan p scan_current co
      a0 a1 tail new_lits co_new false_lit watch0_2 sig Hdbwf Hin Hlits
      H_Zlength H_real_watch_pair H_watch0_2 H_false_lit H_sig H_Znth Hp
      Hprocessed ltac:(reflexivity) ltac:(reflexivity)) as
      [Hperm [Hentryold [Hentrynew [Honewsafe
        [Hentryperm [Hswap Hhead]]]]]].
    pose proof (msat_propagate_route_facts_p2 n F A_arr K Mscan Mroute p
      scan_current co co_new a0 a1 tail new_lits prob_route learnt_route
      (ms_prob Mscan ++ pre) post retained raw_suffix Hdb Hdb2 Hupdate
      ltac:(reflexivity) Hdbwf Hin Hperm Hentryold Hentrynew Honewsafe
      Hentryperm Hswap Hhead Hweak Hprop Hheapready Hheapcovers Hreasonless
      Hlevel Hp Hprocessed Hfrontier Hscan) as Htransition.
    assert (Hcases : (a0 = lit_neg_c p /\ watch0_2 = a1) \/
      (a1 = lit_neg_c p /\ watch0_2 = a0)).
    { pose proof H_real_watch_pair as Hpair. pose proof H_watch0_2 as Hsum.
      change (a0 = lit_neg_c p \/ a1 = lit_neg_c p) in Hpair.
      change (watch0_2 + false_lit = a0 + a1) in Hsum.
      rewrite H_false_lit in Hsum. destruct Hpair; [left|right]; split; lia. }
    assert (Hreal : is_tag scan_current = false).
    { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan) scan_current co Hdbwf Hin). }
    assert (Hdbnew : db_wf n (prob_route ++ learnt_route)).
    { pose proof (proj2 Htransition) as Hsem_new.
      destruct Hsem_new as [Hlive_new|[Hnonzero _]]; [|contradiction].
      destruct Hlive_new as (_ & Hweak_new & _).
      destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mroute Hweak_new)
        as (_ & _ & Hdb_new & _). exact Hdb_new. }
    assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mroute p 0 raw_suffix).
    { unfold Mroute.
      eapply minisat_propagation_reuse_real_satisfied__api_reentry;
        [exact Hdbnew|exact Htrail_wf| |exact Hcases|exact Hreal|
         exact Hfocus_cell|exact Hother_true|exact Hreuse_entry].
      unfold new_lits in Hupdate. rewrite H_false_lit in Hupdate. exact Hupdate. }
    Exists garbage_route (replace_Znth jj scan_current watch_memory)
      Mroute raw_suffix (retained ++ scan_current :: nil) watch0_2
      prob_route learnt_route.
    split_pure_spatial.
    + unfold learnt_route.
      msat_propagate_db_entry_spatial_p2 pre post scan_current co_new
        new_lits Htail Hcolearnt H_clause_lits_pointer lits tail.
    + split_pures; apply derivable1s_coq_prop_r;
        try exact Hupdate; try exact Htransition; try exact Hkeep; try exact Hreuse_next;
        try reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_53 : solver_propagate_which_implies_wit_53.
Proof.
  Unfold.
  left; intros.
  bind_fact ( propagation_scan_open n F A_arr K M0 Mentry Mscan p confl source_words retained moved rest garbage
      watch_memory ii jj scan_current raw_suffix ) as H_propagation_scan_open.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p confl rest) as Hreuse_entry.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src copy_dst
      copy_memory ) as H_binary_watch_copy_progress.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i >= endvar ) as H_i.
  bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i_2.
  bind_fact ( j = begin + copy_dst * sizeof ( PTR ) ) as H_j.
  bind_fact ( 0 <= copy_dst ) as H_copy_dst.
  bind_fact ( copy_src <= Zlength source_words ) as H_copy_src.
  bind_fact ( propagation_scan_slot Mscan p scan_wm_pre logical_words scan_wm_post scan_caps_pre scan_wcap
      scan_caps_post ) as H_propagation_scan_slot.
  bind_fact ( ws = vecp_slot wlists_entry p ) as H_ws.
  bind_fact ( propagation_capacity_target_facts Mscan wlists_entry destination candidate scan_wm_pre scan_wm_post
      scan_caps_pre scan_caps_post ) as H_propagation_capacity_target_facts.
  bind_fact ( propagation_scan_candidate_layout scan_current lits stop k offset false_lit p candidate sig
      clause_contents ) as H_propagation_scan_candidate_layout.
  bind_fact ( watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0.
  assert (Hdbwf : db_wf n (msolver_db Mscan)).
  {
    eapply propagation_scan_open_db_wf__propagate_dbu.
    exact H_propagation_scan_open.
  }
  sep_apply_l_atomic
    (propagation_normalized_clause_db_rebuild__propagate_dbu
      n (ms_prob Mscan) (ms_learnt Mscan) scan_current lits stop k offset
      false_lit p candidate sig watch0 clause_contents Hdbwf H_propagation_scan_candidate_layout).
  Intros prob_after learnt_after.
  coq_prop_lift.
  rename H into Hupdate.
  pose proof H_propagation_scan_open as Hopen_reuse.
  destruct Hopen_reuse as
    (Hshape_reuse & Hseed_reuse & Hcaller_reuse & Hscan_frontier &
     Hsem_reuse & Hphysical_reuse & Hrest_reuse & Hconfl_reuse).
  rewrite Hconfl_reuse in Hreuse_entry.
  destruct Hsem_reuse as [Hlive_reuse|[Hnonzero _]]; [|contradiction].
  destruct Hlive_reuse as (_ & Hweak_reuse & _ & _ & _ & _ & _ & _ & _ & Hfront_reuse & Hscan_reuse).
  destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak_reuse)
    as (_ & _ & _ & _ & Htrail_reuse).
  destruct Hscan_frontier as (_ & _ & _ & _ & Hrollback).
  destruct Hrollback as (Hqhead_positive & Hfocus_previous & Hrollback_gate).
  pose proof H_propagation_scan_candidate_layout as Hlayout_reuse.
  destruct Hlayout_reuse as (Hlits_reuse & Hlength_reuse & Hfalse_reuse & _).
  rewrite Hrest_reuse in Hscan_reuse.
  destruct (propagation_unit_normalized_watcher_transport__propagate_dbu
    n Mscan (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan)))
    p scan_current raw_suffix retained clause_contents watch0 false_lit lits
    prob_after learnt_after Hdbwf Hlits_reuse Hfalse_reuse H_watch0
    Hscan_reuse Hupdate Hfront_reuse)
    as (selected & a0 & a1 & tail & Hcontents & Hlong & Hselected & Hwords &
      Htail & Hwatchcases & Hperm & Hexpected & Hnewfrontier).
  set (Mnormalized := msolver_propagation_db_wmap_update Mscan prob_after learnt_after
    (ms_wm Mscan) (ms_wcaps Mscan)).
  assert (Hreuse_normalized : minisat_propagation_reuse_scan M0 Mnormalized p 0 rest).
  { unfold Mnormalized. apply (minisat_propagation_reuse_normalize__api_reentry
      M0 Mscan p 0 rest scan_current a0 a1 tail watch0
      prob_after learnt_after (ms_wm Mscan) (ms_wcaps Mscan)).
    - rewrite <- Hcontents, <- Hfalse_reuse. exact Hupdate.
    - rewrite <- Hfalse_reuse. exact Hwatchcases.
    - exact Hreuse_entry. }
  assert (Hreuse_abort : minisat_propagation_reuse_live M0
    (msolver_propagation_abort Mscan prob_after learnt_after
      (scan_wm_pre ++ sublist 0 ((j - begin) ÷ sizeof(PTR)) copy_memory :: scan_wm_post)
      (scan_caps_pre ++ scan_wcap :: scan_caps_post) simp_count prop_count)).
  { change (minisat_propagation_reuse_live M0
      (msolver_propagation_abort Mnormalized (ms_prob Mnormalized) (ms_learnt Mnormalized)
        (scan_wm_pre ++ sublist 0 ((j - begin) ÷ sizeof(PTR)) copy_memory :: scan_wm_post)
        (scan_caps_pre ++ scan_wcap :: scan_caps_post) simp_count prop_count)).
    eapply (minisat_propagation_reuse_rollback__api_reentry
      n M0 Mnormalized p rest);
      [exact Htrail_reuse|exact Hqhead_positive|exact Hfocus_previous|exact Hreuse_normalized]. }
  pose proof (propagation_capacity_abort_pure_core__propagate_dbu
      n F A_arr K M0 Mentry Mscan p confl
      source_words retained moved rest garbage watch_memory ii jj
      scan_current raw_suffix raw_prefix copy_src copy_dst copy_memory
      scan_wm_pre scan_wm_post logical_words
      scan_caps_pre scan_caps_post scan_wcap
      wlists_entry destination candidate lits stop k offset false_lit sig
      clause_contents watch0 begin i j endvar simp_count prop_count
      prob_after learnt_after) as Habort.
  specialize (Habort
      H_propagation_scan_open H_binary_watch_copy_progress H_endvar H_i H_i_2 H_j H_copy_src H_propagation_scan_slot
          H_propagation_capacity_target_facts H_propagation_scan_candidate_layout
      H_watch0 Hupdate).
  destruct Habort as [Hstate [Hconfl2 [Hprelen [Hdestination
       [Hprobkeys [Hlearntkeys Hstatslen]]]]]].
  sep_apply_l_atomic
    (solver_propagation_nonwatch_rest_abort_fold__propagate_dbu
      s Mscan prob_after learnt_after
      (scan_wm_pre ++
         sublist 0 ((j - begin) ÷ sizeof(PTR)) copy_memory :: scan_wm_post)
      (scan_caps_pre ++ scan_wcap :: scan_caps_post)
      simp_count prop_count values s_reasons levels_entry s_trail
      Hprobkeys Hlearntkeys Hstatslen).
  sep_apply_l_atomic
    (solver_propagation_capacity_rest_fold__propagate_dbu
      s (msolver_propagation_abort Mscan prob_after learnt_after
           (scan_wm_pre ++
              sublist 0 ((j - begin) ÷ sizeof(PTR)) copy_memory :: scan_wm_post)
           (scan_caps_pre ++ scan_wcap :: scan_caps_post)
           simp_count prop_count)
      wlists_entry (Zlength scan_wm_pre) (lit_neg_c candidate)
      scan_wm_pre scan_wm_post scan_caps_pre scan_caps_post
      values levels_entry).
  Exists (msolver_propagation_abort Mscan prob_after learnt_after
      (scan_wm_pre ++
         sublist 0 ((j - begin) ÷ sizeof(PTR)) copy_memory :: scan_wm_post)
      (scan_caps_pre ++ scan_wcap :: scan_caps_post)
      simp_count prop_count)
    prob_after learnt_after.
  split_pure_spatial.
  + entailer_with ltac:(lia).
  + split_pures; apply derivable1s_coq_prop_r;
      try exact Hupdate; try exact Hstate; try exact Hreuse_abort;
      try exact Hconfl2; try exact Hprelen;
      try exact H_ws; try exact H_endvar; try exact H_i;
      try exact H_j; try exact H_copy_dst; try exact H_propagation_scan_candidate_layout;
      try exact Hdestination; try lia.
    constructor.
    - rewrite Hprelen. exact H_ws.
    - exact Hdestination.
    - reflexivity.
    - reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_72 : solver_propagate_which_implies_wit_72.
Proof.
  Unfold. left. intros.
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
  (* db_wf projected by solver_propagation_weak_core_facts__propagate. *)
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
      (ms_wm Mscan) (ms_wcaps Mscan))).
  { eapply propagation_unit_db_weak_transport__propagate_dbu
      with (p := p) (current := scan_current) (false_lit := false_lit)
        (watch0 := watch0) (a0 := a0) (a1 := a1) (tail := tail)
        (contents := clause_contents) (co := co); eassumption. }
  unfold enqueue_post_at. Intros qtail' assigns' levels' reasons' trail'.
  match goal with Htr : enqueue_transition watch0 _ _ unit_ret _ _ _ _ _ _ _ _ _ _
    |- _ => rename Htr into Henqueue end.
  rewrite H_Znth in Henqueue.
  unfold enqueue_state_at. Intros rsn_enqueue trl_enqueue.
  assert (Hpostbound : 0 <= qtail' <= ms_cap Mscan) by entailer_with ltac:(lia).
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
    (ms_wm Mscan) (ms_wcaps Mscan)).
  assert (Hreuse_db : minisat_propagation_reuse_scan M0 Mdb p 0
    (scan_current :: raw_suffix)).
  { unfold Mdb. apply (minisat_propagation_reuse_normalize__api_reentry
      M0 Mscan p 0 (scan_current :: raw_suffix) scan_current a0 a1 tail watch0
      prob_after learnt_after (ms_wm Mscan) (ms_wcaps Mscan)).
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
  entailer_with ltac:(lia).
  apply store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_73 : solver_propagate_which_implies_wit_73.
Proof.
  unfold solver_propagate_which_implies_wit_73.
  unfold stats_propagations.
  Unfold.
  right.
  intros.
  subst p.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan
    (Zlength scan_wm_pre) 0 rest) as Hreuse_entry.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( msolver_seed_shadow Mscan ) as H_msolver_seed_shadow.
  bind_fact ( propagation_caller_frame M0 Mscan ) as H_propagation_caller_frame.
  bind_fact ( propagation_scan_frontier Mentry Mscan (Zlength scan_wm_pre) ) as H_propagation_scan_frontier.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan (Zlength scan_wm_pre) 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( candidate_post_memory = watch_memory ) as H_candidate_post_memory.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( migration_post_memory = replace_Znth ii (Znth ii candidate_post_memory 0) candidate_post_memory ) as
      H_migration_post_memory.
  bind_fact ( false_lit = lit_neg_c (Zlength scan_wm_pre) ) as H_false_lit.
  bind_fact ( real_watch_pair (Zlength scan_wm_pre) clause_contents ) as H_real_watch_pair.
  bind_fact ( watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0.
  bind_fact ( propagation_scan_candidate_layout scan_current lits stop k offset false_lit (Zlength scan_wm_pre)
      candidate (2 * lit_sign_c candidate - 1) clause_contents ) as H_propagation_scan_candidate_layout.
  bind_fact ( Znth (lit_var_c candidate) (mt_assigns (ms_core Mscan)) 0 <> 2 * lit_sign_c candidate - 1 ) as H_Znth_2.
  bind_fact ( propagation_destination_index (2 * ms_size Mscan) (Zlength scan_wm_pre) (lit_neg_c candidate) ) as
      H_propagation_destination_index.
  bind_fact ( propagation_real_migrated_physical_alias wlists_entry (Zlength scan_wm_pre) (lit_neg_c candidate) scan_current
      destination_index destination_ptr scan_wm_pre scan_wm_post destination_words ) as
      H_propagation_real_migrated_physical_alias.
  bind_fact ( propagation_scan_slot Mscan (Zlength scan_wm_pre) scan_wm_pre logical_words scan_wm_post scan_caps_pre
      scan_wcap scan_caps_post ) as H_propagation_scan_slot.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  pose proof H_propagation_scan_slot as Hslot.
  destruct Hslot as [Hwm [Hwcaps [Hpre Hcapspre]]].
  pose proof (msat_propagate_scan_db_wf_p2 _ _ _ _ _ _ _ _
      H_solver_propagation_scan_semantics) as Hdbwf.
  sep_apply (propagation_migrated_clause_db_rebuild__propagate_dbu n (ms_prob Mscan)
      (ms_learnt Mscan) scan_current lits stop k offset false_lit (Zlength scan_wm_pre) candidate (2 * lit_sign_c
      candidate - 1) watch0 clause_contents Hdbwf H_propagation_scan_candidate_layout).
  Intros prob_after learnt_after.
  match goal with Hup : db_pair_lits_update _ _ scan_current clause_contents _ prob_after learnt_after |- _ =>
      rename Hup into Hupdate end.
  destruct (msat_propagate_real_migrated_exit_p2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ destination_cap _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ H_solver_shape H_msolver_seed_shadow H_propagation_caller_frame H_propagation_scan_frontier
      H_solver_propagation_scan_semantics H_rest H_propagation_watch_scan_physical H_candidate_post_memory H_Znth
      H_migration_post_memory H_false_lit H_real_watch_pair H_watch0 H_propagation_scan_candidate_layout H_Znth_2
      H_propagation_destination_index H_propagation_scan_slot H_simp_count H_prop_count Hupdate Hreuse_entry)
      as [Hwmlen [Htargetrange [Htargetneq [Hpostcaps [Hexit Hreuseroute]]]]].
  inversion H_propagation_real_migrated_physical_alias; subst destination_index destination_ptr destination_words.
  sep_apply (msat_vecp_rep_from_cells_p2 (vecp_slot wlists_entry (lit_neg_c candidate))
      (wlists_split_target_words (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
      scan_wm_post ++ (scan_current :: nil)) destination_cap destination_base
      ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (wlists_destination_update_to_source_hole__propagate_dbu s wlists_entry (Zlength
      scan_wm_pre) (lit_neg_c candidate) scan_wm_pre scan_wm_post scan_caps_pre scan_caps_post
      (wlists_split_target_words (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre scan_wm_post ++
      (scan_current :: nil)) destination_cap eq_refl (eq_sym Hcapspre) Hpostcaps ltac:(rewrite Zlength_app,
      Zlength_cons; rewrite Hwm in Hwmlen; rewrite Zlength_app, Zlength_cons in Hwmlen; lia) Htargetneq).
  Exists (msolver_propagation_db_wmap_update Mscan prob_after learnt_after
      (propagation_move_wmap (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
      (retained ++ raw_suffix) scan_wm_post scan_current)
      (propagation_move_wcaps (lit_neg_c candidate) scan_caps_pre scan_wcap scan_caps_post
      destination_cap)) (garbage ++ (scan_current :: nil)) prob_after learnt_after.
  split_pure_spatial; [entailer_with ltac:(lia)|].
  split_pures; apply derivable1s_coq_prop_r;
    first [exact Hupdate | exact Hexit | exact Hreuseroute].
Qed.

(* ===== solver_read_wlist return wits (1 proofs) ===== *)
Lemma proof_of_solver_read_wlist_return_wit_1 : solver_read_wlist_return_wit_1.
Proof.
  Unfold.
  left.
  intros l_pre s_pre wl PreH1.
  assert (Hslot :
    wl + l_pre * sizeof("vecp_t") = vecp_slot wl l_pre).
  { unfold vecp_slot. reflexivity. }
  unfold solver_wlists_handle.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_read_wlist which_implies wits (1 proofs) ===== *)
Lemma proof_of_solver_read_wlist_which_implies_wit_1 : solver_read_wlist_which_implies_wit_1.
Proof.
  Unfold.
  left.
  intros wl s.
  unfold solver_wlists_handle.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_search entail wits (11 proofs) ===== *)
Lemma proof_of_solver_search_entail_wit_8_3 : solver_search_entail_wit_8_3.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_4 : solver_search_entail_wit_8_4.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_5 : solver_search_entail_wit_8_5.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_6 : solver_search_entail_wit_8_6.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_7 : solver_search_entail_wit_8_7.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_8 : solver_search_entail_wit_8_8.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_9 : solver_search_entail_wit_8_9.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_10 : solver_search_entail_wit_8_10.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_11 : solver_search_entail_wit_8_11.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_12 : solver_search_entail_wit_8_12.
Proof.
  msat_search_model_copy_entry_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_9 : solver_search_entail_wit_9.
Proof.
  aggressive_pre_process.
  bind_fact ( solver_search_model_ready n F A_arr A_inst Mselected ) as H_solver_search_model_ready.
  bind_fact ( model_copy_progress n Mselected model_words_2 i ) as H_model_copy_progress.
  assert (Hready : solver_search_model_ready n F A_arr A_inst Mselected) by
    exact H_solver_search_model_ready.
  unfold solver_search_model_ready in H_solver_search_model_ready.
  destruct H_solver_search_model_ready as (Hinv & _ & _ & _ & _ & _).
  assert (Hn : 0 <= n) by exact (msi_n_range Hinv).
  assert (Hsize : ms_size Mselected = n) by
    (symmetry; exact (msi_size Hinv)).
  assert (Hassigns : Zlength (mt_assigns (ms_core Mselected)) = n) by
    (rewrite (solver_shape_assigns_len Mselected (msi_shape Hinv)); exact Hsize).
  destruct H_model_copy_progress as (Hi & Hlen & Hmodel).
  Exists (app model_words_2 (cons (Znth i (replace_Znth i
    (Znth i (mt_assigns (ms_core Mselected)) 0)
    (mt_assigns (ms_core Mselected))) 0) nil)).
  rewrite replace_Znth_Znth in *.
  sep_apply CharArray.full_to_seg.
  entailer_with ltac:(first [assumption | lia]).
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
       try exact Hready.
  unfold model_copy_progress.
  repeat split.
  - lia.
  - lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - rewrite Hmodel.
    rewrite (sublist_split 0 (i + 1) i
      (mt_assigns (ms_core Mselected))) by lia.
    rewrite (sublist_single 0 i
      (mt_assigns (ms_core Mselected))) by lia.
    reflexivity.
Qed.

(* ===== solver_search partial_solve wits (17 proofs) ===== *)
Lemma proof_of_solver_search_partial_solve_wit_56_pure : solver_search_partial_solve_wit_56_pure.
Proof.
  unfold solver_search_partial_solve_wit_56_pure.
  unfold stats_conflicts, stats_set_conflicts.
  msat_search_backjump_ready_pure_p2 H_retval H_backjump H_fp32 H_model
    retval n F A_arr A_inst Mcur Mback words.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_57_pure : solver_search_partial_solve_wit_57_pure.
Proof.
  unfold solver_search_partial_solve_wit_57_pure.
  unfold stats_conflicts, stats_set_conflicts.
  msat_search_backjump_ready_pure_p2 H_retval H_backjump H_fp32 H_model
    retval n F A_arr A_inst Mcur Mback words.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_58_pure : solver_search_partial_solve_wit_58_pure.
Proof.
  unfold solver_search_partial_solve_wit_58_pure.
  unfold stats_conflicts, stats_set_conflicts.
  msat_search_cla_inc_nonneg_p2 H_msolver_inv n F A_arr A_inst Mrecord.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_59_pure : solver_search_partial_solve_wit_59_pure.
Proof.
  unfold solver_search_partial_solve_wit_59_pure.
  unfold stats_conflicts, stats_set_conflicts.
  msat_search_cla_inc_nonneg_p2 H_msolver_inv n F A_arr A_inst Mrecord.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_60_pure : solver_search_partial_solve_wit_60_pure.
Proof.
  unfold solver_search_partial_solve_wit_60_pure.
  unfold stats_conflicts, stats_set_conflicts.
  msat_search_cla_inc_nonneg_p2 H_msolver_inv n F A_arr A_inst Mrecord.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_73_pure : solver_search_partial_solve_wit_73_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mstable ) as H_msolver_inv.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  unfold solver_shape in Hshape.
  destruct Hshape as
    [Hnonneg [Hcap [Htwosize [Hassign [Hlevels _]]]]].
  split_pures.
  - dump_pre_spatial. exact Hlevels.
  - dump_pre_spatial. exact Hassign.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_79_pure : solver_search_partial_solve_wit_79_pure.
Proof.
  msat_search_learnt_vec_bounds_p2 Hcap.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_92_pure : solver_search_partial_solve_wit_92_pure.
Proof.
  msat_search_learnt_vec_bounds_p2 Hcap.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_93_pure : solver_search_partial_solve_wit_93_pure.
Proof.
  msat_search_learnt_vec_bounds_p2 Hcap.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_96_pure : solver_search_partial_solve_wit_96_pure.
Proof.
  msat_search_learnt_vec_bounds_p2 Hcap.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_190_pure : solver_search_partial_solve_wit_190_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_191_pure : solver_search_partial_solve_wit_191_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_192_pure : solver_search_partial_solve_wit_192_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_193_pure : solver_search_partial_solve_wit_193_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_194_pure : solver_search_partial_solve_wit_194_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_195_pure : solver_search_partial_solve_wit_195_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_196_pure : solver_search_partial_solve_wit_196_pure.
Proof.
  msat_search_model_ready_conjuncts_p2 H_model_ready n F A_arr A_inst Mselected.
Qed.

(* ===== solver_search which_implies wits (4 proofs) ===== *)
Lemma proof_of_solver_search_which_implies_wit_1 : solver_search_which_implies_wit_1.
Proof.
  Unfold.
  left; intros.
  unfold solver_search_pre.
  Intros.
  sep_apply solver_rep_cancel_split.
  Intros lvl.
  Exists lvl.
  unfold solver_levels_slice_at.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_2 : solver_search_which_implies_wit_2.
Proof.
  Unfold.
  left; intros.
  lazymatch goal with
  | |- _ |-- solver_rep_levels_wl_at ?s ?M ?wl ?lvl =>
      transitivity (solver_cancel_owned s M wl ** solver_levels_slice_at s M lvl)
  end.
  - unfold solver_levels_slice_at.
    msat_manual_entailer_with ltac:(lia).
  - apply solver_cancel_join_rep_levels_at.
Qed.

Lemma proof_of_solver_search_which_implies_wit_4 : solver_search_which_implies_wit_4.
Proof.
  Unfold.
  left; intros.
  bind_fact ( solver_at_root M0 ) as H_solver_at_root.
  entailer_with ltac:(lia); try (symmetry; exact H_solver_at_root).
Qed.

Lemma proof_of_solver_search_which_implies_wit_5 : solver_search_which_implies_wit_5.
Proof.
  Unfold.
  left. intros Mview search_wl s levels.
  unfold solver_search_root_frame_at, solver_search_init_frame_at,
    solver_search_bundle_at, solver_search_payload.
  Intros.
  sep_apply (join_scalars_root s Mview).
  sep_apply (join_vecs_trail_lim s Mview).
  sep_apply (peel_fp_decays s Mview).
  sep_apply (peel_vecs_model s Mview).
  unfold stats_rep, stats_without_starts_rep.
  Intros.
  msat_manual_entailer_with ltac:(lia).
  csimpl; reflexivity.
Qed.

(* ===== solver_search return wits (1 proofs) ===== *)
Lemma proof_of_solver_search_return_wit_1 : solver_search_return_wit_1.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Left. Left. Left.
  Exists Mmodel_root.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_solve entail wits (8 proofs) ===== *)
Lemma proof_of_solver_solve_entail_wit_5_1 : solver_solve_entail_wit_5_1.
Proof.
  Unfold.
  intros.
  assert (Hprefix0 : assumption_prefix raw_entry 0 = @nil literal).
  { unfold assumption_prefix.
    rewrite Zsublist_nil by lia.
    reflexivity. }
  Left.
  Exists raw_entry 0 Mready.
  rewrite Hprefix0.
  entailer_with ltac:(lia).
  pose proof (Zlength_nonneg raw_entry).
  lia.
Qed.

Lemma proof_of_solver_solve_entail_wit_5_2 : solver_solve_entail_wit_5_2.
Proof.
  Unfold.
  intros.
  assert (Hprefix0 : assumption_prefix raw_entry 0 = @nil literal).
  { unfold assumption_prefix.
    rewrite Zsublist_nil by lia.
    reflexivity. }
  Right.
  Exists raw_entry 0 Mready.
  rewrite Hprefix0.
  entailer_with ltac:(lia).
  pose proof (Zlength_nonneg raw_entry).
  lia.
Qed.

Lemma proof_of_solver_solve_entail_wit_6_1 : solver_solve_entail_wit_6_1.
Proof.
  Unfold. intros. Left.
  msat_solve_lbool_cell_arm_p2 Mcur retval_2.
Qed.

Lemma proof_of_solver_solve_entail_wit_6_2 : solver_solve_entail_wit_6_2.
Proof.
  Unfold. intros. Left.
  msat_solve_lbool_cell_arm_p2 Mcur retval_3.
Qed.

Lemma proof_of_solver_solve_entail_wit_6_3 : solver_solve_entail_wit_6_3.
Proof.
  Unfold. intros. Right.
  msat_solve_lbool_cell_arm_p2 Mcur retval_5.
Qed.

Lemma proof_of_solver_solve_entail_wit_6_4 : solver_solve_entail_wit_6_4.
Proof.
  Unfold. intros. Right.
  msat_solve_lbool_cell_arm_p2 Mcur retval_6.
Qed.

Lemma proof_of_solver_solve_entail_wit_7_1 : solver_solve_entail_wit_7_1.
Proof.
  msat_solve_capacity_arm_return_p2 A_arr raw Mcur n F M H.
Qed.

Lemma proof_of_solver_solve_entail_wit_7_2 : solver_solve_entail_wit_7_2.
Proof.
  msat_solve_capacity_arm_return_p2 A_arr raw Mcur n F M H.
Qed.

(* ===== solver_solve partial_solve wits (10 proofs) ===== *)
Lemma proof_of_solver_solve_partial_solve_wit_38_pure : solver_solve_partial_solve_wit_38_pure.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  bind_fact ( signed_last_nbits (Znth (retval_2 - 0) (mt_assigns (ms_core Mcur)) 0) 8 = 0 ) as H_signed_last_nbits.
  rewrite !Z.sub_0_r in *.
  subst retval_2.
  assert (Hcell : lbool_cell
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0)).
  { eapply Forall_Znth_elim.
    (* The invariant and the assigns-length fact are selected by shape, not by PreH
              index: the numbering shifts whenever the obligation gains a binder. *)
    - match goal with
      | H : msolver_inv_assuming_strong _ _ _ _ Mcur |- _ =>
          exact (mtw_cells (msa_trail_wf (msas_weak H)))
      end.
    - match goal with
      | H : Zlength (mt_assigns (ms_core Mcur)) = n |- _ => rewrite H
      end; lia. }
  assert (Hrepr : signed_last_nbits
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0) 8 =
    Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
  { apply signed_last_nbits_eq; [lia|].
    unfold lbool_cell in Hcell.
    destruct Hcell as [Hcell | [Hcell | Hcell]];
      rewrite Hcell; lia. }
  rewrite Hrepr in H_signed_last_nbits.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_39_pure : solver_solve_partial_solve_wit_39_pure.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  bind_fact ( signed_last_nbits (- Znth (retval_2 - 0) (mt_assigns (ms_core Mcur)) 0) 8 = 0 ) as H_signed_last_nbits.
  rewrite !Z.sub_0_r in *.
  subst retval_2.
  assert (Hcell : lbool_cell
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0)).
  { eapply Forall_Znth_elim.
    (* The invariant and the assigns-length fact are selected by shape, not by PreH
              index: the numbering shifts whenever the obligation gains a binder. *)
    - match goal with
      | H : msolver_inv_assuming_strong _ _ _ _ Mcur |- _ =>
          exact (mtw_cells (msa_trail_wf (msas_weak H)))
      end.
    - match goal with
      | H : Zlength (mt_assigns (ms_core Mcur)) = n |- _ => rewrite H
      end; lia. }
  assert (Hrepr : signed_last_nbits
    (- Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0) 8 =
    - Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
  { apply signed_last_nbits_eq; [lia|].
    unfold lbool_cell in Hcell.
    destruct Hcell as [Hcell | [Hcell | Hcell]];
      rewrite Hcell; lia. }
  rewrite Hrepr in H_signed_last_nbits.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_48_pure : solver_solve_partial_solve_wit_48_pure.
Proof.
  msat_solve_assume_fresh_pure_p2 k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_49_pure : solver_solve_partial_solve_wit_49_pure.
Proof.
  msat_solve_assume_fresh_pure_p2 k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_50_pure : solver_solve_partial_solve_wit_50_pure.
Proof.
  msat_solve_assume_fresh_pure_p2 k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_51_pure : solver_solve_partial_solve_wit_51_pure.
Proof.
  msat_solve_assume_fresh_pure_p2 k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_108_pure : solver_solve_partial_solve_wit_108_pure.
Proof.
  Unfold; right; intros.
  rename n_solver_solve_spec into n.
  msat_solve_assign_pos_pure_p2 H_signed_last_nbits retval_2 retval Mcur k raw n.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_109_pure : solver_solve_partial_solve_wit_109_pure.
Proof.
  Unfold; right; intros.
  rename n_solver_solve_spec into n.
  msat_solve_assign_neg_pure_p2 H_signed_last_nbits retval_2 retval Mcur k raw n.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_110_pure : solver_solve_partial_solve_wit_110_pure.
Proof.
  Unfold; right; intros.
  rename n_solver_solve_spec into n.
  msat_solve_assign_pos_pure_p2 H_signed_last_nbits retval_2 retval Mcur k raw n.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_111_pure : solver_solve_partial_solve_wit_111_pure.
Proof.
  Unfold; left; intros.
  rename n_solver_solve_spec into n.
  msat_solve_assign_neg_pure_p2 H_signed_last_nbits retval_2 retval Mcur k raw n.
Qed.

(* ===== solver_solve return wits (4 proofs) ===== *)
Lemma proof_of_solver_solve_return_wit_9 : solver_solve_return_wit_9.
Proof.
  msat_solve_unsat_arm_return_p2 A_arr raw Massumption_unsat.
  msat_manual_entailer_with ltac:(tauto || int_auto).
Qed.

Lemma proof_of_solver_solve_return_wit_10 : solver_solve_return_wit_10.
Proof.
  msat_solve_unsat_arm_return_p2 A_arr raw Massumption_unsat.
  msat_manual_entailer_with ltac:(tauto || int_auto).
Qed.

Lemma proof_of_solver_solve_return_wit_11 : solver_solve_return_wit_11.
Proof.
  msat_solve_unsat_arm_return_p2 A_arr raw Massumption_unsat.
  msat_manual_entailer_with ltac:(tauto || lia).
Qed.

Lemma proof_of_solver_solve_return_wit_12 : solver_solve_return_wit_12.
Proof.
  msat_solve_unsat_arm_return_p2 A_arr raw Massumption_unsat.
  msat_manual_entailer_with ltac:(tauto || lia).
Qed.

(* ===== solver_solve which_implies wits (2 proofs) ===== *)
Lemma proof_of_solver_solve_which_implies_wit_1 : solver_solve_which_implies_wit_1.
Proof.
  left. intros. unfold solver_rep_wl. Intros lvl. Exists lvl.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_2 : solver_solve_which_implies_wit_2.
Proof.
  left. intros. apply solver_rep_levels_assigns_split__simplify.
Qed.

(* ===== vecp_remove entail wits (4 proofs) ===== *)
Lemma proof_of_vecp_remove_entail_wit_1 : vecp_remove_entail_wit_1.
Proof.
  aggressive_pre_process.
  all: bind_fact ( Zlength pre = index ) as H_Zlength;
       bind_fact ( vecp_remove_member e_pre (Znth index wm nil) )
         as H_vecp_remove_member;
       unfold vecp_remove_member in H_vecp_remove_member;
       subst wm;
       rewrite app_Znth2 in H_vecp_remove_member by lia;
       rewrite H_Zlength in H_vecp_remove_member;
       replace (index - index) with 0 in H_vecp_remove_member by lia;
       rewrite Znth0_cons in H_vecp_remove_member.
  - destruct words0 as [|a words0]; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg words0). lia.
  - unfold vecp_remove_scan_inv.
    repeat split.
    + lia.
    + destruct words0 as [|a words0]; [contradiction |].
      rewrite Zlength_cons. pose proof (Zlength_nonneg words0). lia.
    + rewrite sublist_self by reflexivity. exact H_vecp_remove_member.
    + simpl. constructor.
Qed.

Lemma proof_of_vecp_remove_entail_wit_2 : vecp_remove_entail_wit_2.
Proof.
  aggressive_pre_process.
  all: bind_fact ( Znth (j - 0) words0 0 <> e_pre ) as H_Znth;
       bind_fact ( vecp_remove_scan_inv e_pre words0 j )
         as H_vecp_remove_scan_inv;
       replace (j - 0) with j in H_Znth by lia;
       pose proof
         (vecp_remove_scan_step__clause_is_lit e_pre words0 j
           H_vecp_remove_scan_inv H_Znth) as Hstep.
  - unfold vecp_remove_scan_inv in Hstep.
    destruct Hstep as ((_ & Hlt) & _). exact Hlt.
  - exact Hstep.
Qed.

Lemma proof_of_vecp_remove_entail_wit_3 : vecp_remove_entail_wit_3.
Proof.
  aggressive_pre_process.
  bind_fact ( Znth (j - 0) words0 0 = e_pre ) as H_Znth.
  bind_fact ( vecp_remove_scan_inv e_pre words0 j ) as H_vecp_remove_scan_inv.
  Exists j.
  entailer_with ltac:(lia).
  replace (j - 0) with j in * by lia.
  rewrite <- H_Znth in H_vecp_remove_scan_inv.
  apply vecp_remove_shift_init__clause_is_lit; [exact H_vecp_remove_scan_inv|reflexivity].
Qed.

Lemma proof_of_vecp_remove_entail_wit_4 : vecp_remove_entail_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact ( vecp_remove_shift_inv e_pre words0 found_2 j words_now_2 ) as H_vecp_remove_shift_inv.
  Exists found_2
    (replace_Znth j (Znth (j + 1 - 0) words_now_2 0) words_now_2).
  unfold PtrArray.full.
  entailer_with ltac:(lia).
  all: try rewrite Zlength_replace_Znth.
  - unfold PtrArray.seg, store_array. cancel.
  - lia.
  - apply Zlength_nonneg.
  - lia.
  - replace (j + 1 - 0) with (j + 1) by lia.
    apply vecp_remove_shift_step__clause_is_lit; [exact H_vecp_remove_shift_inv|lia].
  - reflexivity.
Qed.

(* ===== vecp_remove return wits (1 proofs) ===== *)
Lemma proof_of_vecp_remove_return_wit_1 : vecp_remove_return_wit_1.
Proof.
  aggressive_pre_process.
  assert (Hrow : Znth index wm (@nil Z) = words0).
  { subst wm. rewrite app_Znth2 by lia.
    replace (index - Zlength pre) with 0 by lia. reflexivity. }
  rewrite Hrow.
  Exists found_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== vecp_remove which_implies wits (1 proofs) ===== *)
Lemma proof_of_vecp_remove_which_implies_wit_1 : vecp_remove_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  unfold wlists_focus_at.
  Intros pre0 words0 post0 capspre cap capspost.
  unfold wlists_focus_rep, vecp_rep.
  Intros p.
  unfold vecp_rep_at.
  Exists p capspre cap capspost pre0 words0 post0.
  unfold vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  entailer_with ltac:(int_auto).
  destruct H as (Hwm & Hcaps & Hpre & Hcapspre & Hv).
  rewrite Hpre, Hv. cancel.
Qed.


(* Additional obligations for the constructor and incremental public API. *)

Lemma helper_of_solver_solve_which_implies_wit_3_split_goal_spatial :
  solver_solve_which_implies_wit_3_split_goal_spatial.
Proof.
  unfold solver_solve_which_implies_wit_3_split_goal_spatial. intros.
  rename n_solver_solve_spec into n. rename F_solver_solve_spec into F.
  rename M_solver_solve_spec into M0.
  set (Mr := msolver_resume_pending M0) in *.
  assert (Hstrong : msolver_inv_assuming_strong n F nil nil Mr) by exact (proj1 PreH1).
  assert (Hpend : ms_capacity_root_propagation_pending Mr = 0)
    by exact (proj2 (proj2 PreH1)).
  assert (Hseed : msolver_seed_shadow Mr)
    by exact (msolver_resume_pending_seed__api_reentry M0 PreH2).
  assert (Hprop : solver_propagation_inv n F nil (PropagationAssuming nil) Mr).
  { unfold solver_propagation_inv. simpl. split.
    - exact Hpend.
    - constructor.
      + exact (msas_weak Hstrong).
      + exact (msas_prop_level Hstrong).
      + exact (msas_watch_frontier Hstrong).
      + left. exact (msas_heap_covers Hstrong).
      + exact (msas_reasonless_current Hstrong). }
  unfold solver_propagate_pre.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_3 : solver_solve_which_implies_wit_3.
Proof.
  left. exact helper_of_solver_solve_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_4 : solver_solve_which_implies_wit_4.
Proof.
  Unfold. left; intros.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M0.
  rename n_solver_solve_spec into n. rename F_solver_solve_spec into F.
  assert (Hbc : minisat_base_watch_completed (msolver_resume_pending M0))
    by exact (solver_update_watch_ready_base_completed__api_reentry n F M0 PreH1 PreH2).
  assert (Hcap0 : ms_cap (msolver_resume_pending M0) = ms_cap M0)
    by apply msolver_resume_pending_size_cap__api_reentry.
  assert (Hstatus : propagation_status = -2) by lia.
  subst propagation_status.
  unfold solver_propagate_post.
  rewrite !orp_sepcon_right_equiv.
  repeat apply derivable1_orp_elim.
  - Intros Mdone. entailer_with ltac:(lia).
  - Intros Mconf p focus C. entailer_with ltac:(lia).
  - unfold solver_propagation_capacity_raw.
    Intros Mcap.
    match goal with
    | H : solver_propagation_inv _ _ _ _ _ /\ _ |- _ =>
        destruct H as (Hinv & Hcaller & Hreuse & Hseed & Hexhausted & Hwatch & Hscan)
    end.
    assert (Hcap : ms_cap Mcap = ms_cap M0).
    { unfold propagation_caller_frame in Hcaller.
      destruct Hcaller as (_ & _ & _ & _ & Hc). rewrite Hc. exact Hcap0. }
    assert (Hbc_cap : minisat_base_watch_completed Mcap)
      by exact ((proj1 Hreuse) Hbc).
    Exists Mcap.
    unfold solver_prepare_capacity_pre.
    sep_apply (solver_propagation_capacity_rep_at_refold
      s Mcap assigns_prop levels_entry solve_wl).
    sep_apply (solver_rep_assigns_levels_at_rep
      s Mcap assigns_prop levels_entry solve_wl).
    repeat sep_apply store_int_undef_store_int.
    repeat sep_apply store_ptr_undef_store_ptr.
    entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_5 : solver_solve_which_implies_wit_5.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename M_solver_solve_spec into M0.
  rename solve_wl_solver_solve_spec into solve_wl.
  assert (Hbc : minisat_base_watch_completed (msolver_resume_pending M0))
    by exact (solver_update_watch_ready_base_completed__api_reentry n F M0 PreH1 PreH2).
  assert (Hlim0 : Zlength (mt_lim (ms_core (msolver_resume_pending M0))) = 0)
    by exact (proj1 (proj2 PreH1)).
  assert (Hcap0 : ms_cap (msolver_resume_pending M0) = ms_cap M0)
    by apply msolver_resume_pending_size_cap__api_reentry.
  assert (Hstatus : propagation_status = 0) by lia.
  subst propagation_status.
  unfold assumptions_array.
  Intros raw.
  match goal with
  | H : endvar = _ /\ A_arr = lits_denote raw /\ _ |- _ =>
      destruct H as (Hend & HA & Hrawwf & Hempty)
  end.
  assert (HAwf : Forall (literal_wf n) A_arr).
  { rewrite HA. apply lits_denote_wf. exact Hrawwf. }
  unfold solver_propagate_post.
  rewrite !orp_sepcon_right_equiv.
  repeat apply derivable1_orp_elim.
  - Intros Mdone. entailer_with ltac:(lia).
  - Intros Mconf p focus C.
    match goal with
    | H : propagation_cancel_ready _ _ _ _ _ _ /\ _ |- _ =>
        destruct H as (Hcancel & Hcaller & Hwatch & Hresident & Hseed & Hcert & Hptr)
    end.
    pose proof Hcancel as Hcancel0.
    unfold propagation_cancel_ready in Hcancel.
    destruct Hcancel as [Hsw Hcancel_rest].
    unfold solver_propagation_weak in Hsw; cbn in Hsw.
    destruct Hsw as [Hpending Hassuming].
    assert (Hsize : ms_size Mconf = n).
    { symmetry. exact (msa_size Hassuming). }
    unfold propagation_caller_frame in Hcaller.
    destruct Hcaller as (Hlim & Hroot & Hmodel & Hdecay & Hcap).
    assert (Hlim_conf : Zlength (mt_lim (ms_core Mconf)) = 0).
    { rewrite Hlim. exact Hlim0. }
    assert (Hcap_public : ms_cap Mconf = ms_cap M0).
    { rewrite Hcap. exact Hcap0. }
    (* the gate fires unconditionally *)
    pose proof (solver_propagation_conflict_base_recovery__api_reentry
      n F nil (PropagationAssuming nil) Mconf focus Hcancel0
      (Hwatch Hbc) Hresident Hlim_conf) as Hbase.
    assert (Hreentry : solver_query_reentry n F Mconf)
      by exact (solver_base_recovery_false_reentry__api_reentry
                  n F Mconf Hbase Hresident).
    (* cnf_unsat via the ASSUMING route: no `ms_root_level Mconf = 0' needed,
       which `solver_update_ready' could not have supplied. *)
    pose proof Hcert as Hcert0.
    destruct Hcert as [Hent [Hfalse [HCwf Hcert_rest]]].
    assert (Hunsat0 : cnf_unsat n (cnf_with_units F (@nil literal))).
    { exact (assuming_conflict_unsat n F nil nil Mconf C
               Hassuming Hent Hfalse HCwf). }
    assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)).
    { eapply cnf_unsat_units_mono with (A := (@nil literal)).
      - intros x Hx. contradiction.
      - exact HAwf.
      - exact Hunsat0. }
    assert (Hguarded : solver_query_reuse_guard M0 ->
      solver_base_recovery n F Mconf /\ solver_query_reentry n F Mconf /\
      msolver_seed_shadow Mconf).
    { intros _. split; [exact Hbase | split; [exact Hreentry | exact Hseed]]. }
    Exists Mconf raw.
    unfold solver_unsat_arm_at.
    sep_apply (solver_rep_assigns_levels_at_rep
      s Mconf assigns_prop levels_entry solve_wl).
    repeat sep_apply store_int_undef_store_int.
    repeat sep_apply store_ptr_undef_store_ptr.
    entailer_with ltac:(lia).
  - unfold solver_propagation_capacity_raw.
    Intros Mcap. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_derive_solver_solve_incremental_spec_by_solver_solve_spec :
  solver_solve_derive_solver_solve_incremental_spec_by_solver_solve_spec.
Proof.
  unfold solver_solve_derive_solver_solve_incremental_spec_by_solver_solve_spec.
  intros finish begin s entry A F n. Intros.
  pose proof (solver_incremental_update_entry_frame__api_reentry
    s begin finish n F A entry) as Hentry_frame.
  lazymatch type of Hentry_frame with
  | _ |-- ?Frame =>
    assert (Hsplit : solver_incremental_ownership_at s entry **
      assumptions_array n begin finish A |-- Frame) by
      (rewrite <- Hentry_frame; msat_entailer_with ltac:(tauto))
  end.
  sep_apply Hsplit.
  Intros wl.
  match goal with
  | Hfacts : solver_update_ready n F nil entry /\ solver_query_watch_ready entry /\
      msolver_seed_shadow entry /\ solver_query_reuse_guard entry /\
      2 * ms_cap entry <= INT_MAX |- _ =>
      destruct Hfacts as [Hupdate [Hready [Hseed [Hwatch Hbound]]]]
  end.
  Exists wl n F A entry.
  split_pure_spatial.
  - cancel (solver_rep_wl s entry wl).
    cancel (assumptions_array n begin finish A).
    apply derivable1_wand_sepcon_adjoint.
    rewrite orp_sepcon_right. apply derivable1_orp_elim;
      [rewrite orp_sepcon_right; apply derivable1_orp_elim | idtac].
    all: Intros Mret ret.
    (* Group the actual low arm into the exact premise of the checked
       same-return theorem. This retains the low ret as the public witness. *)
    all: pose proof
      (solver_incremental_common_result_from_expanded__api_reentry
        s begin finish n F A entry ret wl Hwatch Hbound) as Hresult.
    all: lazymatch type of Hresult with
      | ?Raw |-- _ =>
        assert (Hraw :
          assumptions_array n begin finish A **
          (solver_rep_wl s Mret wl **
           wlists_undef wl (2 * n) (2 * ms_cap entry)) |-- Raw) by
          (lazymatch goal with
           | Hcase : ?actual_ret = -2 |- _ =>
               cancel (assumptions_array n begin finish A);
               cancel (wlists_undef wl (2 * n) (2 * ms_cap entry));
               rewrite <- derivable1_orp_intros2;
               Exists Mret; msat_entailer_with ltac:(tauto)
           | Hcase : ?actual_ret = 0 |- _ =>
               cancel (assumptions_array n begin finish A);
               cancel (wlists_undef wl (2 * n) (2 * ms_cap entry));
               rewrite <- derivable1_orp_intros1;
               rewrite <- derivable1_orp_intros2;
               Exists Mret; msat_entailer_with ltac:(tauto)
           | Hcase : ?actual_ret = 1 |- _ =>
               cancel (assumptions_array n begin finish A);
               cancel (wlists_undef wl (2 * n) (2 * ms_cap entry));
               rewrite <- derivable1_orp_intros1;
               rewrite <- derivable1_orp_intros1;
               Exists Mret; msat_entailer_with ltac:(tauto)
           end)
      end.
    all: rewrite Hraw.
    all: rewrite Hresult.
    all: Intros Mout.
    all: match goal with
      | Hfacts : solver_public_query_entry ?out_n ?out_F ?out_state /\
          solver_query_reuse_guard ?out_state /\
          solver_update_ready ?out_n ?out_F nil ?out_state /\ _ |- _ =>
          destruct Hfacts as [Hpublic [Hguard [Hupdate_out Hcases]]]
      end.
    (* Four RHS arms now: -2 | 0-with-watch-ready | 0-with-cnf_unsat | 1.
       R-23 splits the old 0 arm on the named continuation alternative. *)
    all: destruct Hcases as
      [[Hret Hsat] | [[Hret [Hunsat [Hpending_out Halt]]] | [Hret Hretry]]];
      [ rewrite <- derivable1_orp_intros2;
        Exists Mout ret; msat_entailer_with ltac:(tauto)
      | destruct Halt as [Hwatch_out | Hunsat_F];
        [ rewrite <- derivable1_orp_intros1;
          rewrite <- derivable1_orp_intros1;
          rewrite <- derivable1_orp_intros2;
          Exists Mout ret; msat_entailer_with ltac:(tauto)
        | rewrite <- derivable1_orp_intros1;
          rewrite <- derivable1_orp_intros2;
          Exists Mout ret; msat_entailer_with ltac:(tauto) ]
      | rewrite <- derivable1_orp_intros1;
        rewrite <- derivable1_orp_intros1;
        rewrite <- derivable1_orp_intros1;
        Exists Mout ret; msat_entailer_with ltac:(tauto) ].
  - split_pures; try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_1 : solver_simplify_which_implies_wit_1.
Proof.
  unfold solver_simplify_which_implies_wit_1. left.
  intros wl lvl physical M A F n s.
  unfold solver_simplify_resumed_pre_at. Intros.
  destruct H as [Heq [Hinv [Hdepth [Hpending Hseed]]]].
  subst M. msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_2 : solver_simplify_which_implies_wit_2.
Proof.
  unfold solver_simplify_which_implies_wit_2. left.
  intros wl lvl physical M A F n s Heq Hinv Hdepth Hpending Hseed.
  subst M. unfold solver_simplify_pre_at.
  msat_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_32 : solver_search_which_implies_wit_32.
Proof.
  unfold solver_search_which_implies_wit_32. left. intros.
  apply solver_simplify_resumed_pre_ordinary__api_reentry.
Qed.
