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

(* solver_qcp_proof_manual_part7.v -- manual VC proofs for these C functions, in file
   order: clause_activity, clause_begin, clause_from_lit, clause_learnt, clause_new,
   clause_setactivity, clause_size, lit_sign, lit_var, solver_analyze, solver_propagate,
   solver_reducedb, solver_search, solver_simplify, solver_solve, sort, sortrnd.
   Within each function the lemmas are grouped by obligation kind (entail / return /
   partial_solve / safety / which_implies) and alphabetical by lemma name, with one
   documented exception: a `Proof. exact proof_of_<keeper>. Qed.` stub has to follow
   its keeper, because the gate requires the keeper to sit earlier in the same file.
   Such stubs stay directly after the obligation whose statement they share;
   search for `exact proof_of_` to find the current keeper references.
   The `(* ===== <function> <kind> wits (N proofs) ===== *)` banners below
   mark each group.
   The Tactic Notation/Ltac helpers shared across several groups are declared next,
   before the first group; a helper used by one obligation only sits immediately above
   that obligation instead. *)

(* Entry step of the analyze resolution loop: the clause scan starts at index 0 with
   empty resolution accumulators.  Shared by the two entail VCs that open the scan
   (wit_10_1_learnt, wit_11_1).  The caller names the solver state and the phase and
   clause it is opening; every other argument of the loop invariant is read off the
   invariant fact itself, which those two names already pin down. *)
Tactic Notation "msat_analyze_scan_entry_p7"
    ident(mact) ident(ph) ident(ccur) ident(cw2) ident(lrn2) :=
  match goal with
  | Hloop : analyze_resolution_loop_inv ?nn ?ff ?aa ?kk mact ?foc ph ?cc ccur ?w2 ?cn ?idx ?pp |- _ =>
    assert (Hphase : ph = AnalyzeInitial) by
      (destruct ph; [ reflexivity | ];
       unfold analyze_resolution_loop_inv in Hloop;
       cbn in Hloop;
       decompose [and ex] Hloop; lia);
    subst ph;
    subst ccur;
    assert (Hcore : analysis_core_equiv mact mact) by
      (unfold analysis_core_equiv; repeat split; reflexivity);
    assert (Hscan :
      analyze_clause_scan_inv nn ff aa kk mact mact foc AnalyzeInitial
        (lits_denote cw2) 0 idx
        (@nil Z) (@nil Z) (@nil literal) (-1)
        (@nil Z) (@nil Z) (@nil literal) w2 cn) by
      (unfold analyze_clause_scan_inv;
       unfold analyze_resolution_loop_inv in Hloop;
       cbn in Hloop;
       destruct Hloop as (Hready & Hind0 & Hwords & Hroot & Htags & Hinit);
       destruct Hinit as (Hp & Hcnt & Hindtail & Hconf & Hptr & Htagged & Hlearnt);
       pose proof Hconf as Hconf_all;
       destruct Hconf as (Hent & Hfalse & HCwf & HCnd & Hex);
       refine (conj Hready _);
       refine (conj Hcore _);
       refine (conj Hind0 _);
       refine (conj Hroot _);
       refine (conj HCwf _);
       refine (conj HCnd _);
       refine (conj _ _);
       [ pose proof (Zlength_nonneg (lits_denote cw2)); lia | ];
       refine (conj _ _);
       [ rewrite Hcnt; reflexivity | ];
       refine (conj Hwords _);
       refine (conj Hlearnt _);
       refine (conj Htags _);
       refine (conj _ _);
       [ rewrite Htagged; simpl; constructor | ];
       cbn;
       repeat split; try assumption; simpl; try lia; try reflexivity);
    assert (Hhdr : clause_hdr_word lrn2 (Zlength cw2) / 2 = Zlength cw2) by
      (apply clause_hdr_word_div2; apply Zlength_nonneg);
    Exists (@nil Z) (@nil Z) (@nil literal) (-1)
           (@nil Z) (@nil Z) (@nil literal);
    entailer_with ltac:(int_auto);
    [ apply Zlength_nonneg
    | unfold analyze_resolution_loop_inv in Hloop; cbn in Hloop; tauto
    | unfold analyze_resolution_loop_inv in Hloop; cbn in Hloop; tauto
    | rewrite zdiv_equiv;
      [ exact Hhdr
      | unfold clause_hdr_word; destruct lrn2;
        pose proof (Zlength_nonneg cw2); lia
      | lia ] ]
  end.

(* One resolution step of the analyze loop: the selected literal [x] leaves the tag
   set [S0] and joins the resolved set, and the clause scan restarts at index 1 on the
   reason clause.  Shared by the two entail VCs that take that step (wit_10_2_learnt,
   wit_11_2).  As above, the caller names the state, phase and clause plus the three
   witnesses the post-condition existentially quantifies. *)
Tactic Notation "msat_analyze_resolve_p7"
    ident(mact) ident(ph) ident(ccur) ident(cw2) ident(lrn2)
    ident(wcap2) ident(opos) ident(aptr) :=
  match goal with
  | Hret : _ = clause_lits_addr ?cc,
    Hloop : analyze_resolution_loop_inv ?nn ?ff ?aa ?kk mact ?foc ph ?cc ccur ?w2 ?cn ?idx ?pp
    |- _ =>
    Left;
    assert (Hphase : ph = AnalyzeSelected) by
      (destruct ph;
       [ unfold analyze_resolution_loop_inv in Hloop; cbn in Hloop; tauto
       | reflexivity ]);
    subst ph; subst ccur;
    pose proof Hloop as Hstep;
    unfold analyze_resolution_loop_inv in Hstep; cbn in Hstep;
    destruct Hstep as
      (Hready & Hind & Hwords & Hroot & Htags &
       S0 & R0 & learnt0 & x & Hp & Hx & Hinx & Htrail & Hrankx &
       Horder & Hlit & Hcnt & Hcntpos & Hc & Hreason & Htarget & Hfocus &
       Hrv & Hent & HwfC & HnodupC & Hinv & Hlearnt & Hperm);
    assert (HndS0 : NoDup S0) by
      (pose proof Hinv as Hinv';
       unfold analyze_inv in Hinv';
       destruct Hinv' as (_ & Hndtags & _);
       unfold analyze_tags in Hndtags;
       eapply NoDup_app_remove_r; exact Hndtags);
    pose proof (zremove_split x) as Hremove;
    destruct (Hremove S0 HndS0 Hinx) as (before & after & HS0 & HremoveS0);
    assert (Hlenremove : cn = Zlength (zremove x S0)) by
      (rewrite HremoveS0, Zlength_app;
       rewrite HS0, !Zlength_app, Zlength_cons in Hcnt; lia);
    assert (Hperm_move :
      Permutation (analyze_tags S0 R0 learnt0)
                  (analyze_tags (zremove x S0) (x :: R0) learnt0)) by
      (unfold analyze_tags;
       rewrite HremoveS0, HS0;
       clear HS0 HremoveS0;
       induction before as [|a before IH];
       [ cbn; exact (Permutation_middle after (R0 ++ map literal_var learnt0) x)
       | cbn; constructor; exact IH ]);
    assert (HClen : 1 <= Zlength (lits_denote cw2)) by
      (unfold reason_valid in Hrv;
       destruct Hrv as (b & d & rx & Hass & Hlev & Hrank & Hsat & Hside);
       destruct (In_Znth_ex literal (lits_denote cw2)
         (satisfying_literal x b) (satisfying_literal x b) Hsat) as (i & Hi & Hnth);
       lia);
    assert (Htailone :
      skipn (Pos.to_nat 1)
        (firstn (Pos.to_nat 1) (lits_denote cw2)) = (@nil literal)) by
      (cbn; apply skipn_all2; rewrite length_firstn; lia);
    assert (Hscan :
      analyze_clause_scan_inv nn ff aa kk mact mact foc AnalyzeSelected
        (lits_denote cw2) 1 idx S0 R0 learnt0 x
        (zremove x S0) (x :: R0) learnt0 w2 cn) by
      (unfold analyze_clause_scan_inv; cbn;
       split; [exact Hready |];
       split; [ unfold analysis_core_equiv; repeat split; reflexivity |];
       split; [exact Hind |];
       split; [exact Hroot |];
       split; [exact HwfC |];
       split; [exact HnodupC |];
       split; [lia |];
       split; [exact Hlenremove |];
       split; [exact Hwords |];
       split; [exact Hlearnt |];
       split; [exact Htags |];
       split; [ eapply Permutation_trans; [exact Hperm | exact Hperm_move] |];
       split; [exact Hcntpos |];
       split; [lia |];
       split; [exact Hinx |];
       split; [exact Hrankx |];
       split; [exact Horder |];
       split; [exact Hinv |];
       split; [exact Hreason |];
       split; [exact Hrv |];
       split; [exact Hent |];
       split;
       [ unfold resolve_S, resolve_new_S; rewrite Htailone; cbn;
         rewrite app_nil_r; reflexivity |];
       split; [reflexivity |];
       unfold resolve_learnt, resolve_new_lits; rewrite Htailone; cbn;
       rewrite app_nil_r; reflexivity);
    Exists wcap2 aptr opos
      S0 R0 learnt0 x (zremove x S0) (x :: R0) learnt0 w2 mact;
    entailer_with ltac:(lia);
    [ rewrite Hret; reflexivity
    | rewrite lits_denote_length in HClen; exact HClen
    | rewrite zdiv_equiv;
      [ apply clause_hdr_word_div2; apply Zlength_nonneg
      | unfold clause_hdr_word; destruct lrn2;
        pose proof (Zlength_nonneg cw2); lia
      | lia ]
    | unfold analysis_core_equiv; repeat split; reflexivity ]
  end.

(* Frame of the propagation loop's finish step: the level array is restored from the
   entry snapshot and the remaining pure residue is discharged from the bound facts.
   Shared by the two finish VCs (wit_34_1, wit_34_2). *)
Tactic Notation "msat_propagate_finish_frame_p7"
    ident(lvl) ident(lvl0) ident(trl) ident(rsn) ident(mfin) :=
  let Hlvl := fresh "H_lvl_finish" in
  bind_fact ( lvl = lvl0 ) as Hlvl;
  Exists rsn trl mfin;
  split_pure_spatial;
  [ rewrite <- Hlvl; set_String_name; sepcon_assoc_change; sepcon_cancel
  | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia ].

(* Assumption loop, propagation-succeeded step: the loop advances to assumption
   [k + 1] in the state the propagation returned.  The caller selects the disjunct
   (Left/Right) its own post-condition needs before calling. *)
Tactic Notation "msat_solve_assumption_prop_step_p7"
    ident(nn) ident(ff) ident(aa) ident(raw) ident(kk) ident(mprop)
    ident(endv) ident(beg) :=
  let Hsucc := fresh "H_assumption_propagation_success" in
  let Hend := fresh "H_endvar_pre" in
  bind_fact ( assumption_propagation_success nn ff aa raw (kk + 1) mprop ) as Hsucc;
  bind_fact ( endv = beg + Zlength raw * sizeof ( INT ) ) as Hend;
  Exists raw (kk + 1) mprop;
  unfold assumption_propagation_success in Hsucc;
  destruct Hsucc as (Hinv & Hqh & Hpend & Hseed);
  entailer_with lia;
  rewrite Hend;
  entailer_with lia.

(* Assumption loop, assumption-already-true step: the loop advances to assumption
   [k + 1] without changing the solver state.  The caller selects the disjunct its
   own post-condition needs before calling. *)
Tactic Notation "msat_solve_assumption_true_step_p7"
    ident(nn) ident(ff) ident(aa) ident(raw) ident(kk) ident(mcur)
    ident(endv) ident(beg) :=
  let Hadv := fresh "H_assumption_true_advance" in
  let Hend := fresh "H_endvar_pre" in
  bind_fact ( assumption_true_advance nn ff aa raw kk mcur ) as Hadv;
  bind_fact ( endv = beg + Zlength raw * sizeof ( INT ) ) as Hend;
  Exists raw (kk + 1) mcur;
  unfold assumption_true_advance in Hadv;
  entailer_with lia;
  rewrite Hend;
  entailer_with lia.

(* The four search safety VCs that need the learnt-vector / qtail gap out of the
   solver invariant.  Their contexts hold more than one [msolver_inv] fact (counted in
   solver_qcp_goal.v: two for wit_44 and wit_45, on Mclean and Mstable; three for wit_46
   and wit_47, on Mclean, Msimplify and Mstable), so the match below selects candidates by
   shape and Ltac backtracks over them until the shared closer discharges the goal.  Call
   sites therefore never re-spell the five invariant arguments; an editor who adds another
   invariant fact to these VCs should re-check that the closer still picks a usable one. *)
Ltac msat_search_safety_qtail_gap_p7 :=
  Unfold; left; intros; pre_process_default;
  match goal with
  | H : msolver_inv _ _ _ _ _ |- _ => msat_search_bound_learnts_qtail_gap H
  end.

(* Watch-vector bounds for the two clause_new pure VCs that read the watch list of
   the negated first literal: the bound comes out of the vector's own representation
   predicate, and the goal is closed from it. *)
Tactic Notation "msat_clause_new_watch_bounds_p7"
    ident(wptr) ident(wwords) ident(cwords) ident(mstage) :=
  let Hb := fresh "Hbounds" in
  prop_apply_p (vecp_rep_bounds__clause_new wptr wwords
    (Znth (lit_neg_c (Znth 0 cwords 0)) (ms_wcaps mstage) 1));
  Intros_p Hb;
  entailer_with ltac:(lia).

(* Binds the scanned watch's assignment-cell equation by its statement and closes the
   goal with it.  The equation is indexed [var - 0] while the goal is indexed [var],
   and the shared closer normalises that before the arithmetic *)
Tactic Notation "msat_propagate_scan_assign_cell_p7" ident(var_idx) ident(mstate) :=
  let HZ := fresh "H_Znth" in
  bind_fact ( Znth (var_idx - 0) (mt_assigns (ms_core mstate)) 0 = 1 + 1 - 1 ) as HZ;
  msat_propagate_close_scan_assign_cell HZ var_idx.


(* Third watch room: bumping the cap of watch list 1 to [cap1] turns clause_new's
   two-room reservation into a three-room one; only the two watch indices, their
   disequality and the new cap's size premise are needed. *)
Lemma msat_clause_new_rooms_bump_p7 :
  forall (M : msolver) (words : list Z) (sel lcap cap0 cap1 : Z),
    0 <= lit_neg_c (Znth 0 words 0) <
      Zlength (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M)) ->
    0 <= lit_neg_c (Znth 1 words 0) <
      Zlength (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M)) ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    Zlength (Znth (lit_neg_c (Znth 1 words 0)) (ms_wm M) nil) < cap1 ->
    clause_new_reserved_rooms_gen 2 words
      (msolver_with_clause_caps_gen M lcap
        (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M)) sel) sel ->
   clause_new_reserved_rooms_gen 3 words
    (msolver_with_clause_caps_gen M lcap
      (replace_Znth (lit_neg_c (Znth 1 words 0))
        cap1
        (replace_Znth (lit_neg_c (Znth 0 words 0))
          cap0 (ms_wcaps M))) sel) sel.
Proof.
  intros M words sel lcap cap0 cap1 Hidx0 Hidx1 H_lit_neg_c H_Zlength
    H_clause_new_reserved_rooms.
  unfold clause_new_reserved_rooms_gen in H_clause_new_reserved_rooms |- *.
    rewrite ?sel_db_with_caps, ?sel_cap_with_caps
      in H_clause_new_reserved_rooms |- *.
    rewrite ?wm_with_caps, ?wcaps_with_caps
      in H_clause_new_reserved_rooms |- *.
    rewrite (Znth_replace_Znth_Same 1
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M))
      (lit_neg_c (Znth 1 words 0)) cap1 Hidx1).
    rewrite (Znth_replace_Znth_Diff 1
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M))
      (lit_neg_c (Znth 1 words 0))
      (lit_neg_c (Znth 0 words 0)) cap1
      Hidx1 Hidx0 ltac:(lia)).
    split.
    - intros _. apply (proj1 H_clause_new_reserved_rooms). lia.
    - split.
      + intros _. apply (proj1 (proj2 H_clause_new_reserved_rooms)). lia.
      + intros _. exact H_Zlength.
Qed.

(* Raising watch list 1's cap keeps clause_new's stage-ready package: the solver
   invariant survives a capacity-only update and the caps-progress disjunct moves
   to its third arm. *)
Lemma msat_clause_new_stage_ready_bump_p7 :
  forall (n : Z) (F : cnf) (A_arr A_inst : list literal) (M : msolver)
         (words : list Z) (sel root lcap cap0 cap1 : Z),
    sel = 0 \/ sel = 1 ->
    clause_new_stage_ready_root n F A_arr A_inst M
      (msolver_with_clause_caps_gen M lcap
        (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M)) sel)
      words sel root ->
    clause_new_stage_ready_root n F A_arr A_inst M
      (msolver_with_clause_caps_gen M lcap
        (replace_Znth (lit_neg_c (Znth 1 words 0)) cap1
          (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M))) sel)
      words sel root /\
    solver_support_inv n F A_arr A_inst root
      (msolver_with_clause_caps_gen M lcap
        (replace_Znth (lit_neg_c (Znth 1 words 0)) cap1
          (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M))) sel) /\
    clause_new_caps_progress_gen M words
      (msolver_with_clause_caps_gen M lcap
        (replace_Znth (lit_neg_c (Znth 1 words 0)) cap1
          (replace_Znth (lit_neg_c (Znth 0 words 0)) cap0 (ms_wcaps M))) sel) sel.
Proof.
  intros n F A_arr A_inst M words sel root lcap cap0 cap1 Hsel H_clause_new_stage_ready.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hcert as Hcert_full.
  assert (Hlen :
    Zlength (replace_Znth
      (lit_neg_c (Znth 1 words 0)) cap1
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M))) =
    Zlength (ms_wcaps
      (msolver_with_clause_caps_gen M lcap
        (replace_Znth (lit_neg_c (Znth 0 words 0))
          cap0 (ms_wcaps M)) sel))).
  { cbn. apply Zlength_replace_Znth. }
  pose proof (solver_support_inv_with_clause_caps__api_reentry
    n F A_arr
    A_inst root
    (msolver_with_clause_caps_gen M lcap
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M)) sel) lcap
    (replace_Znth (lit_neg_c (Znth 1 words 0))
      cap1
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M))) sel Hsel Hinv Hlen) as Hinv'.
  pose proof (solver_shape_with_clause_caps__api_reentry
    (msolver_with_clause_caps_gen M lcap
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M)) sel) lcap
    (replace_Znth (lit_neg_c (Znth 1 words 0))
      cap1
      (replace_Znth (lit_neg_c (Znth 0 words 0))
        cap0 (ms_wcaps M))) sel Hphysical Hlen) as Hphysical'.
  rewrite with_caps_gen_idem in Hphysical'.
  rewrite with_caps_gen_idem in Hinv'.
  assert (Hcaps' : clause_new_caps_progress_gen M
    words
    (msolver_with_clause_caps_gen M lcap
      (replace_Znth (lit_neg_c (Znth 1 words 0))
        cap1
        (replace_Znth (lit_neg_c (Znth 0 words 0))
          cap0 (ms_wcaps M))) sel) sel).
  { right. right. right.
    exists lcap, cap0, cap1. reflexivity. }
  assert (Hready' : clause_new_stage_ready_root n
    F A_arr A_inst
    M
    (msolver_with_clause_caps_gen M lcap
      (replace_Znth (lit_neg_c (Znth 1 words 0))
        cap1
        (replace_Znth (lit_neg_c (Znth 0 words 0))
          cap0 (ms_wcaps M))) sel)
    words sel root).
  { unfold clause_new_stage_ready_root.
    split; [exact Hphysical' |].
    split; [exact Hwords |].
    split; [exact Hwords_bound |].
    split; [exact Hcaps' |].
    split.
    - exact Hinv'.
    - split; [exact Hpending |].
      split; [exact Hseed | exact Hcert_full]. }
  split; [exact Hready' |].
  split; [exact Hinv' | exact Hcaps'].
Qed.


(* ---- shared steps of the solver_analyze clause-scan tag step (part 7) ----
   [proof_of_solver_analyze_entail_wit_12_1_learnt] below re-establishes
   [analyze_clause_scan_inv] after the tag step of solver_analyze's inner clause
   scan, on the AnalyzeSelected exit that copies the order heap.  Related
   clause-scan obligations live in part 5; every step this exit shares with them is
   declared once in solver_qcp_proof_common.v, section 9.  What remains in this
   block are the four facts this exit needs and the siblings do not: the
   scanned literal sits at the CURRENT decision level, the cancel-ready package
   travels along a heap PERMUTATION rather than an order-position condition, the
   scanned variable is untagged in the general scan position, and the resolved
   candidate set -- not the learnt clause -- is what grows.
   Every ghost name and every hypothesis a tactic block needs is an argument: an
   [Ltac] body may only mention globals and its own parameters. *)

(* The scanned literal [l] of the selected variable's reason clause sits at the
   CURRENT decision level.  [reason_valid] gives it a level and a trail rank;
   the trail well-formedness turns the level cell that the C code just read back
   ([Hraw]: the cell equals the number of decision levels) into the statement
   that this rank's level IS the current one.  Both boolean level flags the
   resolved-set step reads follow. *)
Lemma msat_analyze_e12_scan_lit_current_p7 :
  forall (n : Z) (M : msolver) (C : clause) (l : literal) (v x : Z),
    reason_valid (msolver_view n M) x C ->
    In l C ->
    literal_var l = v ->
    v <> x ->
    mtrail_wf n (ms_core M) ->
    Znth v (mt_levels (ms_core M)) 0 = Zlength (mt_lim (ms_core M)) ->
    at_current_level_b (msolver_view n M) l = true /\
    below_current_b (msolver_view n M) l = false.
Proof.
  intros n M C l v x Hvalid Hin Ev Hne Htrailwf Hraw. subst v.
  destruct Hvalid as (bx & dx & rx & Hassx & Hlevx & Hrankx & Hsatx & Hsides).
  destruct (Hsides l Hin Hne) as
    (Hlfalse & dq & rq & Hlevq & Hrankq & Hdq & Hrq).
  assert (Hpos : trail_pos (ms_core M) (literal_var l) = Some rq)
    by exact Hrankq.
  assert (Hlevel : level_of (msolver_view n M) (literal_var l) =
    Some (current_level (msolver_view n M))).
  {
    pose proof (trail_pos_bound (ms_core M) (literal_var l) rq Hpos) as Hrqb.
    pose proof (mtw_levels_agree Htrailwf (Z.of_nat rq) ltac:(lia)) as Hagree.
    rewrite (trail_pos_var (ms_core M) (literal_var l) rq Hpos) in Hagree.
    change
      (option_map
        (fun k => level_of_index (ms_core M) (Z.of_nat k))
        (trail_pos (ms_core M) (literal_var l)) =
       Some (Zlength (mt_lim (ms_core M)))).
    rewrite Hpos. cbn. rewrite <- Hagree. f_equal. exact Hraw.
  }
  split.
  - apply (proj2 (at_current_level_b_true_iff _ _)). exact Hlevel.
  - destruct (below_current_b (msolver_view n M) l) eqn:Hb; [|reflexivity].
    apply below_current_b_true_iff in Hb.
    destruct Hb as (d & Hd & Hdrange).
    assert (Hdcur : d = current_level (msolver_view n M)) by congruence.
    subst d. lia.
Qed.

(* The tag step keeps [analysis_cancel_ready] when the fresh order heap is
   presented as a PERMUTATION of the old one (the exit that copies the heap
   rather than the one that only rewrites order positions): a permutation is an
   inclusion, and the missing-variable coverage of the old heap transports along
   an inclusion between two well-formed heaps. *)
Lemma msat_analyze_e12_tag_ready_perm_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z)
         (tags tagged : list Z) (tagged_cap : Z) (activity : list fp64)
         (orderpos order : list Z) (var_inc : fp64),
    analysis_cancel_ready n F A_arr K M focus ->
    order_heap_wf n order orderpos ->
    Permutation (ms_order M) order ->
    analysis_cancel_ready n F A_arr K
      (analyze_tag_step_msolver M tags tagged tagged_cap activity orderpos
         order var_inc) focus.
Proof.
  intros n F A_arr K M focus tags tagged tagged_cap activity orderpos order
    var_inc Hready Hheap Hperm.
  destruct Hready as
    (Mentry & Hcancel_full & HequivEntry & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  assert (HheapNow :
    heap_wf n {| mh_heap := order; mh_orderpos := orderpos |})
    by exact Hheap.
  assert (HheapIncl : incl (ms_order M) order).
  { intros u Hin. eapply Permutation_in; [exact Hperm | exact Hin]. }
  assert (HcoversNow :
    heap_covers n {| mh_heap := order; mh_orderpos := orderpos |}
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M))).
  {
    unfold heap_covers in Hcovers |- *.
    intros u Hu Hmissing.
    apply Hcovers; [exact Hu |].
    eapply heap_wf_incl_missing_mono;
      [exact Hheapwf | exact HheapNow | exact HheapIncl | exact Hu |
       exact Hmissing].
  }
  unfold analysis_cancel_ready.
  exists Mentry.
  refine (conj Hcancel_full _).
  refine (conj _ _).
  { apply analysis_core_equiv_analyze_tag_step. exact HequivEntry. }
  refine (conj _ _).
  { rewrite msolver_heap_analyze_tag_step. exact HheapNow. }
  refine (conj _ _).
  { cbn. exact HcoversNow. }
  refine (conj _ _).
  { unfold current_reasonless_earliest in *. cbn in *. exact Hearliest. }
  refine (conj _ _).
  { cbn. exact Hfocuslev. }
  cbn. exact Hclainc.
Qed.

(* A variable absent from the RESOLVED tag sets is absent from the INITIAL ones,
   in the general scan position: the resolved [S] drops only the pivot [x] and
   keeps every other initial candidate, the resolved trail only prepends [x],
   and the resolved learnt list only extends the initial one.  Stated as the
   [zmem] boolean the resolved-set step consumes. *)
Lemma msat_analyze_e12_notin_initial_p7 :
  forall (a : cdcl_view) (C : clause) (j : Z) (x v : Z)
         (S0 R0 Sc Rc : list Z) (L0 Lc : clause),
    ~ In v (analyze_tags Sc Rc Lc) ->
    v <> x ->
    Sc = resolve_S a x (sublist 1 j C) S0 R0 L0 ->
    Rc = x :: R0 ->
    Lc = resolve_learnt a (sublist 1 j C) S0 R0 L0 ->
    zmem v (analyze_tags S0 R0 L0) = false.
Proof.
  intros a C j x v S0 R0 Sc Rc L0 Lc Hnot Hne HS HR HL.
  apply zmem_false_iff. intro Hin. apply Hnot.
  unfold analyze_tags in Hin |- *.
  rewrite !in_app_iff in Hin |- *.
  destruct Hin as [HinS | [HinR | HinL]].
  - left. rewrite HS. unfold resolve_S.
    apply in_or_app. left. apply In_zremove_iff. split; assumption.
  - right. left. rewrite HR. right. exact HinR.
  - right. right. rewrite HL. unfold resolve_learnt.
    rewrite map_app. apply in_or_app. left. exact HinL.
Qed.

(* One tag step of the AnalyzeSelected scan: the scanned literal [l] is at the
   current level ([Hat]) and therefore not below it ([Hbelow]), and its variable
   [v] was not tagged initially ([Hmem]), so the resolved candidate set grows by
   exactly [v] while the resolved learnt clause is unchanged.  [Hsub] is the
   scanned prefix growing by [l]. *)
Lemma msat_analyze_e12_resolve_step_tag_p7 :
  forall (a : cdcl_view) (C : clause) (j : Z) (l : literal) (v x : Z)
         (S0 R0 Sc : list Z) (L0 Lc : clause),
    literal_var l = v ->
    sublist 1 (j + 1) C = sublist 1 j C ++ (l :: nil) ->
    at_current_level_b a l = true ->
    below_current_b a l = false ->
    zmem v (analyze_tags S0 R0 L0) = false ->
    Sc = resolve_S a x (sublist 1 j C) S0 R0 L0 ->
    Lc = resolve_learnt a (sublist 1 j C) S0 R0 L0 ->
    Sc ++ (v :: nil) = resolve_S a x (sublist 1 (j + 1) C) S0 R0 L0 /\
    Lc = resolve_learnt a (sublist 1 (j + 1) C) S0 R0 L0.
Proof.
  intros a C j l v x S0 R0 Sc L0 Lc Ev Hsub Hat Hbelow Hmem HS HL.
  split.
  - symmetry. unfold resolve_S, resolve_new_S in HS |- *.
    rewrite Hsub, filter_app, map_app, filter_app.
    cbn [filter map]. rewrite Hat. cbn [filter map negb].
    rewrite Ev. rewrite Hmem. cbn [filter map negb].
    rewrite app_assoc. rewrite <- HS. reflexivity.
  - symmetry. unfold resolve_learnt, resolve_new_lits in HL |- *.
    rewrite Hsub, filter_app. cbn [filter].
    rewrite Hbelow. cbn [filter negb andb]. rewrite app_nil_r.
    exact (eq_sym HL).
Qed.


(* Everything solver_analyze's entry VC needs about the state it is called on:
   the cancel-ready package carries the trail, level-limit and database
   well-formedness of [M] itself, and rebuilds [solver_shape M] as soon as the
   four array lengths that only the spatial part knows are supplied. *)
Lemma msat_analyze_cancel_ready_core_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z),
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    Zlength (mt_lim (ms_core M)) <= n /\
    0 <= ms_root_level M /\
    Zlength (mt_trail (ms_core M)) = ms_qtail M /\
    ms_binary M <> 0 /\
    db_wf n (msolver_db M) /\
    (Zlength (ms_orderpos M) = ms_size M ->
     Zlength (ms_activity M) = ms_size M ->
     Zlength (ms_tags M) = ms_size M ->
     Zlength (ms_stats M) = 11 ->
     solver_shape M).
Proof.
  intros n F A_arr K M focus H_analysis_cancel_ready.
  pose proof H_analysis_cancel_ready as Hready.
  destruct Hready as [Mbase [Hcancel [Hequiv _]]].
  destruct Hcancel as [[_ Hinv] _].
  assert (Hshape_base : solver_shape Mbase).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_shape Hinv).
    - exact (msa_shape Hinv).
  }
  assert (Htrail_base : mtrail_wf n (ms_core Mbase)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_trail_wf Hinv).
    - exact (msa_trail_wf Hinv).
  }
  assert (Hlim_base : Zlength (mt_lim (ms_core Mbase)) <= n).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_level_bound Hinv).
    - exact (msa_level_bound Hinv).
  }
  assert (Hdb_base : db_wf n (msolver_db Mbase)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hinv.
    - exact (msw_db_wf Hinv).
    - exact (msa_db_wf Hinv).
  }
  assert (Hqtail_eq : ms_qtail M = ms_qtail Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hcore_eq : ms_core M = ms_core Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hroot_eq : ms_root_level M = ms_root_level Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hbinary_eq : ms_binary M = ms_binary Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hprob_eq : ms_prob M = ms_prob Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Hlearnt_eq : ms_learnt M = ms_learnt Mbase)
    by (unfold analysis_core_equiv in Hequiv; tauto).
  assert (Htrail : mtrail_wf n (ms_core M)).
  { rewrite Hcore_eq. exact Htrail_base. }
  assert (Hlim : Zlength (mt_lim (ms_core M)) <= n).
  { rewrite Hcore_eq. exact Hlim_base. }
  assert (Hroot_nonnegative : 0 <= ms_root_level M).
  {
    assert (0 <= ms_root_level Mbase)
      by (unfold solver_shape in Hshape_base; tauto).
    rewrite Hroot_eq. assumption.
  }
  assert (Htrail_length :
    Zlength (mt_trail (ms_core M)) = ms_qtail M).
  {
    assert (Zlength (mt_trail (ms_core Mbase)) = ms_qtail Mbase)
      by (unfold solver_shape in Hshape_base; tauto).
    rewrite Hcore_eq, Hqtail_eq. assumption.
  }
  assert (Hbinary_nonzero : ms_binary M <> 0).
  {
    assert (ms_binary Mbase <> 0)
      by (unfold solver_shape in Hshape_base; tauto).
    rewrite Hbinary_eq. assumption.
  }
  assert (Hdb : db_wf n (msolver_db M)).
  {
    unfold msolver_db in *.
    rewrite Hprob_eq, Hlearnt_eq.
    exact Hdb_base.
  }
  split; [exact Htrail |].
  split; [exact Hlim |].
  split; [exact Hroot_nonnegative |].
  split; [exact Htrail_length |].
  split; [exact Hbinary_nonzero |].
  split; [exact Hdb |].
  intros Horder_shape Hactivity_shape Htags_shape Hstats_shape.
  unfold solver_shape in Hshape_base |- *.
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Eprobcap & Elearntcap & Ebinary &
     Ebinarylits & Ewm & Ewcaps & Elimcap & Emodel & Emodelcap &
     Ecladecay & Eseed & Ependingq & Epending & Esimpassigns &
     Esimpprops).
  rewrite Horder_shape, Hactivity_shape, Htags_shape, Hstats_shape,
    Esize, Ecap, Eqtail, Ecore, Eroot, Ewords, Ebinary,
    Ebinarylits, Ewm, Ewcaps, Ependingq, Epending.
  tauto.
Qed.


(* The semantic content of the analysis cancel-ready package for the state the
   selected-reason step runs on: the trail is well formed, the CDCL view is
   stable, the trail is implied by the formula, and every root-level assignment
   is a unit consequence.  All four transfer from the propagation entry state
   through [analysis_core_equiv], which pins [ms_core] and the clause halves. *)
Lemma msat_analyze_e7_ready_semantics_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (focus : Z),
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    stable_view (msolver_view n M) /\
    trail_implied F (ms_core M) /\
    (forall y b,
       assignment (msolver_view n M) y = Some b ->
       level_of (msolver_view n M) y = Some 0 ->
       entails_clause F (satisfying_literal y b :: nil)).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof Hready as Hready_copy.
  unfold analysis_cancel_ready in Hready_copy.
  destruct Hready_copy as
    (Mentry & Hcancel & Hequiv & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  unfold propagation_cancel_ready in Hcancel.
  destruct Hcancel as
    (Hweak & Hprop & Hfocuswf & Hprocessed & Hentryfocus & Hfrontier &
     Hentryheap & Hentrycovers & Hentryearliest).
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as (Hcaproot & Hweak).
  assert (Hsem_entry :
    mtrail_wf n (ms_core Mentry) /\
    stable_view (msolver_view n Mentry) /\
    trail_implied F (ms_core Mentry)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (conj (msw_trail_wf Hweak)
        (conj (msw_stable Hweak) (msw_trail_impl Hweak))).
    - exact (conj (msa_trail_wf Hweak)
        (conj (msa_stable Hweak) (msa_trail_impl Hweak))).
  }
  destruct Hsem_entry as (Htrailwf_entry & Hstable_entry & Htrailimpl_entry).
  pose proof Hequiv as Hequiv_fields.
  unfold analysis_core_equiv in Hequiv_fields.
  destruct Hequiv_fields as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason & Eprob &
     Elearnt & Erest).
  assert (Hview : msolver_view n M = msolver_view n Mentry).
  {
    unfold msolver_view, view_of, msolver_clauses, msolver_db.
    rewrite Ecore, Ereason, Eprob, Elearnt.
    reflexivity.
  }
  assert (Htrailwf : mtrail_wf n (ms_core M)).
  { rewrite Ecore. exact Htrailwf_entry. }
  assert (Hstable : stable_view (msolver_view n M)).
  { rewrite Hview. exact Hstable_entry. }
  assert (Htrailimpl : trail_implied F (ms_core M)).
  { rewrite Ecore. exact Htrailimpl_entry. }
  destruct Hstable as (Hgrounded & Hclosed).
  assert (Hrootunit :
    forall y b,
      assignment (msolver_view n M) y = Some b ->
      level_of (msolver_view n M) y = Some 0 ->
      entails_clause F (satisfying_literal y b :: nil)).
  {
    intros y b Hass Hlev0.
    destruct (Hgrounded y b Hass) as
      (d & r & Hlevd & Hrank & Hreason_origin).
    assert (Hd : d = 0) by congruence. subst d.
    change (trail_pos (ms_core M) y = Some r) in Hrank.
    pose proof (trail_pos_bound (ms_core M) y r Hrank) as Hrbound.
    assert (Hri :
      0 <= Z.of_nat r < Zlength (mt_trail (ms_core M))) by lia.
    pose proof (trail_pos_var (ms_core M) y r Hrank) as Hvar.
    unfold trail_var in Hvar.
    pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
      (mtw_trail_lits Htrailwf) Hri) as Hlwf.
    pose proof (lit_var_c_in_range n
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) Hlwf)
      as Hvrange.
    pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
      (mtw_trail_true Htrailwf) Hri) as Htrue.
    cbn beta in Htrue.
    rewrite Hvar in Htrue.
    change (mt_pv (ms_core M) y = Some b) in Hass.
    rewrite mt_pv_nonneg in Hass by lia.
    rewrite Htrue, lbool_val_lit_sig in Hass.
    inversion Hass. subst b.
    change
      (option_map
         (fun k => level_of_index (ms_core M) (Z.of_nat k))
         (trail_pos (ms_core M) y) = Some 0) in Hlev0.
    rewrite Hrank in Hlev0. cbn in Hlev0.
    assert (Hlevelindex :
      level_of_index (ms_core M) (Z.of_nat r) = 0) by congruence.
    pose proof (Htrailimpl (Z.of_nat r)
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)
      Hri eq_refl) as Hent.
    rewrite Hlevelindex in Hent.
    unfold decisions_upto, ztake, cnf_with_units in Hent. cbn in Hent.
    rewrite app_nil_r in Hent.
    rewrite lit_denote_satisfying, Hvar in Hent.
    exact Hent.
  }
  exact (conj Htrailwf
    (conj (conj Hgrounded Hclosed) (conj Htrailimpl Hrootunit))).
Qed.

(* One unpacking of the selected-reason loop invariant.  The invariant names its
   own resolution triple existentially, so the first job is to prove that its
   selected variable is the VC's [x] (both reason words are the same tagged
   word, and a tagged word determines its owner) and to transport every field
   onto [x] and onto the VC's [S0]/[R0]/[learnt0].  What comes out is the whole
   set of facts the two tag-step arms share: the two-literal shape of the reason
   clause, the reverse-trail order of the pending set, the resolved invariant
   for the next step, the rank bounds on the pending and resolved sets, and the
   range of the trail word the backward scan is about to read. *)
Lemma msat_analyze_e7_select_bridge_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver)
         (focus c ind cnt p x : Z) (C : clause) (words S0 R0 : list Z)
         (learnt0 : clause),
    analyze_resolution_loop_inv n F A_arr K M focus AnalyzeSelected
      c C words cnt ind p ->
    reason_target_wf n M x c C ->
    is_tag c = msat_true ->
    In x S0 ->
    cnt + 1 = Zlength S0 ->
    analyze_inv F (msolver_view n M) S0 R0 learnt0 ->
    Permutation (ms_tagged M) (analyze_tags S0 R0 learnt0) ->
    solver_shape M ->
    mtrail_wf n (ms_core M) ->
    stable_view (msolver_view n M) ->
    (forall y b,
       assignment (msolver_view n M) y = Some b ->
       level_of (msolver_view n M) y = Some 0 ->
       entails_clause F (satisfying_literal y b :: nil)) ->
    C = lit_denote (trail_lit_of (ms_core M) x) ::
        literal_neg (lit_denote (tag_lit c)) :: nil /\
    (forall s, In s S0 -> s <> x -> rank_lt (msolver_view n M) s x) /\
    assignment_rank (msolver_view n M) x = Some (Z.to_nat (ind + 1)) /\
    reason_valid (msolver_view n M) x C /\
    entails_clause F C /\
    NoDup (map literal_var C) /\
    analyze_inv F (msolver_view n M)
      (resolve_S (msolver_view n M) x C S0 R0 learnt0) (x :: R0)
      (resolve_learnt (msolver_view n M) C S0 R0 learnt0) /\
    (forall y, In y S0 -> y <> x -> exists r,
       assignment_rank (msolver_view n M) y = Some r /\
       Z.of_nat r <= ind) /\
    (forall y, In y (x :: R0) -> exists r,
       assignment_rank (msolver_view n M) y = Some r /\
       ind < Z.of_nat r) /\
    analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
    0 <= ind < ms_qtail M /\
    1 <= Zlength words <= n /\
    ms_root_level M < Zlength (mt_lim (ms_core M)) /\
    0 <= lit_var_c (Znth ind (mt_trail (ms_core M)) 0) < n /\
    0 <= x < n /\
    lit_var_c (tag_lit c) <> x.
Proof.
  intros n F A_arr K M focus c ind cnt p x C words S0 R0 learnt0
    Hloop Htargetx Htag HinS Hcnt Hinv Hperm Hshape Htrailwf Hstable
    Hrootunit.
  destruct Hstable as (Hgrounded & Hclosed).
  unfold analyze_resolution_loop_inv in Hloop. cbn in Hloop.
  destruct Hloop as
    (Hready & Hind & Hwords & Hroot & Htags &
     Sa & Ra & La & xa & Hpne & Hxa & Hina & Htrail & Hrankxa &
     Hordera & Hlita & Hcnta & Hcntposa & Hca & HreasA & HtargetA &
     HfocusA & HvalidA & HentA & HCwfA & HCndA & HinvA & HwordsA &
     HpermA).
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as
    (Hsizecur & Hmatch & Hbinary).
  assert (Htagged_source : forall v,
    reason_target_wf n M v c C ->
    0 <= v < n /\ c = Znth v (ms_reason_words M) 0 /\
    C = lit_denote (trail_lit_of (ms_core M) v) ::
        literal_neg (lit_denote (tag_lit c)) :: nil).
  { intros v Htarget.
    unfold reason_target_wf in Htarget.
    destruct Htarget as (Hrange & Hword & Hnonzero & Hreason & Hkind).
    destruct Hkind as [(Htagged & Hpositive & Hlitwf) |
                      (co & Hnotag & Hnotbinary & Hin & Hdenote)].
    - assert (Hvn : 0 <= v < n) by lia.
      pose proof (Hmatch v Hvn) as Hcodec.
      rewrite <- Hword in Hcodec.
      pose proof (reason_word_ok_tag (ms_core M) v (msolver_db M) c
        (ms_reason_of M v) Hpositive Htag Hcodec) as Hclause.
      rewrite Hreason in Hclause.
      split; [exact Hvn |]. split; [exact Hword | congruence].
    - rewrite Htag in Hnotag. discriminate. }
  destruct (Htagged_source xa HtargetA) as (HrangeAn & HwordA & HCshapeA).
  destruct (Htagged_source x Htargetx) as (HrangeXn & HwordX & HCshapeX).
  assert (Hhead :
    lit_denote (trail_lit_of (ms_core M) xa) =
    lit_denote (trail_lit_of (ms_core M) x)) by congruence.
  pose proof (f_equal literal_var Hhead) as Howner.
  rewrite !lit_var_c_denote in Howner.
  rewrite !trail_lit_of_var in Howner by lia.
  subst xa.
  assert (HpermAS :
    Permutation (analyze_tags Sa Ra La) (analyze_tags S0 R0 learnt0)).
  {
    eapply Permutation_trans.
    - apply Permutation_sym. exact HpermA.
    - exact Hperm.
  }
  assert (HlenAS : Zlength Sa = Zlength S0) by lia.
  pose proof
    (analyze_inv_rank_partition_unique__analyze
      F (msolver_view n M) Sa Ra La S0 R0 learnt0
      HinvA Hinv HpermAS HlenAS) as HmembersAS.
  assert (Horder0 :
    forall s, In s S0 -> s <> x ->
      rank_lt (msolver_view n M) s x).
  {
    intros s Hs Hne.
    rewrite <- Howner.
    apply Hordera.
    - apply (proj2 (HmembersAS s)). exact Hs.
    - rewrite Howner. exact Hne.
  }
  rewrite Howner in HvalidA, HreasA, Hrankxa.
  pose proof HvalidA as Hvalid_fields.
  destruct Hvalid_fields as
    (bx & dx & rx & Hassx & Hlevx & Hrankx & Hsatx & Hsidesx).
  assert (Hreason_view :
    reason_of (msolver_view n M) x = Some C).
  {
    change (trail_pos (ms_core M) x = Some rx) in Hrankx.
    change
      ((match trail_pos (ms_core M) x with
        | Some _ => ms_reason_of M x
        | None => None
        end) = Some C).
    rewrite Hrankx. exact HreasA.
  }
  assert (HinvNew :
    analyze_inv F (msolver_view n M)
      (resolve_S (msolver_view n M) x C S0 R0 learnt0)
      (x :: R0)
      (resolve_learnt (msolver_view n M) C S0 R0 learnt0)).
  {
    eapply analyze_resolve_step;
      [exact Hclosed | exact Hrootunit | exact Hinv | exact HinS |
       exact Hreason_view | exact HvalidA | exact HentA | exact HCndA |
       exact Horder0].
  }
  assert (HpendS :
    forall y, In y S0 -> y <> x -> exists r,
      assignment_rank (msolver_view n M) y = Some r /\
      Z.of_nat r <= ind).
  {
    intros y HyS Hyx.
    destruct (Horder0 y HyS Hyx) as (ry & rx' & Hry & Hrx' & Hlt).
    change (trail_pos (ms_core M) x = Some rx') in Hrx'.
    rewrite Hrankxa in Hrx'. inversion Hrx'. subst rx'.
    exists ry. split; [exact Hry |].
    apply Nat2Z.inj_lt in Hlt.
    rewrite Z2Nat.id in Hlt by lia. lia.
  }
  pose proof Hinv as Hinv0_rank_fields.
  unfold analyze_inv in Hinv0_rank_fields.
  destruct Hinv0_rank_fields as
    (_ & _ & _ & _ & _ & HrankR0 & _).
  rewrite Forall_forall in HrankR0.
  assert (HresolvedRanks :
    forall y, In y (x :: R0) -> exists r,
      assignment_rank (msolver_view n M) y = Some r /\
      ind < Z.of_nat r).
  {
    intros y Hy. destruct Hy as [Hy | Hy].
    - subst y. exists (Z.to_nat (ind + 1)). split.
      + exact Hrankxa.
      + rewrite Z2Nat.id by lia. lia.
    - specialize (HrankR0 y Hy x HinS).
      destruct HrankR0 as (rx' & ry & Hrx' & Hry & Hlt).
      change (trail_pos (ms_core M) x = Some rx') in Hrx'.
      rewrite Hrankxa in Hrx'. inversion Hrx'. subst rx'.
      exists ry. split; [exact Hry |].
      apply Nat2Z.inj_lt in Hlt.
      rewrite Z2Nat.id in Hlt by lia. lia.
  }
  assert (Hqtrail :
    Zlength (mt_trail (ms_core M)) = ms_qtail M).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hidx :
    0 <= ind < Zlength (mt_trail (ms_core M))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 ind
    (mtw_trail_lits Htrailwf) Hidx) as Hindlitwf.
  pose proof (lit_var_c_in_range n
    (Znth ind (mt_trail (ms_core M)) 0) Hindlitwf) as Hindvarrange.
  assert (Htagword :
    is_tag (Znth x (ms_reason_words M) 0) = true).
  { rewrite <- HwordX. exact Htag. }
  assert (HxrangeM : 0 <= x < ms_size M) by lia.
  destruct (Hbinary x HxrangeM Htagword) as
    (Hqwf & Hqlevel_same & Hqneq_word).
  assert (Hqneq : lit_var_c (tag_lit c) <> x).
  { rewrite HwordX. exact Hqneq_word. }
  exact (conj HCshapeX (conj Horder0 (conj Hrankxa (conj HvalidA
    (conj HentA (conj HCndA (conj HinvNew (conj HpendS
    (conj HresolvedRanks (conj Htags (conj Hind (conj Hwords
    (conj Hroot (conj Hindvarrange (conj HrangeXn Hqneq))))))))))))))).
Qed.

(* The resolvent of a two-literal tagged reason, in both tag states.  Both of
   its literals are at the current level, so nothing is added to [learnt]; the
   selected variable is always already tagged and leaves the pending set, while
   the side variable joins it exactly when it was not tagged yet.  The two
   [zmem] arms are the only place the two tag-step VCs differ. *)
Lemma msat_analyze_e7_resolve_sets_p7 :
  forall (n : Z) (M : msolver) (c x : Z) (C : clause)
         (S0 R0 : list Z) (learnt0 : clause),
    C = lit_denote (trail_lit_of (ms_core M) x) ::
        literal_neg (lit_denote (tag_lit c)) :: nil ->
    0 <= x ->
    level_of (msolver_view n M) x =
      Some (current_level (msolver_view n M)) ->
    level_of (msolver_view n M) (lit_var_c (tag_lit c)) =
      Some (current_level (msolver_view n M)) ->
    In x S0 ->
    resolve_learnt (msolver_view n M) C S0 R0 learnt0 = learnt0 /\
    (zmem (lit_var_c (tag_lit c)) (analyze_tags S0 R0 learnt0) = false ->
     resolve_S (msolver_view n M) x C S0 R0 learnt0 =
       zremove x S0 ++ (lit_var_c (tag_lit c) :: nil)) /\
    (zmem (lit_var_c (tag_lit c)) (analyze_tags S0 R0 learnt0) = true ->
     resolve_S (msolver_view n M) x C S0 R0 learnt0 = zremove x S0).
Proof.
  intros n M c x C S0 R0 learnt0 HC Hx Hlevx Hlevq HinS.
  assert (Hxseen : zmem x (analyze_tags S0 R0 learnt0) = true).
  {
    apply zmem_true_iff. unfold analyze_tags.
    rewrite !in_app_iff. tauto.
  }
  assert (Hxcurrent :
    at_current_level_b (msolver_view n M)
      (lit_denote (trail_lit_of (ms_core M) x)) = true).
  {
    apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite lit_var_c_denote, trail_lit_of_var by lia.
    exact Hlevx.
  }
  assert (Hqcurrent :
    at_current_level_b (msolver_view n M)
      (literal_neg (lit_denote (tag_lit c))) = true).
  {
    apply (proj2 (at_current_level_b_true_iff _ _)).
    rewrite literal_var_neg, lit_var_c_denote.
    exact Hlevq.
  }
  assert (Hxbelow :
    below_current_b (msolver_view n M)
      (lit_denote (trail_lit_of (ms_core M) x)) = false).
  {
    destruct (below_current_b (msolver_view n M)
      (lit_denote (trail_lit_of (ms_core M) x))) eqn:Hb;
      [|reflexivity].
    apply below_current_b_true_iff in Hb.
    destruct Hb as (d & Hd & Hdrange).
    rewrite lit_var_c_denote, trail_lit_of_var in Hd by lia.
    assert (Hdcur : d = current_level (msolver_view n M)) by congruence.
    subst d. lia.
  }
  assert (Hqbelow :
    below_current_b (msolver_view n M)
      (literal_neg (lit_denote (tag_lit c))) = false).
  {
    destruct (below_current_b (msolver_view n M)
      (literal_neg (lit_denote (tag_lit c)))) eqn:Hb;
      [|reflexivity].
    apply below_current_b_true_iff in Hb.
    destruct Hb as (d & Hd & Hdrange).
    rewrite literal_var_neg, lit_var_c_denote in Hd.
    assert (Hdcur : d = current_level (msolver_view n M)) by congruence.
    subst d. lia.
  }
  refine (conj _ (conj _ _)).
  - unfold resolve_learnt, resolve_new_lits. rewrite HC.
    cbn [filter].
    rewrite Hxbelow, Hqbelow. cbn. rewrite app_nil_r. reflexivity.
  - intros Hqnotseen.
    unfold resolve_S, resolve_new_S. rewrite HC.
    cbn [map filter].
    rewrite Hxcurrent, Hqcurrent. cbn.
    rewrite lit_var_c_denote, trail_lit_of_var by lia.
    rewrite literal_var_neg, lit_var_c_denote.
    rewrite Hxseen, Hqnotseen. cbn. reflexivity.
  - intros Hqseen.
    unfold resolve_S, resolve_new_S. rewrite HC.
    cbn [map filter].
    rewrite Hxcurrent, Hqcurrent. cbn.
    rewrite lit_var_c_denote, trail_lit_of_var by lia.
    rewrite literal_var_neg, lit_var_c_denote.
    rewrite Hxseen, Hqseen. cbn. rewrite app_nil_r. reflexivity.
Qed.

(* Removing the selected variable from the pending set: the counter drops by
   one and the ghost tag list is only permuted, because the variable moves from
   the pending block to the head of the resolved block. *)
Lemma msat_analyze_e7_pending_split_p7 :
  forall (n : Z) (F : cnf) (M : msolver) (x cnt : Z)
         (S0 R0 : list Z) (learnt0 : clause),
    analyze_inv F (msolver_view n M) S0 R0 learnt0 ->
    In x S0 ->
    cnt + 1 = Zlength S0 ->
    cnt = Zlength (zremove x S0) /\
    Permutation (analyze_tags S0 R0 learnt0)
                (analyze_tags (zremove x S0) (x :: R0) learnt0).
Proof.
  intros n F M x cnt S0 R0 learnt0 Hinv HinS Hcnt.
  assert (HndS0 : NoDup S0).
  {
    pose proof Hinv as Hinv0_fields.
    unfold analyze_inv in Hinv0_fields.
    destruct Hinv0_fields as (_ & Hndtags0 & _).
    unfold analyze_tags in Hndtags0.
    eapply NoDup_app_remove_r. exact Hndtags0.
  }
  pose proof (zremove_split x) as Hremove.
  destruct (Hremove S0 HndS0 HinS)
    as (before & after & HS0 & HremoveS0).
  assert (Hlenremove : cnt = Zlength (zremove x S0)).
  {
    rewrite HremoveS0, Zlength_app.
    rewrite HS0, !Zlength_app, Zlength_cons in Hcnt. lia.
  }
  refine (conj Hlenremove _).
  unfold analyze_tags.
  rewrite HremoveS0, HS0.
  clear HS0 HremoveS0.
  induction before as [|a before IH].
  - cbn. exact (Permutation_middle after
      (R0 ++ map literal_var learnt0) x).
  - cbn. constructor. exact IH.
Qed.

(* The rank of the tagged side variable.  It is the one literal of the reason
   clause other than the selected variable's own, so [reason_valid] bounds its
   trail position strictly below the selected variable's, which the loop
   invariant pins at [ind + 1]. *)
Lemma msat_analyze_e7_side_rank_p7 :
  forall (n : Z) (M : msolver) (c x ind : Z) (C : clause),
    C = lit_denote (trail_lit_of (ms_core M) x) ::
        literal_neg (lit_denote (tag_lit c)) :: nil ->
    reason_valid (msolver_view n M) x C ->
    assignment_rank (msolver_view n M) x = Some (Z.to_nat (ind + 1)) ->
    0 <= ind ->
    lit_var_c (tag_lit c) <> x ->
    exists rq,
      assignment_rank (msolver_view n M) (lit_var_c (tag_lit c)) = Some rq /\
      Z.of_nat rq <= ind.
Proof.
  intros n M c x ind C HC Hvalid Hrank_sel Hind Hqneq.
  destruct Hvalid as
    (bx & dx & rx & Hassx & Hlevx & Hrankx & Hsatx & Hsidesx).
  assert (HqinC : In (literal_neg (lit_denote (tag_lit c))) C).
  { rewrite HC. cbn. tauto. }
  assert (Hqvarneq :
    literal_var (literal_neg (lit_denote (tag_lit c))) <> x).
  {
    rewrite literal_var_neg, lit_var_c_denote.
    exact Hqneq.
  }
  destruct (Hsidesx _ HqinC Hqvarneq) as
    (_ & dq & rq & Hlevq & Hrankq & Hdq & Hrqlt).
  rewrite literal_var_neg, lit_var_c_denote in Hrankq.
  exists rq. split; [exact Hrankq |].
  rewrite Hrank_sel in Hrankx. inversion Hrankx. subst rx.
  apply Nat2Z.inj_lt in Hrqlt.
  rewrite Z2Nat.id in Hrqlt by lia. lia.
Qed.

(* The backward scan may only decrement [ind] when the trail word it points at
   is untagged, so the loop must not stop at index 0 while pending work remains.
   Any pending variable is tagged, and a pending variable at rank 0 is the
   variable of trail word 0, so an untagged word 0 contradicts the existence of
   a pending variable at or below the index. *)
Lemma msat_analyze_e7_scan_index_nonzero_p7 :
  forall (n : Z) (M Mnext : msolver) (ind : Z)
         (S R : list Z) (learnt : clause),
    ms_core Mnext = ms_core M ->
    analysis_tags_exact n (ms_tags Mnext) (ms_tagged Mnext) ->
    Permutation (ms_tagged Mnext) (analyze_tags S R learnt) ->
    (exists y, In y S) ->
    (forall y, In y S -> exists r,
       assignment_rank (msolver_view n M) y = Some r /\
       Z.of_nat r <= ind) ->
    0 <= ind ->
    Znth (lit_var_c (Znth ind (mt_trail (ms_core Mnext)) 0))
      (ms_tags Mnext) 0 = 0 -> 0 < ind.
Proof.
  intros n M Mnext ind S R learnt Hcore Htags Hperm HexS Hranks Hind Hzero.
  destruct (Z.eq_dec ind 0) as [Hzind | Hzind]; [|lia].
  subst ind.
  pose proof Htags as Htags_fields.
  unfold analysis_tags_exact in Htags_fields.
  destruct Htags_fields as
    (Htagslen & Htaggednd & Htaggedrange & Htagcells & Htagiff).
  destruct HexS as (y & Hy).
  destruct (Hranks y Hy) as (r & Hyrank & Hyrle).
  assert (Hr0 : r = 0%nat) by lia. subst r.
  change (trail_pos (ms_core M) y = Some 0%nat) in Hyrank.
  pose proof (trail_pos_var (ms_core M) y 0%nat Hyrank) as Hyvar.
  cbn in Hyvar. unfold trail_var in Hyvar.
  assert (Hytags : In y (analyze_tags S R learnt)).
  { unfold analyze_tags. apply in_or_app. left. exact Hy. }
  assert (Hyphysical : In y (ms_tagged Mnext)).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hytags.
  }
  rewrite Forall_forall in Htaggedrange.
  pose proof (Htaggedrange y Hyphysical) as Hyrange.
  pose proof (proj2 (Htagiff y Hyrange) Hyphysical) as Hyone.
  rewrite Hcore, Hyvar in Hzero.
  congruence.
Qed.

(* The state after the C code tags the side variable, bumps the heap and copies
   the activity arrays.  The step touches only heuristic and scratch fields, so
   the whole cancel-ready package, the shape, the seed shadow and both core
   equivalences survive it; the ghost tag list gains exactly [q] at the end,
   which is where the resolvent's new pending variable sits. *)
Lemma msat_analyze_e7_tag_state_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M0 M Mtag : msolver)
         (focus q cap' x : Z) (activity' : list fp64)
         (orderpos' heap' S0 R0 : list Z) (learnt0 : clause)
         (var_inc' : fp64),
    Mtag = analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
             (ms_tagged M ++ (q :: nil)) cap' activity' orderpos'
             heap' var_inc' ->
    analysis_cancel_ready n F A_arr K M focus ->
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    0 <= q < n ->
    Znth q (ms_tags M) 0 = 0 ->
    Permutation (ms_tagged M) (analyze_tags S0 R0 learnt0) ->
    Permutation (analyze_tags S0 R0 learnt0)
                (analyze_tags (zremove x S0) (x :: R0) learnt0) ->
    order_heap_wf n heap' orderpos' ->
    Permutation (ms_order M) heap' ->
    solver_shape M ->
    ms_size M = n ->
    Zlength activity' = n ->
    Zlength orderpos' = n ->
    analysis_core_equiv M0 M ->
    msolver_seed_shadow M ->
    zmem q (analyze_tags S0 R0 learnt0) = false /\
    analysis_tags_exact n (ms_tags Mtag) (ms_tagged Mtag) /\
    Permutation (ms_tagged Mtag)
      (analyze_tags (zremove x S0 ++ (q :: nil)) (x :: R0) learnt0) /\
    analysis_cancel_ready n F A_arr K Mtag focus /\
    solver_shape Mtag /\
    n = ms_size Mtag /\
    analysis_core_equiv M0 Mtag /\
    analysis_core_equiv M Mtag /\
    msolver_seed_shadow Mtag /\
    ms_core Mtag = ms_core M /\
    msolver_view n Mtag = msolver_view n M /\
    ms_root_level Mtag = ms_root_level M /\
    ms_qtail Mtag = ms_qtail M.
Proof.
  intros n F A_arr K M0 M Mtag focus q cap' x activity' orderpos' heap'
    S0 R0 learnt0 var_inc' HMtag Hready Htags Hqrange Hqcell0 Hperm
    Hperm_move Hheap Horder Hshape Hsize Hact Hpos Hcore0 Hseed.
  subst Mtag.
  pose proof Hready as Hready_copy.
  unfold analysis_cancel_ready in Hready_copy.
  destruct Hready_copy as
    (Mentry & Hcancel_full & Hequiv & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  pose proof Htags as Htags_fields.
  unfold analysis_tags_exact in Htags_fields.
  destruct Htags_fields as
    (Htagslen & Htaggednd & Htaggedrange & Htagcells & Htagiff).
  assert (Hqnotin_tagged : ~ In q (ms_tagged M)).
  {
    intro Hin.
    pose proof (proj2 (Htagiff q Hqrange) Hin) as Hone.
    congruence.
  }
  assert (Hqnotseen : zmem q (analyze_tags S0 R0 learnt0) = false).
  {
    apply zmem_false_iff. intro Hin.
    apply Hqnotin_tagged.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
  }
  assert (HtagsNew :
    analysis_tags_exact n
      (replace_Znth q 1 (ms_tags M))
      (ms_tagged M ++ (q :: nil))).
  {
    unfold analysis_tags_exact.
    refine (conj _ _).
    { rewrite Zlength_replace_Znth. exact Htagslen. }
    refine (conj _ _).
    { apply NoDup_snoc; assumption. }
    refine (conj _ _).
    { apply Forall_app. split; [exact Htaggedrange |].
      constructor; [exact Hqrange | constructor]. }
    refine (conj _ _).
    { apply Forall_replace_Znth; [exact Htagcells |].
      right. reflexivity. }
    intros v Hv.
    destruct (Z.eq_dec v q) as [-> | Hneq].
    - rewrite Znth_replace_Znth_Same by (rewrite Htagslen; exact Hqrange).
      split; intros _.
      + apply in_or_app. right. left. reflexivity.
      + reflexivity.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htagslen; try lia; congruence).
      rewrite (Htagiff v Hv), in_app_iff. cbn.
      intuition congruence.
  }
  assert (Hperm_base :
    Permutation (ms_tagged M)
      (analyze_tags (zremove x S0) (x :: R0) learnt0)).
  { eapply Permutation_trans; [exact Hperm | exact Hperm_move]. }
  assert (HpermNew :
    Permutation (ms_tagged M ++ (q :: nil))
      (analyze_tags (zremove x S0 ++ (q :: nil))
        (x :: R0) learnt0)).
  {
    eapply Permutation_trans.
    - apply Permutation_app_tail. exact Hperm_base.
    - unfold analyze_tags.
      exact (Permutation_rotate_snoc (zremove x S0)
        ((x :: R0) ++ map literal_var learnt0) q).
  }
  assert (HheapNow :
    heap_wf n {| mh_heap := heap'; mh_orderpos := orderpos' |}).
  { exact Hheap. }
  assert (HheapIncl : incl (ms_order M) heap').
  {
    intros v Hin.
    eapply Permutation_in; [exact Horder | exact Hin].
  }
  assert (HcoversNow :
    heap_covers n {| mh_heap := heap'; mh_orderpos := orderpos' |}
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M))).
  {
    unfold heap_covers in Hcovers |- *.
    intros v Hv Hmissing.
    apply Hcovers; [exact Hv |].
    eapply heap_wf_incl_missing_mono;
      [exact Hheapwf | exact HheapNow | exact HheapIncl | exact Hv |
       exact Hmissing].
  }
  assert (HreadyTag :
    analysis_cancel_ready n F A_arr K
      (analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
         (ms_tagged M ++ (q :: nil)) cap' activity' orderpos'
         heap' var_inc') focus).
  {
    unfold analysis_cancel_ready.
    exists Mentry.
    refine (conj _ _); [exact Hcancel_full |].
    refine (conj _ _).
    { apply analysis_core_equiv_analyze_tag_step. exact Hequiv. }
    refine (conj _ _).
    { rewrite msolver_heap_analyze_tag_step. exact HheapNow. }
    refine (conj _ _).
    { cbn. exact HcoversNow. }
    refine (conj _ _).
    { unfold current_reasonless_earliest in *. cbn in *. exact Hearliest. }
    refine (conj _ _).
    { cbn. exact Hfocuslev. }
    cbn. exact Hclainc.
  }
  assert (HshapeTag :
    solver_shape
      (analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
         (ms_tagged M ++ (q :: nil)) cap' activity' orderpos'
         heap' var_inc')).
  {
    eapply solver_shape_analyze_tag_step; [exact Hshape | | |].
    - rewrite Hsize, Zlength_replace_Znth. exact Htagslen.
    - rewrite Hsize. exact Hact.
    - rewrite Hsize. exact Hpos.
  }
  assert (HseedTag :
    msolver_seed_shadow
      (analyze_tag_step_msolver M (replace_Znth q 1 (ms_tags M))
         (ms_tagged M ++ (q :: nil)) cap' activity' orderpos'
         heap' var_inc')).
  {
    apply (proj2 (msolver_seed_shadow_analyze_tag_step
      M (replace_Znth q 1 (ms_tags M))
      (ms_tagged M ++ q :: nil) cap' activity'
      orderpos' heap' var_inc')).
    exact Hseed.
  }
  refine (conj Hqnotseen (conj HtagsNew (conj HpermNew (conj HreadyTag (conj
    HshapeTag (conj (eq_sym Hsize) (conj _ (conj _ (conj HseedTag (conj
    eq_refl (conj _ (conj eq_refl (eq_refl))))))))))))).
  - apply analysis_core_equiv_analyze_tag_step. exact Hcore0.
  - apply analysis_core_equiv_analyze_tag_step_self.
  - apply msolver_view_analyze_tag_step.
Qed.

(* The already-tagged arm's side variable.  A non-zero tag cell puts it in the
   physical tag list, and the ghost tag list is a permutation of that list, so
   the resolvent's membership test sees it and the pending set does not grow. *)
Lemma msat_analyze_e7_tag_already_seen_p7 :
  forall (n : Z) (M : msolver) (c q : Z)
         (S0 R0 : list Z) (learnt0 : clause),
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    Permutation (ms_tagged M) (analyze_tags S0 R0 learnt0) ->
    q = lit_var_c (tag_lit c) ->
    0 <= lit_var_c (tag_lit c) ->
    lit_var_c (tag_lit c) < n ->
    Znth q (ms_tags M) 0 <> 0 ->
    zmem (lit_var_c (tag_lit c)) (analyze_tags S0 R0 learnt0) = true.
Proof.
  intros n M c q S0 R0 learnt0 Htags Hperm Hq Hqlo Hqhi Hnz.
  pose proof Htags as Htags_fields.
  unfold analysis_tags_exact in Htags_fields.
  destruct Htags_fields as
    (Htagslen & Htaggednd & Htaggedrange & Htagcells & Htagiff).
  assert (Hqcell : Znth (lit_var_c (tag_lit c)) (ms_tags M) 0 = 1).
  {
    assert (Hqidx :
      0 <= lit_var_c (tag_lit c) < Zlength (ms_tags M)) by lia.
    pose proof (Forall_Znth_elim _ _ _ 0 (lit_var_c (tag_lit c))
      Htagcells Hqidx) as Hcell.
    cbn beta in Hcell.
    rewrite <- Hq in Hcell.
    destruct Hcell as [Hz | Ho].
    - exfalso. apply Hnz. exact Hz.
    - rewrite <- Hq. exact Ho.
  }
  apply zmem_true_iff.
  eapply Permutation_in; [exact Hperm |].
  apply (proj1 (Htagiff _ (conj Hqlo Hqhi))).
  exact Hqcell.
Qed.

(* Bind the common selected-reason facts by content in either tag branch.
   Value introduction and branch-specific allocation facts stay at the caller. *)
Ltac msat_analyze_e7_semantic_facts_p7 n F A_arr K M focus c x C phase
    words cnt ind p S0 R0 learnt :=
  bind_fact ( reason_target_wf n M x c C ) as H_reason_target;
  bind_fact ( analysis_cancel_ready n F A_arr K M focus )
    as H_cancel_ready;
  bind_fact ( is_tag c = msat_true ) as H_is_tag;
  bind_fact ( 0 <= lit_var_c (tag_lit c) ) as H_tag_lo;
  bind_fact ( lit_var_c (tag_lit c) < n ) as H_tag_hi;
  bind_fact ( level_of (msolver_view n M) (lit_var_c (tag_lit c)) =
    Some (current_level (msolver_view n M)) ) as H_tag_level;
  bind_fact ( analyze_resolution_loop_inv n F A_arr K M
    focus phase c C words cnt ind p ) as H_loop_inv;
  bind_fact ( phase = AnalyzeSelected ) as H_phase;
  bind_fact ( In x S0 ) as H_x_in_S0;
  bind_fact ( cnt + 1 = Zlength S0 ) as H_cnt_len;
  bind_fact ( level_of (msolver_view n M) x =
    Some (current_level (msolver_view n M)) ) as H_x_level;
  bind_fact ( c = Znth x (ms_reason_words M) 0 ) as H_reason_word;
  bind_fact ( analyze_inv F (msolver_view n M) S0 R0 learnt )
    as H_analyze_inv;
  bind_fact ( lits_denote (tl words) = learnt ) as H_learnt_eq;
  bind_fact ( Permutation (ms_tagged M) (analyze_tags S0 R0 learnt) )
    as H_tagged_perm;
  bind_fact ( solver_shape M ) as H_shape;
  bind_fact ( ms_size M = n ) as H_size.

(* Introduce solver_analyze_entail_wit_7_1's value binders under the
   names the script below uses, then bind the emitted facts it
   reads by their CONTENT, so that nothing depends on the order symexec
   happened to emit them in (V2.1.0 guide 11).  Serves that obligation only *)
Ltac msat_analyze_e7_bind_facts_p7 :=
  intros learnt_pre s_pre anz_wl levels_ptr anz_focus M0 K anz_A_arr anz_F anz_n Mcur
    phase Ccur words words_cap c p ind cnt tags_loop trail_loop reasons_loop Mcur_2
    phase_2 Ccur_2 words_2 words_cap_2 activity_ptr_loop orderpos_ptr_loop retval S0 R0
    learnt0 x retval_2 retval_3 retval_4 retval_5 retval_6 retval_7 retval_8 p_prime
    cap_prime retval_9 retval_10 activity1 heap1 orderpos1 var_inc_now activity_now
    heap_now orderpos_now tags_now retval_11 retval_12;
  intros;
  bind_fact ( Zlength tags_now = anz_n ) as H_tags_len;
  bind_fact ( order_heap_wf anz_n heap_now orderpos_now ) as H_order_wf;
  bind_fact ( Permutation (ms_order Mcur_2) heap_now ) as H_order_perm;
  bind_fact ( Zlength activity_now = anz_n ) as H_act_len;
  bind_fact ( Zlength orderpos_now = anz_n ) as H_pos_len;
  bind_fact ( Znth (lit_var_c (tag_lit c)) (ms_tags Mcur_2) 0 = 0 )
    as H_tag_zero;
  msat_analyze_e7_semantic_facts_p7 anz_n anz_F anz_A_arr K Mcur_2
    anz_focus c x Ccur_2 phase_2 words_2 cnt ind p S0 R0 learnt0;
  bind_fact ( analysis_core_equiv M0 Mcur_2 ) as H_core_equiv;
  bind_fact ( msolver_seed_shadow Mcur_2 ) as H_seed.


(* Scan step of solver_analyze's minimize loop: the literal at index [i] of the
   working word list is assigned strictly below the current decision level. *)
Lemma msat_analyze_minimize_scan_assigned_p7 :
  forall (n : Z) (F : cnf) (M : msolver)
         (original kept removed words T : list Z) (i j : Z),
    analyze_clause_cert n F M original ->
    analyze_minimize_loop_inv n M original kept removed words T i j ->
    incl (map lit_var_c words) (map lit_var_c (mt_trail (ms_core M))) ->
    0 <= i -> i < Zlength words ->
    assigned_below_current (msolver_view n M) (lit_var_c (Znth (i - 0) words 0)).
Proof.
  intros n F M original kept removed words T i j Hcert0 Hinv H_incl Hi0 Hi1.
  unfold analyze_minimize_loop_inv in Hinv; simpl in Hinv.
  unfold analyze_clause_cert, uip_exit_cert in Hcert0.
  destruct Hinv as [Hj Htmp].
  destruct Htmp as [Hji Htmp].
  destruct Htmp as [HiLen Htmp].
  destruct Htmp as [Hlen Htmp].
  destruct Htmp as [Hhead Htmp].
  destruct Htmp as [Horig Htmp].
  destruct Htmp as [Hwords Htmp].
  destruct Htmp as [Hkept Htmp].
  destruct Htmp as [Hremoved Htmp].
  destruct Htmp as [Hsuffix Htmp].
  destruct Htmp as [Htags Htmp].
  destruct Htmp as [Hperm Htmp].
  destruct Htmp as [Hwitness Htmp].
  destruct Htmp as [Hscope Htmp].
  destruct Htmp as [HremovedT Htmp].
  destruct Htmp as [HallT Hprefix].
  destruct Hcert0 as [Hcert Hroot].
  destruct Hcert as [Hsound HcertRest].
  destruct HcertRest as [Hnodup Hexists].
  destruct Hexists as [uh [ur [Hule [Hul Hrest]]]].
  set (w := Znth (i - 0) words 0).
  assert (Hsub : In w (sublist i (Zlength original) original)).
  { assert (Hsub0 : In w (sublist i (Zlength words) words)).
    { unfold w. replace (i - 0) with i by lia.
      pose proof (Znth_In Z (sublist i (Zlength words) words) 0 0) as H0.
      rewrite (Znth_sublist 0 i 0 (Zlength words) words) in H0 by lia.
      apply H0. rewrite Zlength_sublist by lia. lia. }
    rewrite Hlen in Hsub0. rewrite Hsuffix in Hsub0. exact Hsub0. }
  assert (HlitPending : In (lit_denote w)
    (lits_denote (sublist i (Zlength original) original))).
  { apply lits_denote_in. exact Hsub. }
  assert (HlitTail : In (lit_denote w) (lits_denote (tl original))).
  { eapply Permutation_in; [exact (Permutation_sym Hperm)|].
    apply in_or_app. right. apply in_or_app. right. exact HlitPending. }
  destruct original as [|wh wt].
  - simpl in HlitTail. contradiction.
  - simpl in Hule, HlitTail.
    inversion Hule; subst.
    rewrite Forall_forall in Hrest.
    destruct (Hrest _ HlitTail) as [d [Hd Hlt]].
    rewrite lit_var_c_denote in Hd.
    assert (Htrail : In (lit_var_c w)
      (map lit_var_c (mt_trail (ms_core M)))).
    { apply H_incl. apply in_map. apply Znth_In. lia. }
    destruct (find_var_pos_in _ _ Htrail) as [r Hr].
    unfold assigned_below_current.
    exists d. exists r.
    split; [exact Hd | split; [exact Hr | exact Hlt]].
Qed.


(* Replacing the object at one entry of a database list leaves the pointer
   column untouched.  Both wit_66 arms need this twice: once for the key
   equality the route's well-formedness transfer consumes, and once for the
   frame equality that lets the spatial closer forget which side was rewritten *)
Lemma msat_propagate_wit66_keys_replace_p7 :
  forall (pre post : dbmap) (q : Z) (c1 c2 : clause_obj) (l : dbmap),
    l = pre ++ (q, c1) :: post ->
    map fst (pre ++ (q, c2) :: post) = map fst l.
Proof.
  intros pre post q c1 c2 l Hl. subst l.
  rewrite !map_app. cbn. reflexivity.
Qed.

(* The rewritten clause object is still well-formed: its literal list is a
   permutation of the old one, so length, literal bounds and variable
   distinctness all transport.  Shared by both wit_66 arms *)
Lemma msat_propagate_wit66_new_obj_wf_p7 :
  forall (n : Z) (co : clause_obj) (watch0 false_lit a0 a1 : Z)
         (tail : list Z),
    2 <= Zlength_aux 2 Z tail ->
    Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
    NoDup (map lit_var_c (a0 :: a1 :: tail)) ->
    Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail) ->
    obj_wf n (clause_obj_with_lits co (watch0 :: false_lit :: tail)).
Proof.
  intros n co watch0 false_lit a0 a1 tail Hlen Hall Hnodup Hperm.
  unfold clause_obj_with_lits, obj_wf. cbn.
  split; [exact Hlen|]. split.
  - rewrite Forall_forall in Hall |- *. intros x Hx. apply Hall.
    eapply Permutation_in; [exact Hperm|exact Hx].
  - apply (Permutation_NoDup
      (Permutation_sym (Permutation_map lit_var_c Hperm))).
    exact Hnodup.
Qed.

(* The binary-clause region is not part of the database pair the propagation
   step rewrites, so the route update leaves its representation alone *)
Lemma msat_propagate_wit66_binary_rep_p7 :
  forall (Mscan : msolver) (prob' learnt' : dbmap) (wm : list (list Z))
         (caps : list Z),
    solver_binary_rep
      (msolver_propagation_db_wmap_update Mscan prob' learnt' wm caps) =
    solver_binary_rep Mscan.
Proof.
  intros. unfold solver_binary_rep,
    msolver_propagation_db_wmap_update, msolver_propagation_overlay, msolver_propagation_update.
  reflexivity.
Qed.

(* Splitting the clause-database representation at the entry being rewritten.
   The two directions are the framework's own app introduction and elimination;
   packaging them as one bi-entailment keeps each arm's spatial half short *)
Lemma msat_propagate_wit66_db_rep_split_p7 :
  forall (pre post : dbmap) (e : Z * clause_obj),
    clause_db_rep (pre ++ e :: post) --||--
    clause_db_rep pre ** clause_db_rep (e :: post).
Proof.
  intros. split.
  - apply clause_db_rep_app_elim.
  - apply clause_db_rep_app_intro.
Qed.
(* The propagate frame depends on the database only through its pointer
   columns, so a route update that preserves both columns preserves the frame *)
Lemma msat_propagate_wit66_frame_eq_p7 :
  forall (s : Z) (Mscan : msolver) (prob' learnt' : dbmap)
         (wm : list (list Z)) (caps : list Z),
    map fst prob' = map fst (ms_prob Mscan) ->
    map fst learnt' = map fst (ms_learnt Mscan) ->
    solver_propagate_frame s
      (msolver_propagation_db_wmap_update Mscan prob' learnt' wm caps) =
    solver_propagate_frame s Mscan.
Proof.
  intros s Mscan prob' learnt' wm caps Hp Hl.
  unfold msolver_propagation_db_wmap_update, solver_propagate_frame,
    solver_fp_rep, msolver_propagation_overlay, msolver_propagation_update. cbn.
  rewrite Hp, Hl. reflexivity.
Qed.
(* Everything the two wit_66 arms learn about the scanned clause before they
   diverge: it has at least two literals, its object is well-formed, and the
   watcher-scan facts of propagation_normalized_conflict_scan_facts hold of the normalized
   literal list.  Returning the head split as an existential lets each arm
   rewrite the spec-level literal list in its own goal with one substitution *)
Lemma msat_propagate_wit66_scan_shape_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj)
         (scan_current p wm_len watch0 false_lit : Z)
         (clause_contents : list Z),
    solver_propagation_weak n F A_arr K Mscan ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = clause_contents ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <> 0 ->
    Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <>
      lit_sig watch0 ->
    propagation_replacement_scan_inv n Mscan false_lit
      (propagation_normalized_clause watch0 false_lit clause_contents)
      (Zlength (propagation_normalized_clause watch0 false_lit
         clause_contents)) ->
    false_lit = lit_neg_c p ->
    real_watch_pair wm_len clause_contents ->
    wm_len = p ->
    watch0 + false_lit =
      Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ->
    exists a0 a1 tail,
      clause_contents = a0 :: a1 :: tail
      /\ 2 <= Zlength_aux 2 Z tail
      /\ Forall (lit_wf_c n) (a0 :: a1 :: tail)
      /\ NoDup (map lit_var_c (a0 :: a1 :: tail))
      /\ propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail)
           = watch0 :: false_lit :: tail
      /\ sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail
      /\ Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail)
      /\ ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0))
      /\ Forall (lit_false (mt_assigns (ms_core Mscan)))
           (watch0 :: false_lit :: tail)
      /\ (forall v, 0 <= v < n ->
            Znth v (ms_reason_words Mscan) 0 <> scan_current)
      /\ (forall l, Permutation (entry_watchers (scan_current, co) l)
            (entry_watchers (scan_current,
               clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)).
Proof.
  intros n F A_arr K Mscan co scan_current p wm_len watch0 false_lit
    clause_contents Hweak Hdbwf Hin Hlits Hassigned Hnotsig
    Hscaninv Hfalse_lit Hpair Hwmlen Hwatch0.
  pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin)
    as Hobj.
  unfold obj_wf in Hobj. rewrite Hlits in Hobj.
  destruct Hobj as [Hlen [Hall Hnodup]].
  destruct clause_contents as [|a0 tail0]; cbn in Hlen; [lia|].
  destruct tail0 as [|a1 tail]; cbn in Hlen; [lia|].
  destruct (propagation_normalized_conflict_scan_facts n F A_arr K Mscan co
      scan_current p wm_len watch0 false_lit a0 a1 tail
      Hweak Hin Hlits Hall Hassigned Hnotsig
      Hscaninv Hfalse_lit Hpair Hwmlen Hwatch0)
    as [Htail [Hperm [Hwatchcases [_ [Hnew_false [_
       [_ [Hno_reason_ptr Hentry_perm]]]]]]]].
  exists a0, a1, tail.
  split; [reflexivity|]. split; [exact Hlen|]. split; [exact Hall|].
  split; [exact Hnodup|]. split.
  { unfold propagation_normalized_clause. rewrite Htail. reflexivity. }
  split; [exact Htail|]. split; [exact Hperm|].
  split; [exact Hwatchcases|]. split; [exact Hnew_false|].
  split; [exact Hno_reason_ptr|exact Hentry_perm].
Qed.
(* The route database is the old one with a single entry's object replaced.
   From that presentation alone come the key equality, membership transfer in
   both directions, the watcher-occurrence permutation and well-formedness of
   the route database.  Stated over an abstract split so the problem-clause arm
   and the learnt-clause arm share it *)
Lemma msat_propagate_wit66_route_db_wf_p7 :
  forall (n : Z) (Mscan : msolver) (co co_new : clause_obj)
         (scan_current : Z) (pre2 post2 prob' learnt' : dbmap),
    db_wf n (msolver_db Mscan) ->
    obj_wf n co_new ->
    msolver_db Mscan = pre2 ++ (scan_current, co) :: post2 ->
    prob' ++ learnt' = pre2 ++ (scan_current, co_new) :: post2 ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current, co_new) l)) ->
    map fst (prob' ++ learnt') = map fst (msolver_db Mscan)
    /\ (forall q obj, q <> scan_current -> In (q, obj) (msolver_db Mscan) ->
          In (q, obj) (prob' ++ learnt'))
    /\ (forall q obj, In (q, obj) (prob' ++ learnt') ->
          In (q, obj) (msolver_db Mscan) \/ (q, obj) = (scan_current, co_new))
    /\ (forall l, Permutation (expected_watchers (msolver_db Mscan) l)
          (expected_watchers (prob' ++ learnt') l))
    /\ In (scan_current, co_new) (prob' ++ learnt')
    /\ db_wf n (prob' ++ learnt').
Proof.
  intros n Mscan co co_new scan_current pre2 post2 prob' learnt'
    Hdbwf Hobjnew Hold Hnew Hentry_perm.
  assert (Hkeys : map fst (prob' ++ learnt') = map fst (msolver_db Mscan)).
  { rewrite Hold, Hnew. rewrite !map_app. cbn. reflexivity. }
  pose proof (msat_db_entry_swap_mem_cases (msolver_db Mscan)
    (prob' ++ learnt') pre2 post2 scan_current co co_new Hold Hnew) as Hcases.
  pose proof (msat_db_entry_swap_mem_fwd (msolver_db Mscan)
    (prob' ++ learnt') pre2 post2 scan_current co co_new Hold Hnew) as Hother.
  pose proof (msat_db_entry_swap_expected_watchers (msolver_db Mscan)
    (prob' ++ learnt') pre2 post2 scan_current co co_new Hold Hnew
    Hentry_perm) as Hexp.
  assert (Hsel : In (scan_current, co_new) (prob' ++ learnt')).
  { rewrite Hnew. apply in_or_app. right. simpl. auto. }
  split; [exact Hkeys|]. split; [exact Hother|]. split; [exact Hcases|].
  split; [exact Hexp|]. split; [exact Hsel|].
  unfold db_wf in Hdbwf |- *.
  destruct Hdbwf as [Hk [Hptrs Hobjs]].
  split; [rewrite Hkeys; exact Hk|]. split.
  - rewrite Forall_forall in Hptrs |- *. intros e He.
    assert (Hemap : In (fst e) (map fst (prob' ++ learnt'))).
    { apply in_map. exact He. }
    rewrite Hkeys in Hemap.
    apply in_map_iff in Hemap as [eold [Hfst Heold]].
    specialize (Hptrs eold Heold). rewrite <- Hfst. exact Hptrs.
  - rewrite Forall_forall in Hobjs |- *. intros [q obj] He.
    destruct (Hcases q obj He) as [Hin2 | Heq].
    + apply Hobjs. exact Hin2.
    + inversion Heq; subst. exact Hobjnew.
Qed.
(* The route half of both wit_66 arms, once.  Given the transfer facts of
   msat_propagate_wit66_route_db_wf_p7 and the four database predicates the
   arm establishes for its own side, this rebuilds the msolver invariant over
   the updated database, transports the watcher frontier, certifies the new
   clause as the conflict, and packages the whole thing as the unit-conflict
   readiness the which_implies target asks for *)
Lemma msat_propagate_wit66_route_ready_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj) (scan_current p watch0 false_lit a0 a1 : Z)
         (tail retained rest : list Z) (prob' learnt' : dbmap),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tail ->
    obj_wf n (clause_obj_with_lits co (watch0 :: false_lit :: tail)) ->
    Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail) ->
    false_lit = lit_neg_c p ->
    (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)) ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    map fst (prob' ++ learnt') = map fst (msolver_db Mscan) ->
    (forall q obj, q <> scan_current -> In (q, obj) (msolver_db Mscan) ->
       In (q, obj) (prob' ++ learnt')) ->
    (forall q obj, In (q, obj) (prob' ++ learnt') ->
       In (q, obj) (msolver_db Mscan) \/
       (q, obj) = (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail))) ->
    (forall l, Permutation (expected_watchers (msolver_db Mscan) l)
       (expected_watchers (prob' ++ learnt') l)) ->
    In (scan_current,
        clause_obj_with_lits co (watch0 :: false_lit :: tail))
      (prob' ++ learnt') ->
    db_wf n (prob' ++ learnt') ->
    db_matches_cnf F (msolver_propagation_db_wmap_update Mscan prob' learnt'
      (ms_wm Mscan) (ms_wcaps Mscan)) ->
    db_complete F (msolver_propagation_db_wmap_update Mscan prob' learnt'
      (ms_wm Mscan) (ms_wcaps Mscan)) ->
    db_implied F (msolver_propagation_db_wmap_update Mscan prob' learnt'
      (ms_wm Mscan) (ms_wcaps Mscan)) ->
    prob_db prob' ->
    learnt_db learnt' ->
    entails_clause F
      (denote_obj (clause_obj_with_lits co (watch0 :: false_lit :: tail))) ->
    db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan) scan_current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
      prob' learnt' ->
    propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0
      false_lit (a0 :: a1 :: tail) retained rest prob' learnt'
      (msolver_propagation_db_wmap_update Mscan prob' learnt'
        (ms_wm Mscan) (ms_wcaps Mscan)).
Proof.
  intros n F A_arr K Mscan co scan_current p watch0 false_lit a0 a1 tail
    retained rest prob' learnt' Hsem Hdbwf Hin Hlits Hobjnew Hnew_false
    H_false_lit
    Hno_reason_ptr Hentry_perm Hwatchcases Hkeys_route Hlookup_other Hcases
    Hexpected_perm Hselected_route Hdbwf_route Hdbmatches_route
    Hdbcomplete_route Hdbimplied_route Hprobdb_route Hlearntdb_route
    Hentails_new Hdbupdate.
  destruct Hsem as [Hlive | Hdead]; [|destruct Hdead as [Hzero _]; lia].
  destruct Hlive as
    [_ [Hweak [Hprop [_ [Hheapcovers [Hreasonless
      [Hlevel [Hp [Hprocessed [Hfrontier _]]]]]]]]]].
  set (new_lits := watch0 :: false_lit :: tail) in *.
  set (co_new := clause_obj_with_lits co new_lits) in *.
  set (Mroute := msolver_propagation_db_wmap_update Mscan prob' learnt'
    (ms_wm Mscan) (ms_wcaps Mscan)) in *.
  assert (Hbinary_route :
      ~ In (ms_binary Mscan) (map fst (prob' ++ learnt'))).
  { rewrite Hkeys_route.
    msat_propagate_project_weak_field Hweak K (@msw_binary_out)
      (@msa_binary_out). }
  assert (Hreasons_old : reasons_match n (ms_core Mscan)
      (msolver_db Mscan) (ms_reason_words Mscan) (ms_reason_of Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_reasons_mem)
      (@msa_reasons_mem). }
  assert (Hreasons_route : reasons_match n (ms_core Mscan)
      (prob' ++ learnt') (ms_reason_words Mscan) (ms_reason_of Mscan)).
  { unfold reasons_match in Hreasons_old |- *. intros v Hv.
    specialize (Hreasons_old v Hv).
    unfold reason_word_ok in Hreasons_old |- *.
    destruct ((Znth v (ms_reason_words Mscan) 0 =? 0)%Z) eqn:Hz;
      [exact Hreasons_old|].
    destruct (is_tag (Znth v (ms_reason_words Mscan) 0)) eqn:Htag;
      [exact Hreasons_old|].
    destruct Hreasons_old as [Hassignedv [obj [Hlookup Hr]]].
    split; [exact Hassignedv|]. exists obj. split; [|exact Hr].
    apply Hlookup_other; [apply Hno_reason_ptr; exact Hv|exact Hlookup]. }
  pose proof (msat_db_entry_swap_mem_bwd (msolver_db Mscan)
    (prob' ++ learnt') scan_current co_new Hcases) as Hlookup_route_old.
  assert (Hsize_old : n = ms_size Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_size) (@msa_size). }
  assert (Hreasonhead_old : reason_head_ok Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_reason_head)
      (@msa_reason_head). }
  assert (Hreasonhead_route : reason_head_ok Mroute).
  { unfold reason_head_ok in Hreasonhead_old |- *.
    intros v obj Hv Htag Hnz Hlookup.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update in *; cbn in *.
    apply (Hreasonhead_old v obj); try assumption.
    apply Hlookup_route_old; [|exact Hlookup].
    apply Hno_reason_ptr. rewrite Hsize_old. exact Hv. }
  assert (Hwmap_old : wmap_exact n (msolver_db Mscan) (ms_wm Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_wmap_exact)
      (@msa_wmap_exact). }
  assert (Hwmap_route : wmap_exact n (prob' ++ learnt') (ms_wm Mscan)).
  { unfold wmap_exact in Hwmap_old |- *.
    destruct Hwmap_old as [Hlenwm Hold]. split; [exact Hlenwm|].
    intros l Hl. specialize (Hold l Hl).
    eapply Permutation_trans; [exact Hold|apply Hexpected_perm]. }
  assert (Hweak_route : solver_propagation_weak n F A_arr K Mroute).
  { unfold solver_propagation_weak in Hweak |- *.
    destruct Hweak as [Hroot Hweak]. split; [exact Hroot|].
    destruct K;
    (cbn in Hweak |- *; destruct Hweak;
      unfold Mroute, msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update; cbn;
      constructor; try exact Hdbwf_route; try exact Hdbmatches_route;
        try exact Hdbcomplete_route; try exact Hdbimplied_route;
        try exact Hprobdb_route; try exact Hlearntdb_route;
        try exact Hbinary_route; try exact Hreasons_route;
        try exact Hreasonhead_route; try exact Hwmap_route;
        try assumption). }
  assert (Hfrontier_route : minisat_watch_frontier_except n
      (prob' ++ learnt') (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan))
      (lit_denote p)).
  { unfold minisat_watch_frontier_except,
      minisat_watch_occurrences in Hfrontier |- *.
    unfold watch_frontier_except in Hfrontier |- *.
    rewrite Forall_forall in Hfrontier |- *.
    intros o Ho. apply in_map_iff in Ho as [[q obj] [<- Hentry]].
    destruct (Hcases q obj Hentry) as [Hold | Heq].
    - apply Hfrontier. apply in_map. exact Hold.
    - inversion Heq; subst q obj.
      specialize (Hfrontier (minisat_occurrence_of_entry
        (scan_current, co))).
      assert (Holdin : In (minisat_occurrence_of_entry
          (scan_current, co))
          (map minisat_occurrence_of_entry (msolver_db Mscan))).
      { apply in_map. exact Hin. }
      specialize (Hfrontier Holdin).
      destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
      + subst a0. subst watch0.
        unfold minisat_occurrence_of_entry, co_watch0, co_watch1,
          co_new, clause_obj_with_lits, new_lits in *.
        rewrite Hlits in Hfrontier. cbn in *. tauto.
      + subst a1. subst watch0.
        unfold minisat_occurrence_of_entry, co_watch0, co_watch1,
          co_new, clause_obj_with_lits, new_lits in *.
        rewrite Hlits in Hfrontier. cbn in *. exact Hfrontier. }
  assert (Hheapwf_old : heap_wf n (msolver_heap Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_heap_wf)
      (@msa_heap_wf). }
  assert (Hcancel_route : propagation_cancel_ready n F A_arr K Mroute p).
  { unfold propagation_cancel_ready.
    split; [exact Hweak_route|]. split; [exact Hprop|].
    split; [exact Hp|]. split; [exact Hprocessed|].
    split; [exact Hlevel|]. split; [exact Hfrontier_route|].
    split; [exact Hheapwf_old|]. split;
      [exact Hheapcovers|exact Hreasonless]. }
  assert (Hclause_false_new : clause_false
      (assigns_pv (mt_assigns (ms_core Mroute))) (denote_obj co_new)).
  { unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
    unfold denote_obj.
    change (clause_false (assigns_pv (mt_assigns (ms_core Mscan)))
      (lits_denote new_lits)).
    apply lits_denote_false_iff.
    - destruct Hobjnew as [_ [Hwfnew _]].
      unfold co_new, clause_obj_with_lits in Hwfnew; cbn in Hwfnew.
      eapply Forall_impl; [|exact Hwfnew]. intros x Hx. destruct Hx. lia.
    - exact Hnew_false. }
  assert (Hwfden_new : Forall (literal_wf n) (denote_obj co_new)).
  { unfold denote_obj. apply lits_denote_wf.
    destruct Hobjnew as [_ [Hwfnew _]]. exact Hwfnew. }
  assert (Hnodupden_new : NoDup (map literal_var (denote_obj co_new))).
  { unfold denote_obj. apply lits_denote_nodup_vars.
    destruct Hobjnew as [_ [_ Hndnew]]. exact Hndnew. }
  assert (Hcurrent_new : exists l, In l (denote_obj co_new) /\
      level_of (msolver_view n Mroute) (literal_var l) =
        Some (Zlength (mt_lim (ms_core Mroute)))).
  { exists (lit_denote false_lit). split.
    - unfold denote_obj, co_new, clause_obj_with_lits, new_lits,
        lits_denote. cbn. auto.
    - unfold Mroute, msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
      rewrite lit_var_c_denote, H_false_lit, lit_var_c_neg. exact Hlevel. }
  assert (Hcert_new : propagation_conflict_cert n F Mroute
      (denote_obj co_new)).
  { unfold propagation_conflict_cert. repeat split;
      try exact Hentails_new; try exact Hclause_false_new;
      try exact Hwfden_new; try exact Hnodupden_new;
      try exact Hcurrent_new. }
  assert (Hptr_ne_binary : scan_current <> ms_binary Mroute).
  { intro Heq. apply Hbinary_route.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update in Heq; cbn in Heq. rewrite <- Heq.
    apply in_map_iff. exists (scan_current, co_new).
    split; [reflexivity|exact Hselected_route]. }
  assert (Hptrden_new : conflict_ptr_denotes Mroute scan_current
      (denote_obj co_new)).
  { right. exists co_new. split; [exact Hptr_ne_binary|]. split.
    - unfold Mroute, msolver_propagation_db_wmap_update,
        msolver_propagation_overlay, msolver_propagation_update; cbn. exact Hselected_route.
    - reflexivity. }
  assert (Hscan_conflict : solver_propagation_scan_semantics
      n F A_arr K Mroute p scan_current (retained ++ rest) nil).
  { right. split.
    - pose proof (db_wf_ptr_pos n (msolver_db Mscan) scan_current co
        Hdbwf Hin). lia.
    - split; [reflexivity|]. split; [exact Hcancel_route|].
      exists (denote_obj co_new). split;
        [exact Hcert_new|exact Hptrden_new]. }
  split; [exact Hdbupdate|].
  unfold propagation_unit_conflict_transition. split;
    [reflexivity|exact Hscan_conflict].
Qed.
(* The problem-clause arm of wit_66.  The rewritten entry lives in ms_prob, so
   db_matches_cnf and db_complete have to be re-proved against the new problem
   list (the new object denotes a permutation of the old clause), while the
   learnt side is untouched.  Concludes through
   msat_propagate_wit66_route_ready_p7 *)
Lemma msat_propagate_wit66_prob_ready_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj) (pre post : dbmap)
         (scan_current p watch0 false_lit a0 a1 : Z)
         (tail retained rest : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tail ->
    ms_prob Mscan = pre ++ (scan_current, co) :: post ->
    2 <= Zlength_aux 2 Z tail ->
    Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
    NoDup (map lit_var_c (a0 :: a1 :: tail)) ->
    Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail) ->
    Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail) ->
    false_lit = lit_neg_c p ->
    (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)) ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail) =
      watch0 :: false_lit :: tail ->
    propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0
      false_lit (a0 :: a1 :: tail) retained rest
      (pre ++ (scan_current,
         clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
      (ms_learnt Mscan)
      (msolver_propagation_db_wmap_update Mscan
        (pre ++ (scan_current,
           clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
        (ms_learnt Mscan) (ms_wm Mscan) (ms_wcaps Mscan)).
Proof.
  intros n F A_arr K Mscan co pre post scan_current p watch0 false_lit a0 a1
    tail retained rest Hsem Hdbwf Hin Hlits Hprob Hlen Hall Hnodup Hperm
    Hnew_false H_false_lit Hno_reason_ptr Hentry_perm Hwatchcases Hnew_eq.
  pose proof Hsem as Hscan_arms.
  destruct Hscan_arms as [Hlive | Hdead]; [|destruct Hdead as [Hzero _]; lia].
  destruct Hlive as
    [_ [Hweak [Hprop [_ [Hheapcovers [Hreasonless
      [Hlevel [Hp [Hprocessed [Hfrontier _]]]]]]]]]].
  set (new_lits := watch0 :: false_lit :: tail) in *.
  set (co_new := clause_obj_with_lits co new_lits) in *.
  set (prob_route := pre ++ (scan_current, co_new) :: post) in *.
  set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
    (ms_learnt Mscan) (ms_wm Mscan) (ms_wcaps Mscan)) in *.
  assert (Hdbupdate : db_pair_lits_update (ms_prob Mscan)
      (ms_learnt Mscan) scan_current (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit
        (a0 :: a1 :: tail)) prob_route (ms_learnt Mscan)).
  { left. exists co, pre, post. repeat split; try assumption.
    unfold prob_route, co_new. rewrite Hnew_eq. reflexivity. }
  pose proof Hdbupdate as Hupdate_lits.
  rewrite Hnew_eq in Hupdate_lits.
  destruct (db_pair_lits_update_prob_entry_bi__propagate_dbu
    _ _ _ _ _ _ _ Hperm Hupdate_lits) as [Hprobforward Hprobreverse].
  assert (Hobjnew : obj_wf n co_new).
  { apply (msat_propagate_wit66_new_obj_wf_p7 n co watch0 false_lit a0 a1 tail); assumption. }
  assert (Hsplit_old : msolver_db Mscan =
      pre ++ (scan_current, co) :: (post ++ ms_learnt Mscan)).
  { unfold msolver_db. rewrite Hprob. rewrite <- app_assoc. reflexivity. }
  assert (Hnewsplit : prob_route ++ ms_learnt Mscan =
      pre ++ (scan_current, co_new) :: (post ++ ms_learnt Mscan)).
  { unfold prob_route. rewrite <- app_assoc. reflexivity. }
  destruct (msat_propagate_wit66_route_db_wf_p7 n Mscan co co_new scan_current
      pre (post ++ ms_learnt Mscan) prob_route (ms_learnt Mscan)
      Hdbwf Hobjnew Hsplit_old Hnewsplit Hentry_perm)
    as [Hkeys_route [Hlookup_other [Hcases [Hexpected_perm
       [Hselected_route Hdbwf_route]]]]].
  assert (Hdbmatches_old : db_matches_cnf F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_matches)
      (@msa_db_matches). }
  assert (Hdbmatches_route : db_matches_cnf F
      (msolver_propagation_db_wmap_update Mscan prob_route
        (ms_learnt Mscan) (ms_wm Mscan) (ms_wcaps Mscan))).
  { unfold db_matches_cnf in Hdbmatches_old |- *. cbn.
    eapply db_matches_entries_transport__propagate_dbu;
      [exact Hprobforward | exact Hdbmatches_old]. }
  assert (Hdbcomplete_old : db_complete F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_complete)
      (@msa_db_complete). }
  assert (Hdbcomplete_route : db_complete F Mroute).
  { unfold db_complete in Hdbcomplete_old |- *.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn.
    eapply db_complete_entries_transport__propagate_dbu;
      [exact Hprobreverse | exact Hdbcomplete_old]. }
  assert (Hprobdb_old : prob_db (ms_prob Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_prob_db)
      (@msa_prob_db). }
  assert (Hprobdb_route : prob_db prob_route).
  { unfold prob_route, co_new.
    apply prob_db_replace_lits__propagate_dbu.
    rewrite <- Hprob. exact Hprobdb_old. }
  assert (Hdbimplied_route : db_implied F Mroute).
  { unfold db_implied, Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn.
    msat_propagate_project_weak_field Hweak K (@msw_db_implied)
      (@msa_db_implied). }
  assert (Hlearntdb_route : learnt_db (ms_learnt Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_learnt_db)
      (@msa_learnt_db). }
  assert (Hentails_new : entails_clause F (denote_obj co_new)).
  { unfold db_matches_cnf in Hdbmatches_route. cbn in Hdbmatches_route.
    rewrite Forall_forall in Hdbmatches_route.
    assert (HCin : In (denote_obj co_new) (db_clauses prob_route)).
    { unfold db_clauses. apply in_map_iff.
      exists (scan_current, co_new). split; [reflexivity|].
      unfold prob_route. apply in_or_app. right. simpl. auto. }
    destruct (Hdbmatches_route _ HCin) as [C0 [HC0 HP0]].
    apply (entails_clause_perm F C0 (denote_obj co_new)).
    - apply Permutation_sym. exact HP0.
    - apply entails_clause_in. exact HC0. }
  apply (msat_propagate_wit66_route_ready_p7 n F A_arr K Mscan co scan_current p watch0
    false_lit a0 a1 tail retained rest prob_route (ms_learnt Mscan));
    assumption.
Qed.
(* The learnt-clause arm of wit_66.  Here ms_prob is untouched, so
   db_matches_cnf and db_complete transport by reduction, and the work is on
   db_implied and learnt_db: the new object is a permutation of a clause the
   formula already entails and keeps the learnt tag.  Concludes through
   msat_propagate_wit66_route_ready_p7 *)
Lemma msat_propagate_wit66_learnt_ready_p7 :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver)
         (co : clause_obj) (pre post : dbmap)
         (scan_current p watch0 false_lit a0 a1 : Z)
         (tail retained rest : list Z),
    solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ->
    db_wf n (msolver_db Mscan) ->
    In (scan_current, co) (msolver_db Mscan) ->
    co_lits co = a0 :: a1 :: tail ->
    ms_learnt Mscan = pre ++ (scan_current, co) :: post ->
    2 <= Zlength_aux 2 Z tail ->
    Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
    NoDup (map lit_var_c (a0 :: a1 :: tail)) ->
    Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail) ->
    Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail) ->
    false_lit = lit_neg_c p ->
    (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current) ->
    (forall l, Permutation (entry_watchers (scan_current, co) l)
       (entry_watchers (scan_current,
          clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)) ->
    ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0)) ->
    propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail) =
      watch0 :: false_lit :: tail ->
    propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0
      false_lit (a0 :: a1 :: tail) retained rest (ms_prob Mscan)
      (pre ++ (scan_current,
         clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
      (msolver_propagation_db_wmap_update Mscan (ms_prob Mscan)
        (pre ++ (scan_current,
           clause_obj_with_lits co (watch0 :: false_lit :: tail)) :: post)
        (ms_wm Mscan) (ms_wcaps Mscan)).
Proof.
  intros n F A_arr K Mscan co pre post scan_current p watch0 false_lit a0 a1
    tail retained rest Hsem Hdbwf Hin Hlits Hlearnt_split Hlen Hall Hnodup
    Hperm Hnew_false H_false_lit Hno_reason_ptr Hentry_perm Hwatchcases
    Hnew_eq.
  pose proof Hsem as Hscan_arms.
  destruct Hscan_arms as [Hlive | Hdead]; [|destruct Hdead as [Hzero _]; lia].
  destruct Hlive as
    [_ [Hweak [Hprop [_ [Hheapcovers [Hreasonless
      [Hlevel [Hp [Hprocessed [Hfrontier _]]]]]]]]]].
  set (new_lits := watch0 :: false_lit :: tail) in *.
  set (co_new := clause_obj_with_lits co new_lits) in *.
  set (learnt_route := pre ++ (scan_current, co_new) :: post) in *.
  set (Mroute := msolver_propagation_db_wmap_update Mscan (ms_prob Mscan)
    learnt_route (ms_wm Mscan) (ms_wcaps Mscan)) in *.
  assert (Hdbupdate : db_pair_lits_update (ms_prob Mscan)
      (ms_learnt Mscan) scan_current (a0 :: a1 :: tail)
      (propagation_normalized_clause watch0 false_lit
        (a0 :: a1 :: tail)) (ms_prob Mscan) learnt_route).
  { right. exists co, pre, post. repeat split; try assumption;
      try reflexivity.
    unfold learnt_route, co_new. rewrite Hnew_eq. reflexivity. }
  pose proof Hdbupdate as Hupdate_lits.
  rewrite Hnew_eq in Hupdate_lits.
  destruct (db_pair_lits_update_learnt_entry_bi__propagate_dbu
    _ _ _ _ _ _ _ Hperm Hupdate_lits) as [Hlearntforward _].
  assert (Hobjnew : obj_wf n co_new).
  { apply (msat_propagate_wit66_new_obj_wf_p7 n co watch0 false_lit a0 a1 tail); assumption. }
  assert (Hsplit_old : msolver_db Mscan =
      (ms_prob Mscan ++ pre) ++ (scan_current, co) :: post).
  { unfold msolver_db. rewrite Hlearnt_split.
    rewrite <- app_assoc. reflexivity. }
  assert (Hnewsplit : ms_prob Mscan ++ learnt_route =
      (ms_prob Mscan ++ pre) ++ (scan_current, co_new) :: post).
  { unfold learnt_route. rewrite <- app_assoc. reflexivity. }
  destruct (msat_propagate_wit66_route_db_wf_p7 n Mscan co co_new scan_current
      (ms_prob Mscan ++ pre) post (ms_prob Mscan) learnt_route
      Hdbwf Hobjnew Hsplit_old Hnewsplit Hentry_perm)
    as [Hkeys_route [Hlookup_other [Hcases [Hexpected_perm
       [Hselected_route Hdbwf_route]]]]].
  assert (Hdbmatches_old : db_matches_cnf F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_matches)
      (@msa_db_matches). }
  assert (Hdbimplied_old : db_implied F Mscan).
  { msat_propagate_project_weak_field Hweak K (@msw_db_implied)
      (@msa_db_implied). }
  assert (Hprobdb_route : prob_db (ms_prob Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_prob_db)
      (@msa_prob_db). }
  assert (Hdbmatches_route : db_matches_cnf F Mroute).
  { unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update, db_matches_cnf; cbn.
    unfold db_matches_cnf in Hdbmatches_old. exact Hdbmatches_old. }
  assert (Hdbimplied_route : db_implied F Mroute).
  { unfold db_implied in Hdbimplied_old |- *.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
    eapply db_implied_entries_transport__propagate_dbu;
      [exact Hlearntforward | exact Hdbimplied_old]. }
  assert (Hdbcomplete_route : db_complete F Mroute).
  { unfold solver_propagation_weak in Hweak.
    destruct Hweak as [_ Hweak].
    assert (Hold : db_complete F Mscan).
    { destruct K; [exact (msw_db_complete Hweak)
                  |exact (msa_db_complete Hweak)]. }
    unfold db_complete in Hold |- *.
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn. exact Hold. }
  assert (Hlearntdb_old : learnt_db (ms_learnt Mscan)).
  { msat_propagate_project_weak_field Hweak K (@msw_learnt_db)
      (@msa_learnt_db). }
  assert (Hlearntdb_route : learnt_db learnt_route).
  { unfold learnt_route, co_new.
    apply learnt_db_replace_lits__propagate_dbu.
    rewrite <- Hlearnt_split. exact Hlearntdb_old. }
  assert (Hentails_new : entails_clause F (denote_obj co_new)).
  { unfold db_implied in Hdbimplied_route.
    rewrite Forall_forall in Hdbimplied_route.
    apply Hdbimplied_route. unfold db_clauses. apply in_map_iff.
    exists (scan_current, co_new). split; [reflexivity|].
    unfold Mroute, msolver_propagation_db_wmap_update,
      msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
    unfold learnt_route. apply in_or_app. right. simpl. auto. }
  apply (msat_propagate_wit66_route_ready_p7 n F A_arr K Mscan co scan_current p watch0
    false_lit a0 a1 tail retained rest (ms_prob Mscan) learnt_route);
    assumption.
Qed.

(* Closes the spatial half of one wit_66 route arm.  The leading
   `entailer_with` leaves a fixed residue: the clause pointer's positivity and
   evenness (both read off the database well-formedness witness), the reason
   array whose stride stays symbolic in `ptr_size_Z` while the literal side has
   already been reduced to the 32-bit width, and the two statistics words that
   `cbn` printed as `nth (Pos.to_nat k)` instead of `Znth k`.  Each `try` arm
   handles one of those and is a no-op on the others, so the same closer serves
   the problem-clause arm and the learnt-clause arm without change *)
Ltac msat_propagate_wit66_route_close_p7 Mscan Hdbwf Hin :=
  (entailer_with ltac:(lia));
  (try (pose proof (db_wf_ptr_pos _ _ _ _ Hdbwf Hin); lia));
  (try (apply clause_ptr_mod2;
    eapply db_wf_even; [exact Hdbwf|exact Hin]));
  (try (unfold PtrArray.seg; cbn [Znth]; entailer_with ltac:(lia)));
  (try (fold (Znth 2 (ms_stats Mscan) 0);
    fold (Znth 3 (ms_stats Mscan) 0); entailer_with ltac:(lia)));
  (try (replace (nth (Pos.to_nat 2%positive) (ms_stats Mscan) 0)
    with (Znth 2 (ms_stats Mscan) 0) by reflexivity;
    replace (nth (Pos.to_nat 3%positive) (ms_stats Mscan) 0)
    with (Znth 3 (ms_stats Mscan) 0) by reflexivity;
    entailer_with ltac:(lia)));
  try apply store_ptr_undef_store_ptr.


(* Laying [xs] into the watch array at [dst], right after a prefix that already
   occupies [0, dst), leaves that prefix in place and puts [xs] immediately after
   it; the tail beyond the write is whatever was there. *)
Lemma msat_binary_watch_write_prefix_p7 :
  forall (xs mem prefix : list Z) (dst : Z),
      0 <= dst ->
      dst + Zlength xs <= Zlength mem ->
      Zlength prefix = dst ->
      sublist 0 dst mem = prefix ->
      exists tail,
        binary_watch_write dst xs mem = prefix ++ xs ++ tail.
Proof.
  intros xs.
  induction xs as [| a xs IH]; intros mem prefix dst Hdst0 Hbound Hplen Hpref.
  - simpl.
    rewrite Zlength_nil in Hbound.
    exists (sublist dst (Zlength mem) mem).
    simpl.
    rewrite <- Hpref.
    rewrite <- (sublist_split 0 (Zlength mem) dst mem) by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  - rewrite Zlength_cons in Hbound.
    pose proof (Zlength_nonneg xs).
    assert (Hidx : 0 <= dst < Zlength mem) by lia.
    simpl.
    destruct (IH (replace_Znth dst a mem)
      (prefix ++ (a :: nil)%list) (dst + 1))
      as [tail Htail].
    + lia.
    + rewrite Zlength_replace_Znth. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hplen. lia.
    + rewrite (replace_Znth_split 0 a dst mem Hidx).
      rewrite Hpref.
      replace (prefix ++ a :: sublist (dst + 1) (Zlength mem) mem)
        with ((prefix ++ (a :: nil)%list) ++
          sublist (dst + 1) (Zlength mem) mem)
        by (rewrite <- app_assoc; reflexivity).
      replace (dst + 1) with
        (Zlength (prefix ++ (a :: nil)%list)) by
        (rewrite Zlength_app, Zlength_cons, Zlength_nil, Hplen; lia).
      apply sublist_app_exact1.
    + exists tail.
      rewrite Htail.
      rewrite <- !app_assoc.
      reflexivity.
Qed.


(* One step of solver_reducedb's compaction: copying entry [i] over slot [j]
   leaves the kept prefix and the untouched suffix exactly as they were. *)
Lemma msat_db_compaction_shift_p7 :
  forall (words : list Z) (i j : Z),
    0 <= j -> j <= i -> i < Zlength words ->
    sublist 0 j words ++ sublist i (Zlength words) words =
    sublist 0 (j + 1) (replace_Znth j (Znth i words 0) words) ++
    sublist (i + 1) (Zlength words) (replace_Znth j (Znth i words 0) words).
Proof.
  intros words i j Hj Hji Hi.
  set (a := Znth i words 0).
  set (A := sublist 0 j words).
  set (B := sublist (j + 1) (Zlength words) words).
  assert (HA : Zlength A = j).
  { unfold A. apply Zlength_sublist0. lia. }
  assert (HBlen : Zlength B = Zlength words - (j + 1)).
  { unfold B. apply Zlength_sublist. lia. }
  assert (HR : replace_Znth j a words = A ++ a :: B).
  { unfold A, B, a.
    apply (replace_Znth_split 0 (Znth i words 0) j words). lia. }
  assert (HRlen : Zlength (A ++ a :: B) = Zlength words).
  { rewrite <- HR. apply Zlength_replace_Znth. }
  assert (HW : words = A ++ Znth j words 0 :: B).
  { unfold A, B. apply (list_Znth_split 0 words j). lia. }
  assert (HP : sublist 0 (j + 1) (A ++ a :: B) = A ++ a :: nil).
  { rewrite (sublist_split 0 (j + 1) j (A ++ a :: B)) by lia.
    rewrite (sublist_split_app_l 0 j A (a :: B)) by lia.
    rewrite (sublist_split_app_r j (j + 1) j A (a :: B)) by lia.
    replace (j - j) with 0 by lia.
    replace (j + 1 - j) with 1 by lia.
    f_equal.
    apply sublist_self. symmetry. exact HA. }
  assert (HS : sublist (i + 1) (Zlength words) (A ++ a :: B) =
               sublist (i + 1) (Zlength words) words).
  { rewrite HW at 3.
    rewrite (sublist_split_app_r (i + 1) (Zlength words) j A (a :: B)) by lia.
    rewrite (sublist_split_app_r (i + 1) (Zlength words) j A
      (Znth j words 0 :: B)) by lia.
    rewrite (sublist_cons2 (i + 1 - j) (Zlength words - j) a B) by
      (try lia; rewrite Zlength_cons, HBlen; lia).
    rewrite (sublist_cons2 (i + 1 - j) (Zlength words - j)
      (Znth j words 0) B) by
      (try lia; rewrite Zlength_cons, HBlen; lia).
    reflexivity. }
  rewrite HR, HP, HS.
  rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
  rewrite (sublist_single 0 i words) by lia.
  unfold a.
  rewrite app_assoc.
  simpl. reflexivity.
Qed.

(* ===== clause_activity return wits (1 proofs) ===== *)
Lemma proof_of_clause_activity_return_wit_1 : clause_activity_return_wit_1.
Proof.
  Unfold.
  right.
  intros c_pre a; intros.
  unfold msat_fp32_same, clause_act_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_activity which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_activity_which_implies_wit_1 : clause_activity_which_implies_wit_1.
Proof.
  Unfold.
  right.
  intros a c; intros.
  unfold clause_act_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_begin entail wits (1 proofs) ===== *)
Lemma proof_of_clause_begin_entail_wit_1 : clause_begin_entail_wit_1.
Proof.
  Unfold.
  right.
  intros c_pre.
  unfold clause_lits_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_begin return wits (1 proofs) ===== *)
Lemma proof_of_clause_begin_return_wit_1 : clause_begin_return_wit_1.
Proof.
  Unfold.
  right.
  intros c_pre; intros.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_from_lit return wits (1 proofs) ===== *)
Lemma proof_of_clause_from_lit_return_wit_1 : clause_from_lit_return_wit_1.
Proof.
  Unfold.
  right.
  intros l_pre; intros.
  unfold tag_of_lit.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_learnt return wits (1 proofs) ===== *)
Lemma proof_of_clause_learnt_return_wit_1 : clause_learnt_return_wit_1.
Proof.
  Unfold.
  right.
  intros c_pre header; intros.
  assert (Hland : Z.land header 1 = Z.rem header 2).
  { rewrite Zland_mod2. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  unfold clause_hdr_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_learnt which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_learnt_which_implies_wit_1 : clause_learnt_which_implies_wit_1.
Proof.
  Unfold.
  right.
  intros header c; intros.
  unfold clause_hdr_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_new entail wits (5 proofs) ===== *)
Lemma proof_of_clause_new_entail_wit_8 : clause_new_entail_wit_8.
Proof.
  (* D1: `wl` is no longer a local existential -- clause_new's contract now takes it
     as the spec ghost `cn_wl_clause_new_spec`.  QCP has no congruence closure, so
     the proof must spell the binder exactly as the STATE spells it. *)
  aggressive_pre_process.
  subst Mstage2.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
      (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) nil) < cap_prime ) as H_Zlength.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
      (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01 (ms_wcaps cn_M_clause_new_spec))
      cn_sel_clause_new_spec) cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as H_clause_new_stage_ready.
  bind_fact ( clause_new_reserved_rooms_gen 2 cn_words_clause_new_spec (msolver_with_clause_caps_gen
      cn_M_clause_new_spec learnt_cap1 (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
      (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec) cn_sel_clause_new_spec ) as H_clause_new_reserved_rooms.
  bind_fact ( lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <> lit_neg_c (Znth 1 cn_words_clause_new_spec 0) ) as
      H_lit_neg_c.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hphysical as Hshape.
  pose proof Hcert as Hcert_full.
  pose proof (clause_install_pending_cert_wf _ _ _ _ _ Hcert) as (_ & Hall & _).
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 Hall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 Hall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  pose proof (msi_size Hinv) as Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  pose proof (solver_shape_wcaps_len _ Hshape) as Hwcaps_len8.
  change (cn_n_clause_new_spec = ms_size cn_M_clause_new_spec) in Hsize.
  change (Zlength (ms_wm cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hwm_len.
  change (Zlength (replace_Znth
    (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
    (ms_wcaps cn_M_clause_new_spec)) =
    2 * ms_size cn_M_clause_new_spec) in Hwcaps_len8.
  assert (Hwmcaps_len :
    Zlength (ms_wm cn_M_clause_new_spec) =
    Zlength (replace_Znth
      (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
      (ms_wcaps cn_M_clause_new_spec))).
  { lia. }
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (replace_Znth
        (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
        (ms_wcaps cn_M_clause_new_spec))).
  { rewrite Zlength_replace_Znth in Hwcaps_len8 |- *.
    unfold lit_wf_c in Hneg0. lia. }
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (replace_Znth
        (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) watch_cap01
        (ms_wcaps cn_M_clause_new_spec))).
  { rewrite Zlength_replace_Znth in Hwcaps_len8 |- *.
    unfold lit_wf_c in Hneg1. lia. }
  assert (Hidx0w :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by lia.
  assert (Hidx1w :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by lia.
  destruct (msat_clause_new_stage_ready_bump_p7 cn_n_clause_new_spec cn_F_clause_new_spec
    cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec
    cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec learnt_cap1 watch_cap01 cap_prime
    ltac:(lia) H_clause_new_stage_ready) as (Hready' & Hinv' & Hcaps').
  pose proof (msat_clause_new_rooms_bump_p7 cn_M_clause_new_spec cn_words_clause_new_spec
    cn_sel_clause_new_spec learnt_cap1 watch_cap01 cap_prime Hidx0 Hidx1 H_lit_neg_c
    H_Zlength H_clause_new_reserved_rooms) as Hrooms'.
  assert (Hcap1 :
    Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps
        (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
          (replace_Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
            cap_prime
            (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
              watch_cap01 (ms_wcaps cn_M_clause_new_spec))) cn_sel_clause_new_spec)) 1 = cap_prime).
  { cbn. apply Znth_replace_Znth_Same. exact Hidx1. }
  assert (Hcap0 :
    Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps
        (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
          (replace_Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
            cap_prime
            (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
              watch_cap01 (ms_wcaps cn_M_clause_new_spec))) cn_sel_clause_new_spec)) 1 =
    Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps
        (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
          (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
            watch_cap01 (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) 1).
  { cbn. apply Znth_replace_Znth_Diff; try assumption. lia. }
  Exists cap_prime.
  rewrite Hcap1, Hcap0.
  sep_apply
    (clause_new_transaction_rest_at_replace_j__clause_new_gen
      s_pre cn_wl_clause_new_spec
      (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      cn_M_clause_new_spec learnt_cap1
      (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
        watch_cap01 (ms_wcaps cn_M_clause_new_spec))
      lvl_clause_new_spec cap_prime cn_sel_clause_new_spec ltac:(lia)
      Hwmcaps_len Hidx0w Hidx1w H_lit_neg_c).
  assert (Hwm_state :
    ms_wm
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
          cap_prime
          (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
            watch_cap01 (ms_wcaps cn_M_clause_new_spec))) cn_sel_clause_new_spec) =
    ms_wm
      (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
          watch_cap01 (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec)) by reflexivity.
  assert (Hlearnt_state :
    (solver_selected_db cn_sel_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
          cap_prime
          (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
            watch_cap01 (ms_wcaps cn_M_clause_new_spec))) cn_sel_clause_new_spec)) =
    (solver_selected_db cn_sel_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
          watch_cap01 (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec))) by reflexivity.
  assert (Hlearnt_cap_state :
    (solver_selected_cap cn_sel_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
          cap_prime
          (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
            watch_cap01 (ms_wcaps cn_M_clause_new_spec))) cn_sel_clause_new_spec)) =
    (solver_selected_cap cn_sel_clause_new_spec (msolver_with_clause_caps_gen cn_M_clause_new_spec learnt_cap1
        (replace_Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
          watch_cap01 (ms_wcaps cn_M_clause_new_spec)) cn_sel_clause_new_spec))) by reflexivity.
  rewrite Hwm_state, Hlearnt_state, Hlearnt_cap_state.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_new_entail_wit_9 : clause_new_entail_wit_9.
Proof.
  aggressive_pre_process;
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready;
  bind_fact ( size = Zlength cn_words_clause_new_spec ) as H_size;
  (try solve [entailer_with lia]).
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof (msi_size Hinv) as Hsize.
  change (cn_n_clause_new_spec = ms_size Mstage3) in Hsize.
  subst watch_words0 watch_words1 size.
  entailer_with lia.
  all: (unfold clause_new_stage_ready_root in H_clause_new_stage_ready);
    (destruct H_clause_new_stage_ready as
    (Hphysical' & Hlen & Hbound & Hcaps' & Hinv' & Hpending' & Hseed' & Hcert')).
  - entailer_with lia.
  - entailer_with lia.
  - pose proof (msi_size Hinv') as Hsize'.
    change (cn_n_clause_new_spec = ms_size Mstage3) in Hsize'.
    entailer_with lia.
  - try rewrite H_size.
    entailer_with lia; lia.
  - try rewrite H_size.
    (* The tag bit of this goal is spelled as the literal 1 rather than through the
              `learnt` hypothesis, so nothing has to be rewritten before the shift / land / lxor
              chain that reassembles the packed header word. *)
    entailer_with lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    change (2 ^ 1) with 2.
    rewrite signed_last_nbits_eq by (try lia; cbn; lia).
    assert (Hland : Z.land (Zlength cn_words_clause_new_spec * 2) cn_sel_clause_new_spec = 0).
    { assert (cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1) as [-> | ->] by lia.
      - apply Z.land_0_r.
      - rewrite land_1_mod2. apply Z_mod_mult. }
    rewrite <- Z.lxor_lor by exact Hland.
    symmetry.
    apply Z.add_nocarry_lxor.
    exact Hland.
Qed.

Lemma proof_of_clause_new_entail_wit_10 : clause_new_entail_wit_10.
Proof.
  aggressive_pre_process.
  entailer_with ltac:(lia).
  rewrite (sublist_split 0 (i + 1) i cn_words_clause_new_spec) by lia.
  rewrite (sublist_single 0 i cn_words_clause_new_spec) by lia.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.

Lemma proof_of_clause_new_entail_wit_12_1 : clause_new_entail_wit_12_1.
Proof.
  (* D1: this refold TAKES cn_wl_clause_new_spec but its conclusion re-HIDES wl,
     while clause_new_post_at_gen now demands the rep at that exact wl.  Hiding ->
     named-at-a-specific-wl is unprovable, so use the wl-named twin. *)
  (* Same D1/wl-binder note as in [proof_of_clause_new_entail_wit_8] above. *)
  (* The RHS spells the watch lists in their unfolded
          "Znth (lit_neg_c ...) (ms_wm Mstage3) nil" form, so the watch_words0 / watch_words1
          re-spelling rewrites that entail_wit_12_2 needs have nothing left to do here, and the
          two capacity side goals are already discharged by the entailer. *)
  aggressive_pre_process.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      1 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 -> cap_prime_3 = Znth (lit_neg_c (Znth 1
      cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      0 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 -> cap_prime_2 = Znth (lit_neg_c (Znth 0
      cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_2.
  bind_fact ( Zlength (db_words ((solver_selected_db cn_sel_clause_new_spec Mstage3))) < (solver_selected_cap
      cn_sel_clause_new_spec Mstage3) -> cap_prime = (solver_selected_cap cn_sel_clause_new_spec Mstage3) ) as
      H_Zlength_3.
  bind_fact ( size = Zlength cn_words_clause_new_spec ) as H_size.
  bind_fact ( database = (solver_selected_vec s_pre cn_sel_clause_new_spec) ) as H_database.
  bind_fact ( cn_n_clause_new_spec = ms_size Mstage3 ) as H_n_clause_new_spec.
  bind_fact ( watch0 = vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) ) as H_watch0.
  bind_fact ( watch1 = vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) ) as H_watch1.
  bind_fact ( 0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) ) as H_lit_neg_c.
  bind_fact ( lit_neg_c (Znth 0 cn_words_clause_new_spec 0) < 2 * cn_n_clause_new_spec ) as H_lit_neg_c_2.
  bind_fact ( 0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) ) as H_lit_neg_c_3.
  bind_fact ( lit_neg_c (Znth 1 cn_words_clause_new_spec 0) < 2 * cn_n_clause_new_spec ) as H_lit_neg_c_4.
  bind_fact ( clause_allocator_fresh Mstage3 c ) as H_clause_allocator_fresh.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  bind_fact ( Zlength (db_words ((solver_selected_db cn_sel_clause_new_spec Mstage3))) < (solver_selected_cap
      cn_sel_clause_new_spec Mstage3) ) as H_Zlength_4.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      0 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_5.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      1 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_6.
  pose proof H_clause_new_stage_ready as Hready.
  unfold clause_new_stage_ready_root in Hready.
  destruct Hready as
    (Hphysical & Hwords & Hwords_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof Hphysical as Hshape.
  (* Hcert is now [clause_install_pending_cert .. (solver_selected_is_learnt sel)];
     at a symbolic sel it is an undecided [if], so it does NOT destruct to the
     record arm's 7-tuple.  Only the three well-formedness facts are needed
     outside the model lemmas, and those are arm-independent. *)
  destruct (clause_install_pending_cert_wf _ _ _ _ _ Hcert)
    as (Hcert_len & Hlitwf & Hnodup).
  assert (Hselb : 0 <= cn_sel_clause_new_spec <= 1) by lia.
  assert (Hselarm : cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1) by lia.
  assert (Hne_var :
    lit_var_c (Znth 0 cn_words_clause_new_spec 0) <>
    lit_var_c (Znth 1 cn_words_clause_new_spec 0)).
  { exact (nodup_first_two_packed_vars__clause_new
      cn_words_clause_new_spec Hwords Hnodup). }
  assert (Hne :
    lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <>
    lit_neg_c (Znth 1 cn_words_clause_new_spec 0)).
  { intro Heq.
    pose proof (f_equal lit_var_c Heq) as Heq_var.
    rewrite !lit_var_c_neg in Heq_var.
    exact (Hne_var Heq_var). }
  assert (Hinv' :
    solver_support_inv cn_n_clause_new_spec (cn_F cn_F_clause_new_spec cn_words_clause_new_spec cn_sel_clause_new_spec) cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec (msolver_install_clause Mstage3 c cn_words_clause_new_spec (solver_selected_is_learnt cn_sel_clause_new_spec))).
  { apply solver_support_inv_install_clause__api_reentry; try assumption; try lia. }
  assert (Htransition :
    clause_new_success_transition_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec cn_words_clause_new_spec c cn_sel_clause_new_spec cn_root_clause_new_spec (msolver_install_clause Mstage3 c cn_words_clause_new_spec (solver_selected_is_learnt
          cn_sel_clause_new_spec))).
  { unfold clause_new_success_transition_root.
    exists Mstage3.
    split; [exact Hcaps |].
    split; [exact H_clause_allocator_fresh |].
    split; [reflexivity |].
    split; [exact Hinv' |].
    split; [exact Hpending |].
    split; [exact Hseed |].
    apply clause_install_cert_at_root__api_reentry; assumption. }
  assert (Hcap_db : cap_prime = (solver_selected_cap cn_sel_clause_new_spec Mstage3)).
  { apply H_Zlength_3. exact H_Zlength_4. }
  assert (Hcap0 : cap_prime_2 =
    Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage3) 1).
  { apply H_Zlength_2. exact H_Zlength_5. }
  assert (Hcap1 : cap_prime_3 =
    Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage3) 1).
  { apply H_Zlength. exact H_Zlength_6. }
  assert (Hlen3_size : 2 < size) by lia.
  assert (Hlen3 : 2 < Zlength cn_words_clause_new_spec).
  { rewrite <- H_size. exact Hlen3_size. }
  unfold clause_new_post_at_root.
  Left.
  entailer_with lia.
  Exists (msolver_install_clause Mstage3 c cn_words_clause_new_spec (solver_selected_is_learnt cn_sel_clause_new_spec))
      c.
  split_pure_spatial.
  - pose proof (solver_shape_wm_len Mstage3 Hshape) as Hwm_len.
    assert (Hidx0 :
      0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
        Zlength (ms_wm Mstage3)) by lia.
    assert (Hidx1 :
      0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
        Zlength (ms_wm Mstage3)) by lia.
    rewrite H_n_clause_new_spec, Hcap_db, Hcap0, Hcap1.
    rewrite H_database, H_watch0, H_watch1.
    transitivity
      (clause_new_transaction_installed_at_gen s_pre
         cn_wl_clause_new_spec lvl_clause_new_spec c Mstage3
         cn_words_clause_new_spec cn_sel_clause_new_spec c c **
       IntArray.seg begin_pre 0 (Zlength cn_words_clause_new_spec)
         cn_words_clause_new_spec ** clause_out_pre # Ptr |-> c).
    + unfold clause_new_transaction_installed_at_gen.
      unfold vecp_rep at 1 2 3.
      Exists p_prime p_prime_2 p_prime_3.
      unfold vecp_rep_at.
      (entailer_with int_auto);
      apply Zlength_nonneg.
    + unfold clause_new_transaction_installed_at_gen.
      rewrite <- H_database, <- H_watch0, <- H_watch1.
      sep_apply (clause_new_install_rep_at_refold__clause_new_gen_wl
        s_pre begin_pre clause_out_pre database watch0 watch1 cn_wl_clause_new_spec
        lvl_clause_new_spec Mstage3 cn_words_clause_new_spec c cn_sel_clause_new_spec
        Hselarm Hshape Hlen3 Hidx0 Hidx1 Hne H_database H_watch0 H_watch1).
      entailer_with lia.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Htransition.
Qed.

Lemma proof_of_clause_new_entail_wit_12_2 : clause_new_entail_wit_12_2.
Proof.
  (* Same D1/wl-hiding note as in [proof_of_clause_new_entail_wit_12_1] above. *)
  (* Same D1/wl-binder note as in [proof_of_clause_new_entail_wit_8] above. *)
  aggressive_pre_process.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil +:: retval_6) <=
      cap_prime_3 ) as H_Zlength.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      1 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 -> cap_prime_3 = Znth (lit_neg_c (Znth 1
      cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_2.
  bind_fact ( retval_6 = tag_of_lit (Znth (0 - 0) cn_words_clause_new_spec 0) ) as H_retval_6.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil +:: retval_4) <=
      cap_prime_2 ) as H_Zlength_3.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      0 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 -> cap_prime_2 = Znth (lit_neg_c (Znth 0
      cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_4.
  bind_fact ( retval_4 = tag_of_lit (Znth (1 - 0) cn_words_clause_new_spec 0) ) as H_retval_4.
  bind_fact ( Zlength (db_words ((solver_selected_db cn_sel_clause_new_spec Mstage3))) < (solver_selected_cap
      cn_sel_clause_new_spec Mstage3) -> cap_prime = (solver_selected_cap cn_sel_clause_new_spec Mstage3) ) as
      H_Zlength_5.
  bind_fact ( database = (solver_selected_vec s_pre cn_sel_clause_new_spec) ) as H_database.
  bind_fact ( cn_n_clause_new_spec = ms_size Mstage3 ) as H_n_clause_new_spec.
  bind_fact ( watch0 = vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) ) as H_watch0.
  bind_fact ( watch1 = vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) ) as H_watch1.
  bind_fact ( watch_words0 = Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil ) as
      H_watch_words0.
  bind_fact ( watch_words1 = Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil ) as
      H_watch_words1.
  bind_fact ( clause_allocator_fresh Mstage3 c ) as H_clause_allocator_fresh.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  bind_fact ( Zlength (db_words ((solver_selected_db cn_sel_clause_new_spec Mstage3))) < (solver_selected_cap
      cn_sel_clause_new_spec Mstage3) ) as H_Zlength_6.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      0 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_7.
  bind_fact ( Zlength (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage3) nil) < Znth (lit_neg_c (Znth
      1 cn_words_clause_new_spec 0)) (ms_wcaps Mstage3) 1 ) as H_Zlength_8.
  (* The goal and the two capacity bounds spell the watch word lists through
          [Znth _ (ms_wm Mstage3) nil].  H_watch_words0 / H_watch_words1 ARE those definitions,
          so fold them back here and let the cancellation step below unfold them again. *)
  rewrite <- H_watch_words0 in H_Zlength_3.
  rewrite <- H_watch_words1 in H_Zlength.
  rewrite <- H_watch_words0, <- H_watch_words1.
  unfold clause_new_stage_ready_root in H_clause_new_stage_ready.
  destruct H_clause_new_stage_ready as
    (Hphysical & Hlen & Hsize_bound & Hcaps & Hinv & Hpending & Hseed & Hcert).
  pose proof (clause_install_pending_cert_wf _ _ _ _ _ Hcert)
    as (Hone & Hwf & Hnodup).
  assert (Hlen2 : Zlength cn_words_clause_new_spec = 2) by lia.
  assert (Hselb : 0 <= cn_sel_clause_new_spec <= 1) by lia.
  assert (Hselarm : cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1) by lia.
  pose proof (first_two_neg_distinct_eq2__clause_new
    cn_words_clause_new_spec Hlen2 Hnodup) as Hdistinct.
  pose proof Hphysical as Hshape.
  pose proof (solver_shape_wm_len Mstage3 Hshape) as Hwmlen.
  assert (Hi :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm Mstage3)).
  { rewrite Hwmlen, <- H_n_clause_new_spec. lia. }
  assert (Hj :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm Mstage3)).
  { rewrite Hwmlen, <- H_n_clause_new_spec. lia. }
  assert (Hcapdb : cap_prime = (solver_selected_cap cn_sel_clause_new_spec Mstage3))
    by (apply H_Zlength_5; exact H_Zlength_6).
  assert (Hcap0 : cap_prime_2 =
    Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage3) 1)
    by (apply H_Zlength_4; exact H_Zlength_7).
  assert (Hcap1 : cap_prime_3 =
    Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage3) 1)
    by (apply H_Zlength_2; exact H_Zlength_8).
  unfold clause_new_post_at_root.
  Left.
  Exists (msolver_install_clause Mstage3 c cn_words_clause_new_spec (solver_selected_is_learnt cn_sel_clause_new_spec))
      c.
  split_pure_spatial.
  2: {
    entailer_with ltac:(lia).
    unfold clause_new_success_transition_root.
    exists Mstage3. split; [exact Hcaps |].
    split; [exact H_clause_allocator_fresh |].
    split; [reflexivity |].
    split.
    - apply solver_support_inv_install_clause__api_reentry; try assumption; try lia.
    - split; [exact Hpending |].
      split; [exact Hseed |].
      apply clause_install_cert_at_root__api_reentry; assumption.
  }
  rewrite H_database, H_watch0, H_watch1, H_watch_words0, H_watch_words1,
    H_retval_6, H_retval_4, Hcapdb, Hcap0, Hcap1, H_n_clause_new_spec.
  rewrite H_watch_words1, H_retval_6, Hcap1 in H_Zlength.
  rewrite H_watch_words0, H_retval_4, Hcap0 in H_Zlength_3.
  replace (0 - 0) with 0 by lia.
  replace (1 - 0) with 1 by lia.
  transitivity
    (clause_new_transaction_installed_at_gen s_pre
       cn_wl_clause_new_spec lvl_clause_new_spec c Mstage3 cn_words_clause_new_spec
       cn_sel_clause_new_spec (tag_of_lit (Znth 1 cn_words_clause_new_spec 0))
       (tag_of_lit (Znth 0 cn_words_clause_new_spec 0)) **
     IntArray.seg begin_pre 0 (Zlength cn_words_clause_new_spec)
       cn_words_clause_new_spec ** clause_out_pre # Ptr |-> c).
  {
    unfold clause_new_transaction_installed_at_gen, vecp_rep, vecp_rep_at.
    Exists p_prime p_prime_2 p_prime_3.
    entailer_with ltac:(lia).
    unfold vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
    entailer_with ltac:(lia).
    all: apply Zlength_nonneg.
  }
  unfold clause_new_transaction_installed_at_gen.
  sep_apply (clause_new_install_spatial_refold__clause_new_gen_wl
    s_pre cn_wl_clause_new_spec Mstage3 cn_words_clause_new_spec
    lvl_clause_new_spec c cn_sel_clause_new_spec
    Hselarm Hshape Hlen2 Hi Hj Hdistinct).
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_new partial_solve wits (14 proofs) ===== *)
Lemma proof_of_clause_new_partial_solve_wit_4_pure : clause_new_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( cn_n_clause_new_spec = ms_size cn_M_clause_new_spec ) as H_n_clause_new_spec;
  bind_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall;
  bind_fact ( solver_support_inv cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec cn_M_clause_new_spec ) as H_msolver_inv.
  all: (pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 H_Forall ltac:(lia)) as Hlit);
    (pose proof (msi_shape H_msolver_inv) as Hshape);
    (unfold lit_wf_c in Hlit);
    (unfold solver_shape in Hshape);
    (destruct Hshape as (_ & _ & Htwice & _));
    (change (2 * ms_size cn_M_clause_new_spec <= INT_MAX) in Htwice);
    (rewrite <- H_n_clause_new_spec in Htwice);
    (entailer_with ltac:(lia));
    (replace (0 - 0) with 0 by lia);
    (lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_5_pure : clause_new_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall;
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 H_Forall ltac:(lia)) as Hlit;
    pose proof (lit_neg_c_wf cn_n_clause_new_spec _ Hlit) as Hneg;
    unfold lit_wf_c in Hneg;
    entailer_with ltac:(lia);
    replace (0 - 0) with 0 in * by lia;
    lia.
Qed.

Lemma proof_of_clause_new_partial_solve_wit_7_pure : clause_new_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( cn_n_clause_new_spec = ms_size cn_M_clause_new_spec ) as H_n_clause_new_spec;
  bind_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall;
  bind_fact ( solver_support_inv cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec cn_M_clause_new_spec ) as H_msolver_inv.
  all: (pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 H_Forall ltac:(lia)) as Hlit);
    (pose proof (msi_shape H_msolver_inv) as Hshape);
    (unfold lit_wf_c in Hlit);
    (unfold solver_shape in Hshape);
    (destruct Hshape as (_ & _ & Htwice & _));
    (change (2 * ms_size cn_M_clause_new_spec <= INT_MAX) in Htwice);
    (rewrite <- H_n_clause_new_spec in Htwice);
    (entailer_with ltac:(lia));
    (replace (1 - 0) with 1 by lia);
    (lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_8_pure : clause_new_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall;
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 H_Forall ltac:(lia)) as Hlit;
    pose proof (lit_neg_c_wf cn_n_clause_new_spec _ Hlit) as Hneg;
    unfold lit_wf_c in Hneg;
    entailer_with ltac:(lia);
    replace (1 - 0) with 1 in * by lia;
    lia.
Qed.

Lemma proof_of_clause_new_partial_solve_wit_12_pure : clause_new_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process;
  try replace (0 - 0) with 0 in * by lia;
    try replace (1 - 0) with 1 in * by lia;
    subst retval retval_2 retval_3 retval_4;
    msat_manual_entailer_with lia.
Qed.

Lemma proof_of_clause_new_partial_solve_wit_13_pure : clause_new_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process;
  prop_apply_p (vecp_rep_bounds__clause_new
    database (db_words ((solver_selected_db cn_sel_clause_new_spec cn_M_clause_new_spec)))
    ((solver_selected_cap cn_sel_clause_new_spec cn_M_clause_new_spec)));
    Intros_p Hbounds;
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_14_pure : clause_new_partial_solve_wit_14_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( watch_words0 = Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)) (ms_wm Mstage1) nil ) as
      H_watch_words0.
  (* The bound is stated on the binder `watch_words0` while
          [vecp_rep_bounds__clause_new] delivers it on the unfolded Znth form; the equation
          H_watch_words0 bridges the two spellings before Hbounds applies. *)
  all: (prop_apply_p (vecp_rep_bounds__clause_new
    watch0
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm Mstage1) (@nil Z))
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage1) 1)));
    (Intros_p Hbounds);
    (entailer_with lia);
    (rewrite H_watch_words0);
    (lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_15_pure : clause_new_partial_solve_wit_15_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( watch_words1 = Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)) (ms_wm Mstage2) nil ) as
      H_watch_words1.
  (* As in wit_14_pure: H_watch_words1 bridges `watch_words1` to its Znth form
          before Hbounds applies. *)
  all: (prop_apply_p (vecp_rep_bounds__clause_new
    watch1
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wm Mstage2) (@nil Z))
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps Mstage2) 1)));
    (Intros_p Hbounds);
    (entailer_with lia);
    (rewrite H_watch_words1);
    (lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_17_pure : clause_new_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  unfold clause_new_stage_ready_root in H_clause_new_stage_ready.
  destruct H_clause_new_stage_ready as [_ [Hlen _]].
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_37_pure : clause_new_partial_solve_wit_37_pure.
Proof.
  aggressive_pre_process;
  prop_apply_p (vecp_rep_bounds__clause_new
    database (db_words ((solver_selected_db cn_sel_clause_new_spec Mstage3))) ((solver_selected_cap
        cn_sel_clause_new_spec Mstage3)));
    Intros_p Hbounds;
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_new_partial_solve_wit_41_pure : clause_new_partial_solve_wit_41_pure.
Proof.
  aggressive_pre_process;
  msat_clause_new_watch_bounds_p7 watch0 watch_words0 cn_words_clause_new_spec Mstage3.
Qed.

Lemma proof_of_clause_new_partial_solve_wit_42_pure : clause_new_partial_solve_wit_42_pure.
Proof.
  aggressive_pre_process;
  msat_clause_new_watch_bounds_p7 watch0 watch_words0 cn_words_clause_new_spec Mstage3.
Qed.

Lemma proof_of_clause_new_partial_solve_wit_45_pure : clause_new_partial_solve_wit_45_pure.
Proof.
  (* The RHS also asks for the nonnegativity of the watch list in its unfolded Znth
     spelling, which Hcap only states for `watch_words1`; Zlength_nonneg discharges it
     directly. *)
  LLM_pre_process ltac:(lia). unfold vecp_rep at 1. Intros p. unfold vecp_rep_at at 1.
  coq_prop_lift. apply coq_prop_andp_left. intros Hcap. entailer_with lia. apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_new_partial_solve_wit_48_pure : clause_new_partial_solve_wit_48_pure.
Proof.
  (* Same RHS-nonnegativity note as in [proof_of_clause_new_partial_solve_wit_45_pure] above. *)
  LLM_pre_process ltac:(lia). unfold vecp_rep at 1. Intros p. unfold vecp_rep_at at 1.
  coq_prop_lift. apply coq_prop_andp_left. intros Hcap. entailer_with lia. apply Zlength_nonneg.
Qed.

(* ===== clause_new which_implies wits (5 proofs) ===== *)
Lemma proof_of_clause_new_which_implies_wit_1 : clause_new_which_implies_wit_1.
Proof.
  (* D1: the rep is now `solver_rep_levels_wl_at`, which makes `wl` a PARAMETER --
     so the existential is gone: `Intros` loses a name and the matching `Exists`
     disappears entirely.  Remaining uses re-spelled at the spec ghost. *)
  LLM_pre_process ltac:(lia).
  bind_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall.
  bind_fact ( solver_support_inv cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec cn_M_clause_new_spec ) as H_msolver_inv.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  pose proof (msi_size H_msolver_inv) as Hsize.
  change (cn_n_clause_new_spec = ms_size cn_M_clause_new_spec) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  change (Zlength (ms_wm cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hwm_len.
  pose proof (solver_shape_wcaps_len _ Hshape) as Hcaps_len.
  change (Zlength (ms_wcaps cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hcaps_len.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 H_Forall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 H_Forall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg0; lia).
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg1; lia).
  assert (Hne :
    lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <>
    lit_neg_c (Znth 1 cn_words_clause_new_spec 0)).
  { apply first_two_neg_distinct_ge2__clause_new; assumption. }
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  unfold wlists_rep at 1. coq_prop_lift.
  apply coq_prop_andp_left. intros Hwlshape.
  sep_apply (wlists_two_remainder_focus__clause_new
    cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
    (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
    (ms_wm cn_M_clause_new_spec) (ms_wcaps cn_M_clause_new_spec)
    ltac:(lia) Hidx0 Hidx1 Hne).
  sep_apply (vecp_rep_distinct__clause_new
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0)))
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil)
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps cn_M_clause_new_spec) 1)
    (vecp_slot cn_wl_clause_new_spec (lit_neg_c (Znth 1 cn_words_clause_new_spec 0)))
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil)
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps cn_M_clause_new_spec) 1)).
  coq_prop_lift. apply coq_prop_andp_left. intros Hslots.
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_ptrs_rep, solver_var_arrays_rep, solver_trail_array_rep,
    clause_new_scalars_frame, clause_new_vecs_frame_gen,
    clause_new_ptrs_frame.
  Exists act asg opos rsn trl tgs.
  entailer_with ltac:(lia).
  unfold solver_wlists_handle, db_words.
  sep_apply (wlists_two_remainder_refold__act_clause_bump
    cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
    (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
    (ms_wm cn_M_clause_new_spec) (ms_wcaps cn_M_clause_new_spec)
    ltac:(lia) Hidx0 Hidx1 Hne).
  unfold wlists_rep. entailer_with ltac:(lia).
  rewrite Hsize. entailer_with ltac:(lia).
  (* the two databases still have to be SORTED into (selected, other); that is
     decided by the index and by nothing else, so split on it. *)
  assert (cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1)
    as [-> | ->] by lia.
  (* entailer_with unfolds the spatial parts and re-exposes selector
     applications the first normalisation never saw.  At a CONCRETE index the
     selectors simply reduce, so unfold is exactly right here -- it is only at
     a symbolic index that unfolding is the wrong move. *)
  - cn_at_prob. entailer_with ltac:(lia).
    replace (1 - 0) with 1 by lia.
    unfold solver_selected_db, solver_selected_cap, solver_selected_vec; cbn.
    entailer_with ltac:(lia).
  - cn_at_learnt. entailer_with ltac:(lia).
    replace (1 - 1) with 0 by lia.
    unfold solver_selected_db, solver_selected_cap, solver_selected_vec; cbn.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_new_which_implies_wit_2 : clause_new_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( endvar = begin + Zlength cn_words_clause_new_spec * sizeof ( INT ) ) as H_endvar.
  rewrite sizeof_int in *.
  entailer_with ltac:(lia).
  rewrite H_endvar.
  replace (begin + Zlength cn_words_clause_new_spec * 4 - begin)
    with (Zlength cn_words_clause_new_spec * 4) by lia.
  rewrite Z.quot_mul by lia. reflexivity.
Qed.

Lemma proof_of_clause_new_which_implies_wit_3 : clause_new_which_implies_wit_3.
Proof.
  (* Same D1/wl-binder note as in [proof_of_clause_new_entail_wit_8] above. *)
  LLM_pre_process ltac:(lia).
  subst watch0 watch1.
  bind_fact ( Forall (lit_wf_c cn_n_clause_new_spec) cn_words_clause_new_spec ) as H_Forall.
  bind_fact ( solver_support_inv cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_root_clause_new_spec cn_M_clause_new_spec ) as H_msolver_inv.
  pose proof (msi_shape H_msolver_inv) as Hshape.
  pose proof (msi_size H_msolver_inv) as Hsize.
  change (cn_n_clause_new_spec = ms_size cn_M_clause_new_spec) in Hsize.
  pose proof (solver_shape_wm_len _ Hshape) as Hwm_len.
  change (Zlength (ms_wm cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hwm_len.
  pose proof (solver_shape_wcaps_len _ Hshape) as Hcaps_len.
  change (Zlength (ms_wcaps cn_M_clause_new_spec) =
    2 * ms_size cn_M_clause_new_spec) in Hcaps_len.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 0 H_Forall ltac:(lia)) as Hlit0.
  pose proof (Forall_Znth_elim Z (lit_wf_c cn_n_clause_new_spec)
    cn_words_clause_new_spec 0 1 H_Forall ltac:(lia)) as Hlit1.
  pose proof (lit_neg_c_wf _ _ Hlit0) as Hneg0.
  pose proof (lit_neg_c_wf _ _ Hlit1) as Hneg1.
  assert (Hidx0 :
    0 <= lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg0; lia).
  assert (Hidx1 :
    0 <= lit_neg_c (Znth 1 cn_words_clause_new_spec 0) <
      Zlength (ms_wm cn_M_clause_new_spec)) by
    (unfold lit_wf_c in Hneg1; lia).
  assert (Hne :
    lit_neg_c (Znth 0 cn_words_clause_new_spec 0) <>
    lit_neg_c (Znth 1 cn_words_clause_new_spec 0)).
  { apply first_two_neg_distinct_ge2__clause_new; assumption. }
  unfold wlists_rep at 1. coq_prop_lift.
  apply coq_prop_andp_left. intros Hwlshape.
  sep_apply (wlists_two_remainder_focus__clause_new
    cn_wl_clause_new_spec (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
    (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
    (ms_wm cn_M_clause_new_spec) (ms_wcaps cn_M_clause_new_spec)
    ltac:(lia) Hidx0 Hidx1 Hne).
  Exists (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wcaps cn_M_clause_new_spec) 1)
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wcaps cn_M_clause_new_spec) 1)
    (Znth (lit_neg_c (Znth 1 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil)
    (Znth (lit_neg_c (Znth 0 cn_words_clause_new_spec 0))
      (ms_wm cn_M_clause_new_spec) nil).
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_clause_new_which_implies_wit_4 : clause_new_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( clause_new_reserved_rooms_gen 3 cn_words_clause_new_spec Mstage3 cn_sel_clause_new_spec ) as
      H_clause_new_reserved_rooms.
  unfold clause_new_reserved_rooms_gen in H_clause_new_reserved_rooms.
  (entailer_with ltac:(lia));
  apply H_clause_new_reserved_rooms; lia.
Qed.

Lemma proof_of_clause_new_which_implies_wit_5 : clause_new_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( clause_new_stage_ready_root cn_n_clause_new_spec cn_F_clause_new_spec cn_A_arr_clause_new_spec cn_A_inst_clause_new_spec cn_M_clause_new_spec Mstage3 cn_words_clause_new_spec cn_sel_clause_new_spec cn_root_clause_new_spec ) as
      H_clause_new_stage_ready.
  split_pure_spatial.
  { entailer_with ltac:(lia). }
  split_pures.
  { dump_pre_spatial. exact H_clause_new_stage_ready. }
  sep_apply (MiniSatClause_undef_db_distinct
    c size ((solver_selected_db cn_sel_clause_new_spec Mstage3))).
  coq_prop_lift. apply coq_prop_andp_left. intros Hlearnt.
  unfold clause_new_transaction_rest_at_gen, clause_new_frame_at_gen.
  Intros act asg opos rsn trl tgs.
  sep_apply (MiniSatClause_undef_db_distinct
    c size (solver_selected_db (1 - cn_sel_clause_new_spec) Mstage3)).
  coq_prop_lift. apply coq_prop_andp_left. intros Hprob.
  unfold MiniSatClause.undef at 1. coq_prop_lift.
  apply coq_prop_andp_left. intros Hptr.
  unfold MiniSatClause.rep at 1. coq_prop_lift.
  apply coq_prop_andp_left. intros Hbinary_ptr.
  destruct (Z.eq_dec c (ms_binary Mstage3)) as [Heq | Hbinary].
  { subst c.
    sep_apply (store_int_undef_store_int
      (clause_hdr_addr (ms_binary Mstage3))
      (clause_hdr_word false (Zlength (ms_binary_lits Mstage3)))).
    sep_apply (dup_undef_store_int (clause_hdr_addr (ms_binary Mstage3))).
    entailer_with ltac:(lia). }
  dump_pre_spatial.
  unfold clause_allocator_fresh, msolver_db.
  repeat split; try tauto.
  { apply clause_ptr_even. tauto. }
  { (* membership in the whole database: at a symbolic index the selected and
       complementary halves are unrelated atoms, so tauto has nothing to chain.
       The index decides which is which and nothing else does. *)
    rewrite map_app, in_app_iff.
    assert (cn_sel_clause_new_spec = 0 \/ cn_sel_clause_new_spec = 1)
      as [-> | ->] by lia; [ cn_at_prob | cn_at_learnt ]; tauto. }
Qed.

(* ===== clause_setactivity return wits (1 proofs) ===== *)
Lemma proof_of_clause_setactivity_return_wit_1 : clause_setactivity_return_wit_1.
Proof.
  Unfold.
  right.
  intros a_pre c_pre; intros.
  unfold clause_act_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_setactivity which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_setactivity_which_implies_wit_1 : clause_setactivity_which_implies_wit_1.
Proof.
  Unfold.
  right.
  intros old c; intros.
  unfold clause_act_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_size return wits (1 proofs) ===== *)
Lemma proof_of_clause_size_return_wit_1 : clause_size_return_wit_1.
Proof.
  Unfold.
  right.
  intros c_pre header; intros.
  assert (Hshift : Z.shiftr header 1 = header ÷ 2).
  { rewrite Z.quot_div_nonneg by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    reflexivity. }
  unfold clause_hdr_addr.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_size which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_size_which_implies_wit_1 : clause_size_which_implies_wit_1.
Proof. exact proof_of_clause_learnt_which_implies_wit_1. Qed.

(* ===== lit_sign return wits (1 proofs) ===== *)
Lemma proof_of_lit_sign_return_wit_1 : lit_sign_return_wit_1.
Proof.
  Unfold.
  right.
  intros l_pre; intros.
  assert (Hsign : Z.land l_pre 1 = lit_sign_c l_pre).
  { rewrite land_1_mod2. unfold lit_sign_c.
    destruct (Z.odd l_pre) eqn:Hodd.
    - apply Z.odd_spec in Hodd. destruct Hodd as [k ->].
      apply Zmod2_pack. lia.
    - assert (Heven : Z.even l_pre = true).
      { rewrite <- Z.negb_odd, Hodd. reflexivity. }
      apply Z.even_spec in Heven. destruct Heven as [k ->].
      replace (2 * k) with (2 * k + 0) by lia.
      apply Zmod2_pack. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== lit_var return wits (1 proofs) ===== *)
Lemma proof_of_lit_var_return_wit_2_zero_index : lit_var_return_wit_2_zero_index.
Proof.
  Unfold.
  right; intros.
  unfold lit_var_c in *.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  assert (Hlo : 0 <= l_pre / 2) by (apply Z.div_pos; lia).
  assert (Hhi : l_pre / 2 < Zlength lv_assigns_zero_index)
    by (apply Z.div_lt_upper_bound; lia).
  msat_manual_entailer_with ltac:(assumption).
Qed.

(* ===== solver_analyze entail wits (13 proofs) ===== *)
(* Peel one named pure fact from the analyze entry postcondition.  Callers
   list all eight facts in their generated order before touching the heap. *)
Tactic Notation "msat_analyze_entry_fact_p7" tactic3(close_fact) :=
  apply _derivable1_andp_intros;
  [ apply derivable1s_coq_prop_r; close_fact | idtac ].

Lemma proof_of_solver_analyze_entail_wit_2 : solver_analyze_entail_wit_2.
Proof.
  Unfold.
  left. intros.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K M0 anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( propagation_conflict_cert anz_n anz_F M0 C ) as H_propagation_conflict_cert.
  bind_fact ( conflict_ptr_denotes M0 c_pre C ) as H_conflict_ptr_denotes.
  bind_fact ( ms_root_level M0 < Zlength (mt_lim (ms_core M0)) ) as H_ms_root_level.
  bind_fact ( ms_tags M0 = repeat_Z 0 anz_n ) as H_ms_tags.
  bind_fact ( ms_tagged M0 = nil ) as H_ms_tagged.
  bind_fact ( msolver_seed_shadow M0 ) as H_msolver_seed_shadow.
  bind_fact ( 2 * anz_n <= INT_MAX ) as H_two_n_le_int_max.
  destruct (msat_analyze_cancel_ready_core_p7 anz_n anz_F anz_A_arr K M0 anz_focus
    H_analysis_cancel_ready)
    as (Htrail & Hlim & Hroot_nonnegative & Htrail_length & Hbinary_nonzero & Hdb
        & Hshape_from_lengths).
  assert (Hlim_positive : 0 < Zlength (mt_lim (ms_core M0))) by lia.
  assert (Hlim_index : 0 <= 0 < Zlength (mt_lim (ms_core M0))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 0
    (mtw_lim_range Htrail) Hlim_index) as Hfirst_boundary.
  destruct Hfirst_boundary as [Hboundary_nonnegative Htrail_positive].
  rewrite Htrail_length in Htrail_positive.
  assert (Hqtail_positive : 0 < ms_qtail M0) by lia.
  assert (Hn_positive : 0 < anz_n) by lia.
  assert (Htags : analysis_tags_exact anz_n (ms_tags M0) (ms_tagged M0)).
  {
    unfold analysis_tags_exact.
    rewrite H_ms_tags, H_ms_tagged.
    unfold repeat_Z.
    repeat split.
    - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity.
    - constructor.
    - constructor.
    - induction (Z.to_nat anz_n) as [| k IH]; simpl.
      + constructor.
      + constructor; [tauto | exact IH].
    - intro Hz. rewrite Znth_repeat in Hz. lia.
    - intro Hin. contradiction.
  }
  assert (Hloop :
    analyze_resolution_loop_inv anz_n anz_F anz_A_arr K M0 anz_focus AnalyzeInitial
      c_pre C ((-2) :: nil) 0 (ms_qtail M0 - 1) (-2)).
  {
    unfold analyze_resolution_loop_inv.
    split; [exact H_analysis_cancel_ready |].
    split; [lia |].
    split; [cbn; lia |].
    split; [exact H_ms_root_level |].
    split; [exact Htags |].
    cbn.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [lia |].
    split; [exact H_propagation_conflict_cert |].
    split; [exact H_conflict_ptr_denotes |].
    split; [exact H_ms_tagged |].
    cbn [lits_denote]. reflexivity.
  }
  assert (Hconflict_nonzero : c_pre <> 0).
  {
    unfold conflict_ptr_denotes in H_conflict_ptr_denotes.
    destruct H_conflict_ptr_denotes as [[Hptr [_ _]] | [co [_ [Hin _]]]].
    - rewrite Hptr. exact Hbinary_nonzero.
    - pose proof (db_wf_ptr_pos anz_n (msolver_db M0) c_pre co Hdb Hin).
      lia.
  }
  assert (Hcore_refl : analysis_core_equiv M0 M0).
  { unfold analysis_core_equiv. repeat split; reflexivity. }
  assert (Hveci_bounds_preserved :
    veci_rep learnt_pre (z_nil +:: (-2)) learnt_cap0
    |-- “ 0 <= Zlength (z_nil +:: (-2)) <= learnt_cap0 /\
          0 < learnt_cap0 <= INT_MAX ” &&
        veci_rep learnt_pre (z_nil +:: (-2)) learnt_cap0).
  {
    unfold veci_rep, veci_rep_at.
    Intros learnt_ptr.
    Exists learnt_ptr.
    entailer_with ltac:(lia).
  }
  pose proof (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K M0 anz_focus H_analysis_cancel_ready) as Hreason_core.
  destruct Hreason_core as [Hn_size _].
  Exists learnt_cap0 AnalyzeInitial C ((-2) :: nil) M0.
  sep_apply Hveci_bounds_preserved.
  Intros_p Hveci_bounds.
  destruct Hveci_bounds as
    [[Hwords_nonnegative Hwords_cap] [Hcap_positive Hcap_max]].
  (* The loop enters with the literal one-element learnt vector; spell it
     the way the postcondition does, so the terminal cancel is syntactic. *)
  assert (Hwords_lit : z_nil +:: (-2) = (-2) :: nil) by reflexivity.
  rewrite Hwords_lit in Hwords_nonnegative, Hwords_cap |- *.
  (* Discharge the eight pure conjuncts against hypotheses already in scope,
     so that the [ms_size] rewrite below cannot disturb them and what is left
     is the bare spatial closure -- which is then the goal itself, so no
     [sep_apply] has to re-associate a 33-atom hypothesis into a 34-atom LHS. *)
  msat_analyze_entry_fact_p7 (exact Hcore_refl).
  msat_analyze_entry_fact_p7 (exact H_msolver_seed_shadow).
  msat_analyze_entry_fact_p7 (exact Hconflict_nonzero).
  msat_analyze_entry_fact_p7 (exact Hloop).
  msat_analyze_entry_fact_p7 (exact H_ms_root_level).
  msat_analyze_entry_fact_p7 (exact H_two_n_le_int_max).
  msat_analyze_entry_fact_p7 (lia).
  msat_analyze_entry_fact_p7 (lia).
  rewrite Hn_size.
  prop_apply solver_analyze_frame_stats_len.
  Intros_p Hstats_shape.
  prop_apply (DoubleArray.seg_Zlength activity_ptr 0
    (ms_size M0) (ms_activity M0)).
  Intros_p Hactivity_len.
  prop_apply (IntArray.seg_Zlength orderpos_ptr 0
    (ms_size M0) (ms_orderpos M0)).
  Intros_p Horder_len.
  prop_apply (CharArray.seg_Zlength tags_ptr 0
    (ms_size M0) (ms_tags M0)).
  Intros_p Htags_len.
  assert (Hactivity_shape :
    Zlength (ms_activity M0) = ms_size M0) by lia.
  assert (Horder_shape :
    Zlength (ms_orderpos M0) = ms_size M0) by lia.
  assert (Htags_shape :
    Zlength (ms_tags M0) = ms_size M0) by lia.
  assert (Hshape : solver_shape M0)
    by (apply Hshape_from_lengths; assumption).
  (* The bundle rebuild is [analyze_frame_join] (lib.v): it re-folds the
     scalar/fp/vector/stats bundles in one step, which is what the hand-rolled
     [R]/[Hframe_split]/[Hstats_suffix] triple used to do by hand. *)
  (* [analyze_frame_join] consumes the [stack] vector and the two literal
     counters, which the entry cut carries folded inside
     [solver_analyze_inert_at]; open the bundle so the join sees its atoms. *)
  unfold solver_analyze_inert_at.
  Intros.
  sep_apply (analyze_frame_join s_pre M0 anz_wl).
  Intros asg.
  unfold solver_rep_analyze_at, solver_rep_at.
  Exists activity_ptr asg orderpos_ptr.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_trail_array_rep.
  unfold msat_false.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_analyze_entail_wit_6 : solver_analyze_entail_wit_6.
Proof.
  Unfold.
  left. intros.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  assert (Horderpos_len : Zlength orderpos1 = anz_n).
  { unfold order_heap_wf, heap_wf in H_order_heap_wf. cbn in H_order_heap_wf. tauto. }
  Exists var_inc1 activity1 heap1 orderpos1.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_7_1 : solver_analyze_entail_wit_7_1.
Proof.
  unfold solver_analyze_entail_wit_7_1, solver_analyze_open_at.
  Unfold.
  right.
  msat_analyze_e7_bind_facts_p7.
  pose proof H_loop_inv as Hloop.
  rewrite H_phase in Hloop.
  destruct (msat_analyze_e7_ready_semantics_p7
    anz_n anz_F anz_A_arr K Mcur_2 anz_focus H_cancel_ready)
    as (Htrailwf & Hstable & Htrailimpl & Hrootunit).
  destruct (msat_analyze_e7_select_bridge_p7
    anz_n anz_F anz_A_arr K Mcur_2 anz_focus c ind cnt p x Ccur_2
    words_2 S0 R0 learnt0 Hloop H_reason_target H_is_tag H_x_in_S0 H_cnt_len
    H_analyze_inv H_tagged_perm H_shape Htrailwf Hstable Hrootunit) as
    (HCshapeX & Horder0 & Hrank_sel & HvalidA & HentA & HCndA & HinvNew &
     HpendS & HresolvedRanks & Htags & Hind & Hwords & Hroot &
     Hindvarrange & HrangeXn & Hqneq).
  destruct (msat_analyze_e7_resolve_sets_p7
    anz_n Mcur_2 c x Ccur_2 S0 R0 learnt0 HCshapeX (proj1 HrangeXn)
    H_x_level H_tag_level H_x_in_S0) as (HresolveL & HresolveAdd & _).
  destruct (msat_analyze_e7_pending_split_p7
    anz_n anz_F Mcur_2 x cnt S0 R0 learnt0 H_analyze_inv H_x_in_S0 H_cnt_len)
    as (Hlenremove & Hperm_move).
  set (qv := lit_var_c (tag_lit c)).
  assert (Hqrange : 0 <= qv < anz_n).
  { unfold qv. split; [exact H_tag_lo | exact H_tag_hi]. }
  set (Mtag := analyze_tag_step_msolver Mcur_2
    (replace_Znth qv 1 (ms_tags Mcur_2))
    (ms_tagged Mcur_2 ++ (qv :: nil)) cap_prime
    activity_now orderpos_now heap_now var_inc_now).
  destruct (msat_analyze_e7_tag_state_p7
    anz_n anz_F anz_A_arr K _ Mcur_2 Mtag anz_focus qv cap_prime x
    activity_now orderpos_now heap_now S0 R0 learnt0 var_inc_now
    eq_refl H_cancel_ready Htags Hqrange H_tag_zero H_tagged_perm Hperm_move
    H_order_wf H_order_perm H_shape H_size H_act_len H_pos_len H_core_equiv
    H_seed) as
    (Hqnotseen & HtagsNew & HpermNew & HreadyTag & HshapeTag & HsizeTag &
     HcoreMTag & HcoreCurTag & HseedTag & HcoreTag & HviewTag &
     HrootTag & HqtailTag).
  assert (HresolveS :
    resolve_S (msolver_view anz_n Mcur_2) x Ccur_2 S0 R0 learnt0 =
    zremove x S0 ++ (qv :: nil)).
  { exact (HresolveAdd Hqnotseen). }
  rewrite HresolveS, HresolveL in HinvNew.
  assert (Hlennew :
    cnt + 1 = Zlength (zremove x S0 ++ (qv :: nil))).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  pose proof (msat_analyze_e7_side_rank_p7
    anz_n Mcur_2 c x ind Ccur_2 HCshapeX HvalidA Hrank_sel
    (proj1 Hind) Hqneq) as Hqrank.
  assert (HpendingRanks :
    forall y, In y (zremove x S0 ++ (qv :: nil)) -> exists r,
      assignment_rank (msolver_view anz_n Mcur_2) y = Some r /\
      Z.of_nat r <= ind).
  {
    intros y Hy. rewrite in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    - apply In_zremove_iff in Hy. destruct Hy as (HyS & Hyx).
      exact (HpendS y HyS Hyx).
    - cbn in Hy. destruct Hy as [Hy | []]. subst y. exact Hqrank.
  }
  assert (HexPending : exists y, In y (zremove x S0 ++ (qv :: nil))).
  { exists qv. apply in_or_app. right. left. reflexivity. }
  assert (Htagged :
    analyze_tagged_step anz_n anz_F anz_A_arr K Mcur_2 Mtag anz_focus
      c (tag_lit c) Ccur_2 S0 R0 learnt0 x
      (zremove x S0 ++ (qv :: nil)) (x :: R0) learnt0 words_2 (cnt + 1)).
  {
    unfold analyze_tagged_step.
    rewrite HrootTag, HcoreTag.
    refine (conj HreadyTag (conj HcoreCurTag (conj Hroot (conj H_reason_target
      (conj H_is_tag (conj eq_refl (conj H_x_in_S0 (conj Horder0
      (conj H_analyze_inv (conj HvalidA (conj HentA (conj HCndA
      (conj H_tag_level (_)))))))))))))).
    refine (conj (eq_sym HresolveS) (conj eq_refl (conj (eq_sym HresolveL)
      (conj Hlennew (conj Hwords (conj H_learnt_eq (conj HtagsNew
      (HpermNew)))))))).
  }
  assert (Hback :
    analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mtag anz_focus
      words_2 (cnt + 1) ind (zremove x S0 ++ (qv :: nil))
      (x :: R0) learnt0).
  {
    unfold analyze_backward_scan_inv.
    rewrite HviewTag, HqtailTag, HrootTag, HcoreTag.
    refine (conj HreadyTag (conj HinvNew (conj Hlennew (conj _ (conj Hind
      (conj Hwords (conj Hroot (conj H_learnt_eq (conj HtagsNew (conj HpermNew
      (conj HpendingRanks (conj HresolvedRanks (_))))))))))))); [lia |].
    destruct HexPending as (y & Hy).
    destruct (HpendingRanks y Hy) as (r & Hr & Hri).
    exists y, r. repeat split; assumption.
  }
  pose proof (msat_analyze_e7_scan_index_nonzero_p7
    anz_n Mcur_2 Mtag ind (zremove x S0 ++ (qv :: nil)) (x :: R0) learnt0
    HcoreTag HtagsNew HpermNew HexPending HpendingRanks (proj1 Hind))
    as Hzero.
  assert (Htagged_target :
    analyze_tagged_step anz_n anz_F anz_A_arr K Mcur_2 Mtag anz_focus
      (Znth x (ms_reason_words Mcur_2) 0)
      (tag_lit (Znth x (ms_reason_words Mcur_2) 0)) Ccur_2
      S0 R0 (lits_denote (tl words_2)) x
      (zremove x S0 ++ qv :: nil) (x :: R0) learnt0
      words_2 (cnt + 1)).
  { rewrite <- H_reason_word, H_learnt_eq. exact Htagged. }
  rename Hback into Hback_target.
  assert (Hbounds_target :
    0 <= lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mtag)) 0) < anz_n).
  { rewrite Z.sub_0_r, HcoreTag. exact Hindvarrange. }
  destruct Hbounds_target as (Hlower_target & Hupper_target).
  assert (Hzero_target :
    Znth
      (lit_var_c (Znth (ind - 0) (mt_trail (ms_core Mtag)) 0) - 0)
      (ms_tags Mtag) 0 = 0 -> 0 < ind).
  { rewrite !Z.sub_0_r. exact Hzero. }
  Exists words_cap_2 (zremove x S0 ++ qv :: nil) (x :: R0) learnt0
    words_2 (replace_Znth qv 1 (ms_tags Mcur_2))
    (ms_tagged Mcur_2 ++ qv :: nil) cap_prime
    activity_now orderpos_now heap_now var_inc_now.
  fold Mtag.
  bind_fact (retval_8 = lit_var_c (tag_lit c)) as Hpush.
  bind_fact (tags_now = replace_Znth (lit_var_c (tag_lit c)) 1 (ms_tags Mcur_2)) as Htagsnow.
  assert (HtagLen : 0 <= Zlength (ms_tagged Mcur_2 ++ qv :: nil) <= cap_prime).
  { unfold qv. rewrite <- Hpush. split; [apply Zlength_nonneg|]. assumption. }
  assert (HtagCap : 0 < cap_prime <= INT_MAX) by lia.
  rewrite Hpush, Htagsnow. fold qv.
  sep_apply (CharArray.full_to_seg tags_loop anz_n (replace_Znth qv 1 (ms_tags Mcur_2))).
  sep_apply (ms_solver_tagged_cells_to_rep_at s_pre p_prime
    (ms_tagged Mcur_2 ++ qv :: nil) cap_prime HtagLen HtagCap).
  sep_apply veci_rep_at_rep.
  assert (Hframe : solver_analyze_frame s_pre Mtag anz_wl = solver_analyze_frame s_pre Mcur_2 anz_wl)
    by reflexivity.
  assert (Hinert : solver_analyze_inert_at s_pre Mtag anz_n activity_ptr_loop orderpos_ptr_loop
    reasons_loop levels_ptr trail_loop tags_loop =
    solver_analyze_inert_at s_pre Mcur_2 anz_n activity_ptr_loop orderpos_ptr_loop
    reasons_loop levels_ptr trail_loop tags_loop) by reflexivity.
  rewrite Hframe, Hinert.
  unfold Mtag, analyze_tag_step_msolver, msolver_analysis_update.
  cbn [ms_qtail ms_cap ms_activity ms_orderpos ms_reason_words ms_core
    ms_tags ms_lim_cap ms_order ms_order_cap ms_stack ms_stack_cap
    ms_tagged ms_tagged_cap ms_var_inc ms_cla_inc ms_learnt
    ms_learnt_cap ms_prob ms_binary ms_binary_lits ms_stats].
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_7_2 : solver_analyze_entail_wit_7_2.
Proof.
  unfold solver_analyze_entail_wit_7_2, solver_analyze_open_at.
  Unfold.
  right. intros.
  bind_fact ( Znth retval_5 (ms_tags Mcur) 0 <> 0 ) as H_Znth.
  bind_fact ( retval_5 = lit_var_c (tag_lit c) ) as H_retval_5.
  msat_analyze_e7_semantic_facts_p7 anz_n anz_F anz_A_arr K Mcur
    anz_focus c x Ccur phase_2 words_2 cnt ind p S0 R0 learnt0.
  bind_fact ( 0 < cnt ) as H_cnt_2.
  pose proof H_loop_inv as Hloop.
  rewrite H_phase in Hloop.
  destruct (msat_analyze_e7_ready_semantics_p7
    anz_n anz_F anz_A_arr K Mcur anz_focus H_cancel_ready)
    as (Htrailwf & Hstable & Htrailimpl & Hrootunit).
  destruct (msat_analyze_e7_select_bridge_p7
    anz_n anz_F anz_A_arr K Mcur anz_focus c ind cnt p x Ccur
    words_2 S0 R0 learnt0 Hloop H_reason_target H_is_tag H_x_in_S0 H_cnt_len
    H_analyze_inv H_tagged_perm H_shape Htrailwf Hstable
    Hrootunit) as
    (HCshapeX & Horder0 & Hrank_sel & HvalidA & HentA & HCndA & HinvNew &
     HpendS & HresolvedRanks & Htags & Hind & Hwords & Hroot &
     Hindvarrange & HrangeXn & Hqneq).
  destruct (msat_analyze_e7_resolve_sets_p7
    anz_n Mcur c x Ccur S0 R0 learnt0 HCshapeX (proj1 HrangeXn)
    H_x_level H_tag_level H_x_in_S0) as (HresolveL & _ & HresolveKeep).
  destruct (msat_analyze_e7_pending_split_p7
    anz_n anz_F Mcur x cnt S0 R0 learnt0 H_analyze_inv H_x_in_S0 H_cnt_len)
    as (Hlenremove & Hperm_move).
  pose proof (msat_analyze_e7_tag_already_seen_p7
    anz_n Mcur c retval_5 S0 R0 learnt0 Htags H_tagged_perm
    H_retval_5 H_tag_lo H_tag_hi H_Znth) as Hqseen.
  assert (HresolveS :
    resolve_S (msolver_view anz_n Mcur) x Ccur S0 R0 learnt0 =
    zremove x S0).
  { exact (HresolveKeep Hqseen). }
  rewrite HresolveS, HresolveL in HinvNew.
  assert (HpermNew :
    Permutation (ms_tagged Mcur)
      (analyze_tags (zremove x S0) (x :: R0) learnt0)).
  { eapply Permutation_trans; [exact H_tagged_perm | exact Hperm_move]. }
  assert (HcoreSelf : analysis_core_equiv Mcur Mcur).
  { unfold analysis_core_equiv. repeat split; reflexivity. }
  assert (Htagged_target :
    analyze_tagged_step (ms_size Mcur) anz_F anz_A_arr K Mcur Mcur
      anz_focus (Znth x (ms_reason_words Mcur) 0)
      (tag_lit (Znth x (ms_reason_words Mcur) 0)) Ccur
      S0 R0 (lits_denote (tl words_2)) x
      (zremove x S0) (x :: R0) learnt0 words_2 cnt).
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
      anz_focus words_2 cnt ind (zremove x S0) (x :: R0) learnt0).
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
  pose proof (msat_analyze_e7_scan_index_nonzero_p7
    anz_n Mcur Mcur ind (zremove x S0) (x :: R0) learnt0
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
  Exists words_cap_2 (zremove x S0) (x :: R0) learnt0 words_2
    (ms_tags Mcur) (ms_tagged Mcur) (ms_tagged_cap Mcur)
    (ms_activity Mcur) (ms_orderpos Mcur) (ms_order Mcur) (ms_var_inc Mcur).
  rewrite analyze_tag_step_msolver_id.
  rewrite H_size in Htagged_target, Hback_target, Hupper_target.
  sep_apply (CharArray.full_to_seg tags_loop anz_n (ms_tags Mcur)).
  entailer_with ltac:(lia).
  rewrite H_learnt_eq in Htagged_target.
  rewrite H_reason_word.
  exact Htagged_target.
Qed.

Lemma proof_of_solver_analyze_entail_wit_7_3 : solver_analyze_entail_wit_7_3.
Proof.
  unfold solver_analyze_entail_wit_7_3, solver_analyze_open_at.
  Unfold.
  right. intros.
  bind_fact ( Znth (retval_6 - 0) (mt_levels (ms_core Mcur)) 0 <= 0 ) as H_Znth.
  bind_fact ( retval_6 = lit_var_c (tag_lit c) ) as H_retval_6.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mcur anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( level_of (msolver_view anz_n Mcur) (lit_var_c (tag_lit c)) = Some (current_level (msolver_view anz_n
      Mcur)) ) as H_level_of.
  bind_fact ( solver_shape Mcur ) as H_solver_shape.
  pose proof H_analysis_cancel_ready as Hready_copy.
  unfold analysis_cancel_ready in Hready_copy.
  destruct Hready_copy as
    (Mentry & Hcancel & Hequiv & Hheapwf & Hcovers & Hearliest &
     Hfocuslev & Hclainc).
  unfold propagation_cancel_ready in Hcancel.
  destruct Hcancel as
    (Hweak & Hprop & Hfocuswf & Hprocessed & Hentryfocus & Hfrontier &
     Hentryheap & Hentrycovers & Hentryearliest).
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as (Hcaproot & Hweak).
  assert (Htrailwf_entry : mtrail_wf anz_n (ms_core Mentry)).
  {
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_trail_wf Hweak).
    - exact (msa_trail_wf Hweak).
  }
  pose proof Hequiv as Hequiv_fields.
  unfold analysis_core_equiv in Hequiv_fields.
  destruct Hequiv_fields as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason & Eprob &
     Elearnt & Erest).
  assert (Htrailwf : mtrail_wf anz_n (ms_core Mcur)).
  { rewrite Ecore. exact Htrailwf_entry. }
  assert (Hcell :
    Znth (lit_var_c (tag_lit c)) (mt_levels (ms_core Mcur)) 0 =
    Zlength (mt_lim (ms_core Mcur))).
  {
    change
      (option_map
         (fun k => level_of_index (ms_core Mcur) (Z.of_nat k))
         (trail_pos (ms_core Mcur) (lit_var_c (tag_lit c))) =
       Some (Zlength (mt_lim (ms_core Mcur)))) in H_level_of.
    destruct (trail_pos (ms_core Mcur) (lit_var_c (tag_lit c)))
      as [k|] eqn:Hpos; cbn in H_level_of; try discriminate.
    assert (Hlevel :
      level_of_index (ms_core Mcur) (Z.of_nat k) =
      Zlength (mt_lim (ms_core Mcur))) by congruence.
    pose proof (trail_pos_bound
      (ms_core Mcur) (lit_var_c (tag_lit c)) k Hpos) as Hbound.
    pose proof (mtw_levels_agree Htrailwf (Z.of_nat k)) as Hagree.
    rewrite (trail_pos_var
      (ms_core Mcur) (lit_var_c (tag_lit c)) k Hpos) in Hagree.
    rewrite Hlevel in Hagree.
    apply Hagree. lia.
  }
  assert (Hroot_nonneg : 0 <= ms_root_level Mcur).
  { unfold solver_shape in H_solver_shape. tauto. }
  rewrite H_retval_6 in H_Znth.
  replace (lit_var_c (tag_lit c) - 0) with (lit_var_c (tag_lit c))
    in H_Znth by lia.
  lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_8_learnt : solver_analyze_entail_wit_8_learnt.
Proof.
  unfold solver_analyze_entail_wit_8_learnt, solver_analyze_open_at.
  Unfold.
  left.
  intros learnt_pre s_pre anz_wl levels_ptr focus M0 K A_arr F n Mcur phase Ccur words
    words_cap c p ind cnt tags_loop trail_loop reasons_loop Mcur_2 phase_2 Ccur_2
    words_2 words_cap_2 activity_ptr_loop orderpos_ptr_loop retval is_learnt_now
    clause_words retval_2 cla_inc1; intros.
  bind_fact ( msat_fp32_nonnegative cla_inc1 ) as H_msat_fp32_nonnegative.
  bind_fact ( analyze_resolution_loop_inv n F A_arr K Mcur_2 focus phase_2 c Ccur_2 words_2 cnt ind p ) as
      H_analyze_resolution_loop_inv.
  bind_fact ( msolver_seed_shadow Mcur_2 ) as H_msolver_seed_shadow.
  set (Mact := msolver_with_cla_inc_stats Mcur_2 cla_inc1 (ms_stats Mcur_2)).
  assert (Hcore : analysis_core_equiv Mcur_2 Mact).
  { subst Mact. unfold analysis_core_equiv, msolver_with_cla_inc_stats.
    cbn. repeat split; reflexivity. }
  assert (Hcore0 : analysis_core_equiv M0 Mact).
  { subst Mact. unfold analysis_core_equiv, msolver_with_cla_inc_stats in *.
    cbn in *. tauto. }
  assert (Hseed : msolver_seed_shadow Mact).
  { subst Mact. unfold msolver_with_cla_inc_stats. cbn. exact H_msolver_seed_shadow. }
  assert (Hframe_act :
    solver_analyze_frame s_pre Mact anz_wl = solver_analyze_frame s_pre Mcur_2 anz_wl).
  { subst Mact.
    unfold solver_analyze_frame, solver_analyze_frame_cells, msolver_with_cla_inc_stats.
    cbn. reflexivity. }
  (* The clause-activity witness keeps [ms_stats] (it is built with
     [stats := ms_stats Mcur_2]), so it leaves every projection the inert
     bundle reads unchanged -- [solver_analyze_inert_at_cla_inc] in lib.v. *)
  assert (Hinert_act :
    solver_analyze_inert_at s_pre Mact n activity_ptr_loop orderpos_ptr_loop
      reasons_loop levels_ptr trail_loop tags_loop
    = solver_analyze_inert_at s_pre Mcur_2 n activity_ptr_loop orderpos_ptr_loop
      reasons_loop levels_ptr trail_loop tags_loop).
  { subst Mact. apply solver_analyze_inert_at_cla_inc. }
  assert (Hloop :
    analyze_resolution_loop_inv n F A_arr K Mact focus phase_2 c Ccur_2
      words_2 cnt ind p).
  { pose proof H_analyze_resolution_loop_inv as Hloop0.
    unfold analyze_resolution_loop_inv in Hloop0.
    destruct Hloop0 as
      (Hready & Hind & Hwords & Hroot & Htags & Hphase).
    assert (Hready_act : analysis_cancel_ready n F A_arr K Mact focus).
    { destruct Hready as
        (Mentry & Hcancel & Hequiv & Hheap & Hcovers & Hreason & Hfocus & Hcla).
      exists Mentry.
      split. { exact Hcancel. }
      split.
      - subst Mact.
        cbn [msolver_with_cla_inc_stats]. exact Hequiv.
      - split.
        + subst Mact. cbn. exact Hheap.
        + split.
          * subst Mact. cbn. exact Hcovers.
          * split.
            -- subst Mact. cbn. exact Hreason.
            -- split.
               ++ subst Mact. cbn. exact Hfocus.
               ++ subst Mact. cbn. exact H_msat_fp32_nonnegative. }
    unfold analyze_resolution_loop_inv.
    split. { exact Hready_act. }
    split. { subst Mact. cbn. exact Hind. }
    split. { subst Mact. cbn. exact Hwords. }
    split. { subst Mact. cbn. exact Hroot. }
    split. { subst Mact. cbn. exact Htags. }
    subst Mact. cbn. exact Hphase. }
  Exists Mact.
  entailer_with ltac:(lia).
  rewrite Hframe_act, Hinert_act.
  subst Mact.
  unfold msolver_with_cla_inc_stats.
  cbn [ms_qtail ms_cap ms_activity ms_orderpos ms_reason_words ms_core
    ms_tags ms_lim_cap ms_order ms_order_cap ms_stack ms_stack_cap
    ms_tagged ms_tagged_cap ms_var_inc ms_cla_inc ms_learnt
    ms_learnt_cap ms_prob ms_binary ms_binary_lits ms_stats].
  set_String_name.
  sepcon_assoc_change.
  sepcon_cancel.
Qed.

Lemma proof_of_solver_analyze_entail_wit_9 : solver_analyze_entail_wit_9.
Proof.
  unfold solver_analyze_entail_wit_9, solver_analyze_open_at.
  Unfold.
  left. intros.
  Exists Mcur.
  entailer_with ltac:(lia).
  unfold analysis_core_equiv.
  repeat split; reflexivity.
Qed.

Lemma proof_of_solver_analyze_entail_wit_10_1_learnt : solver_analyze_entail_wit_10_1_learnt.
Proof.
  unfold solver_analyze_entail_wit_10_1_learnt, solver_analyze_open_at.
  Unfold; right; intros.
  msat_analyze_scan_entry_p7 Mact phase Ccur clause_words2 is_learnt2.
Qed.

Lemma proof_of_solver_analyze_entail_wit_10_2_learnt : solver_analyze_entail_wit_10_2_learnt.
Proof.
  unfold solver_analyze_entail_wit_10_2_learnt, solver_analyze_open_at.
  Unfold; intros.
  msat_analyze_resolve_p7 Mact phase Ccur clause_words2 is_learnt2 words_cap orderpos_ptr_clause activity_ptr_clause.
Qed.

Lemma proof_of_solver_analyze_entail_wit_11_1 : solver_analyze_entail_wit_11_1.
Proof.
  unfold solver_analyze_entail_wit_11_1, solver_analyze_open_at.
  Unfold; right; intros.
  msat_analyze_scan_entry_p7 Mact phase Ccur clause_words2 is_learnt2.
Qed.

Lemma proof_of_solver_analyze_entail_wit_11_2 : solver_analyze_entail_wit_11_2.
Proof.
  unfold solver_analyze_entail_wit_11_2, solver_analyze_open_at.
  Unfold; intros.
  msat_analyze_resolve_p7 Mact phase Ccur clause_words2 is_learnt2 words_cap orderpos_ptr_clause activity_ptr_clause.
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_1_learnt : solver_analyze_entail_wit_12_1_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_1_learnt, solver_analyze_open_at.
  Unfold.
  intros.
  bind_fact ( Znth (retval_10 - 0) (mt_levels (ms_core Mscan_2)) 0 = retval_11 ) as H_Znth.
  bind_fact ( retval_11 = Zlength (mt_lim (ms_core Mscan_2)) ) as H_retval_11.
  bind_fact ( retval_10 = lit_var_c (Znth (j - 0) clause_words2 0) ) as H_retval_10.
  bind_fact ( order_heap_wf anz_n heap1 orderpos1 ) as H_order_heap_wf.
  bind_fact ( Permutation (ms_order Mscan_2) heap1 ) as H_Permutation.
  bind_fact ( Zlength (ms_tagged Mscan_2 +:: retval_7) <= cap_prime ) as H_Zlength.
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
  destruct (msat_analyze_e12_scan_lit_current_p7 anz_n Mscan_2 Ccur
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
    by (exact (msat_analyze_e12_notin_initial_p7 (msolver_view anz_n Mact) Ccur
          j x_2 qv S0_2 R0_2 Sscan_2 Rscan_2 learnt0_2 learnt_scan_2
          Hqnotghost Hqneqx HSscan HRscan HLscan)).
  destruct (msat_analyze_e12_resolve_step_tag_p7 (msolver_view anz_n Mact) Ccur
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
    (ms_tagged Mscan_2 ++ (qv :: nil)) cap_prime
    activity1 orderpos1 heap1 var_inc1).
  assert (HreadyNext :
    analysis_cancel_ready anz_n anz_F anz_A_arr K Mnext anz_focus)
    by (unfold Mnext; apply msat_analyze_e12_tag_ready_perm_p7;
        [exact Hready | exact H_order_heap_wf | exact H_Permutation]).
  msat_analyze_tag_step_carry Mnext Mact M0 HcoreAct H_analysis_core_equiv
    H_msolver_seed_shadow.
  assert (HscanNext : analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact
      Mnext anz_focus phase Ccur (j + 1) ind S0_2 R0_2 learnt0_2 x_2
      (Sscan_2 ++ (qv :: nil)) Rscan_2 learnt_scan_2 words_scan_2 (cnt + 1))
    by (msat_analyze_scan_inv_tag Mnext phase H_Ccur HSnext HLnext).
  assert (Hret6 : retval_6 = qv)
    by (rewrite H_retval_6; replace (j - 0) with j by lia; reflexivity).
  assert (Hret7 : retval_7 = qv)
    by (rewrite H_retval_7; replace (j - 0) with j by lia; reflexivity).
  assert (HtagLen :
    0 <= Zlength (ms_tagged Mscan_2 ++ qv :: nil) <= cap_prime)
    by (split; [apply Zlength_nonneg | rewrite <- Hret7; exact H_Zlength]).
  assert (HtagCap : 0 < cap_prime <= INT_MAX) by lia.
  assert (HremainderNext :
    analysis_clause_remainder Mnext c is_learnt2 clause_words2 =
      analysis_clause_remainder Mscan_2 c is_learnt2 clause_words2)
    by reflexivity.
  assert (HframeNext :
    solver_analyze_frame s_pre Mnext anz_wl = solver_analyze_frame s_pre Mscan_2 anz_wl)
    by (unfold Mnext; apply solver_analyze_frame_analyze_tag_step).
  (* A tagging step changes none of the projections the inert bundle
     reads, so the bundle travels the step folded --
     [solver_analyze_inert_at_tag_step] in lib.v. *)
  assert (HinertNext :
    solver_analyze_inert_at s_pre Mnext anz_n activity_ptr_scan_2
      orderpos_ptr_scan_2 reasons levels_ptr trail tags
    = solver_analyze_inert_at s_pre Mscan_2 anz_n activity_ptr_scan_2
      orderpos_ptr_scan_2 reasons levels_ptr trail tags)
    by (unfold Mnext; apply solver_analyze_inert_at_tag_step).
  rewrite Hret6, Hret7.
  Left.
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 (Sscan_2 ++ qv :: nil)
    Rscan_2 learnt_scan_2 words_scan_2 Mnext.
  split_pure_spatial.
  - rewrite HremainderNext, HframeNext, HinertNext.
    unfold Mnext, analyze_tag_step_msolver, msolver_analysis_update.
    cbn [ms_qtail ms_cap ms_activity ms_orderpos ms_reason_words ms_core
      ms_tags ms_lim_cap ms_order ms_order_cap ms_stack ms_stack_cap
      ms_tagged ms_tagged_cap ms_var_inc ms_cla_inc ms_learnt
      ms_learnt_cap ms_prob ms_binary ms_binary_lits ms_stats].
    msat_cancel_sound.
    sep_apply CharArray.full_to_seg.
    sep_apply (ms_solver_tagged_cells_to_rep_at s_pre p_prime
      (ms_tagged Mscan_2 ++ qv :: nil) cap_prime HtagLen HtagCap).
    sep_apply veci_rep_at_rep.
    msat_cancel_sound; reflexivity.
  - msat_manual_entailer_with ltac:(first [assumption | lia | congruence]).
Qed.

Lemma proof_of_solver_analyze_entail_wit_18 : solver_analyze_entail_wit_18.
Proof.
  Unfold.
  right; intros.
  Exists words_cap_3 phase_3 Ccur_3 words_3 Mcur_3.
  msat_manual_entailer_with ltac:(assumption).
Qed.

(* ===== solver_analyze partial_solve wits ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_149_pure : solver_analyze_partial_solve_wit_149_pure.
Proof.
  pre_process_default.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  bind_fact ( ind < ms_qtail Mresolved ) as H_ind.
 split_pures.
  all: (dump_pre_spatial);
    (try lia).
  all: (destruct H_analyze_backward_scan_inv as [Hready _]);
    (destruct Hready as [Mbase [Hcancel [Hequiv _]]]);
    (destruct Hcancel as [Hweak _]);
    (unfold analysis_core_equiv in Hequiv);
    (destruct Hequiv as [_ [_ [Eqtail [Ecore _]]]]);
    (destruct Hweak as [_ Hinv]).
  all: destruct K as [A_inst | A_proc]; cbn in Hinv;
       [ pose proof (msw_trail_wf Hinv) as Hwf;
         pose proof (msw_size Hinv) as Hsize;
         pose proof (msw_shape Hinv) as Hshape
       | pose proof (msa_trail_wf Hinv) as Hwf;
         pose proof (msa_size Hinv) as Hsize;
         pose proof (msa_shape Hinv) as Hshape ].
  all: (assert (Hq : ind < ms_qtail Mbase)
         by (rewrite <- Eqtail; exact H_ind));
    (assert (Hi : 0 <= ((ind - 1) + 1) < Zlength (mt_trail (ms_core Mbase)))
         by (unfold solver_shape in Hshape; lia));
    (pose proof (Forall_Znth_elim _ _ _ 0 ((ind - 1) + 1)
         (mtw_trail_lits Hwf) Hi) as Hlit);
    (rewrite <- Ecore in Hlit);
    (replace ((ind - 1 + 1) - 0) with (ind - 1 + 1) by lia);
    (pose proof (lit_var_c_in_range anz_n _ Hlit) as Hrange);
    (lia).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_150_pure : solver_analyze_partial_solve_wit_150_pure.
Proof.
  pre_process_default.
  bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mresolved anz_focus words_resolved cnt ind Sresolved
      Rresolved learnt_resolved ) as H_analyze_backward_scan_inv.
  bind_fact ( ind < ms_qtail Mresolved ) as H_ind.
  assert (Hliteral_bounds :
    0 <= Znth (ind - 1 + 1) (mt_trail (ms_core Mresolved)) 0 <= INT_MAX).
  {
    destruct H_analyze_backward_scan_inv as [Hready _].
    destruct Hready as [Mbase [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak _]. destruct Hweak as [_ Hinv].
    unfold analysis_core_equiv in Hequiv.
    destruct Hequiv as [_ [_ [Eqtail [Ecore _]]]].
    destruct K as [A_inst | A_proc]; cbn in Hinv;
      [ pose proof (msw_trail_wf Hinv) as Hwf;
        pose proof (msw_size Hinv) as Hsize;
        pose proof (msw_shape Hinv) as Hshape
      | pose proof (msa_trail_wf Hinv) as Hwf;
        pose proof (msa_size Hinv) as Hsize;
        pose proof (msa_shape Hinv) as Hshape ];
      assert (Hq : ind < ms_qtail Mbase) by (rewrite <- Eqtail; exact H_ind);
      assert (Hi : 0 <= ind - 1 + 1 < Zlength (mt_trail (ms_core Mbase)))
        by (unfold solver_shape in Hshape; lia);
      pose proof (Forall_Znth_elim _ _ _ 0 (ind - 1 + 1)
        (mtw_trail_lits Hwf) Hi) as Hlit;
      rewrite <- Ecore in Hlit;
      unfold lit_wf_c in Hlit; unfold solver_shape in Hshape; lia.
  }
  split_pures; dump_pre_spatial;
    replace (ind - 1 + 1 - 0) with (ind - 1 + 1) by lia;
    lia.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_154_pure : solver_analyze_partial_solve_wit_154_pure.
Proof.
  pre_process_default.
  bind_fact ( analyze_resolution_exit anz_n anz_F anz_A_arr K Mresolution anz_focus p words_before ) as
      H_analyze_resolution_exit.
  assert (Hliteral_bounds : 0 <= p <= INT_MAX).
  {
    destruct H_analyze_resolution_exit as
      [Hready [_ [_ [x [R [learnt [r Hexist]]]]]]].
    destruct Hexist as [Hx [Hr [Htrail _]]].
    destruct Hready as [Mbase [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak _]. destruct Hweak as [_ Hinv].
    unfold analysis_core_equiv in Hequiv.
    destruct Hequiv as [_ [_ [Eqtail [Ecore _]]]].
    destruct K as [A_inst | A_proc]; cbn in Hinv;
      [ pose proof (msw_trail_wf Hinv) as Hwf;
        pose proof (msw_size Hinv) as Hsize;
        pose proof (msw_shape Hinv) as Hshape
      | pose proof (msa_trail_wf Hinv) as Hwf;
        pose proof (msa_size Hinv) as Hsize;
        pose proof (msa_shape Hinv) as Hshape ];
      unfold msolver_view, view_of in Hr;
      pose proof (trail_pos_bound _ _ _ Hr) as Hrng;
      rewrite Ecore in Hrng;
      assert (Hi : 0 <= Z.of_nat r < Zlength (mt_trail (ms_core Mbase))) by lia;
      pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
        (mtw_trail_lits Hwf) Hi) as Hlit;
      rewrite <- Ecore in Hlit; rewrite Htrail in Hlit;
      unfold lit_wf_c in Hlit; unfold solver_shape in Hshape; lia.
  }
  split_pures; dump_pre_spatial; lia.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_158_pure : solver_analyze_partial_solve_wit_158_pure.
Proof.
  pre_process_default.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mresolution anz_focus ) as H_analysis_cancel_ready.
 split_pures;
  dump_pre_spatial;
  try lia;
  (try (destruct H_analysis_cancel_ready as [Mbase [Hcancel [Hequiv _]]];
       destruct Hcancel as [Hweak _]; destruct Hweak as [_ Hinv];
       unfold analysis_core_equiv in Hequiv;
       destruct Hequiv as [HsizeEq _];
       destruct K as [A_inst | A_proc]; cbn in Hinv;
       [ pose proof (msw_size Hinv) as Hsize
       | pose proof (msa_size Hinv) as Hsize ]; lia)).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_162_pure : solver_analyze_partial_solve_wit_162_pure.
Proof.
  Unfold; pre_process_default.
  msat_analyze_close_learnt_vec_lit_range Hf.
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_168_pure : solver_analyze_partial_solve_wit_168_pure.
Proof.
  Unfold; pre_process_default.
  msat_analyze_close_learnt_vec_lit_range Hf.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_171_pure : solver_analyze_partial_solve_wit_171_pure.
Proof. pre_process_default.
  bind_fact ( Znth (retval - 0) (ms_reason_words Mmin) 0 <> 0 ) as H_Znth.
  bind_fact ( retval = lit_var_c (Znth (i - 0) words_min 0) ) as H_retval.
  bind_fact ( analyze_clause_cert anz_n anz_F Mmin words_uip ) as H_cert.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin words_uip kept removed words_min T i j ) as H_inv.
  bind_fact ( incl (map lit_var_c words_min) (map lit_var_c (mt_trail (ms_core Mmin))) ) as H_incl.
  bind_fact ( incl (map lit_var_c words_min) (ms_tagged Mmin) ) as H_incl_2.
  bind_fact ( 0 <= i ) as H_i_low.
  bind_fact ( i < Zlength words_min ) as H_i_high.
  pose proof (msat_analyze_minimize_scan_assigned_p7 anz_n anz_F Mmin words_uip
    kept removed words_min T i j H_cert H_inv H_incl H_i_low H_i_high) as Hbelow.
  assert (Htrail : In (lit_var_c (Znth (i - 0) words_min 0))
    (map lit_var_c (mt_trail (ms_core Mmin)))).
  { apply H_incl. apply in_map. apply Znth_In. lia. }
  assert (Htagged : In (lit_var_c (Znth (i - 0) words_min 0)) (ms_tagged Mmin)).
  { apply H_incl_2. apply in_map. apply Znth_In. lia. }
  assert (Hreason : Znth (lit_var_c (Znth (i - 0) words_min 0))
    (ms_reason_words Mmin) 0 <> 0).
  { replace (retval - 0) with retval in H_Znth by lia.
    rewrite H_retval in H_Znth. exact H_Znth. }
  subst retval.
  (* every residual pure goal is one of the four facts above; entailer_with
     discharges each of them from the context. *)
  unfold veci_rep_at in *; split_pures; msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_analyze_partial_solve_wit_178_pure : solver_analyze_partial_solve_wit_178_pure.
Proof.
  pre_process_default.
  bind_fact ( analyze_minimize_loop_inv anz_n Mmin_done words_uip kept_done removed_done words_done T_done i j ) as
      H_analyze_minimize_loop_inv.
  unfold veci_rep_at in *; split_pures;
  (entailer_with lia);
  try lia;
  (unfold analyze_minimize_loop_inv in H_analyze_minimize_loop_inv; simpl in H_analyze_minimize_loop_inv;
       destruct H_analyze_minimize_loop_inv as [Hj Htmp];
       destruct Htmp as [Hji Htmp];
       destruct Htmp as [HiLen Htmp];
       destruct Htmp as [Hlen Htmp];
       lia).
Qed.

(* ===== solver_propagate entail wits (22 proofs) ===== *)
Lemma proof_of_solver_propagate_entail_wit_11_7_scan_same : solver_propagate_entail_wit_11_7_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_7_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_8_scan_same : solver_propagate_entail_wit_11_8_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_8_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_9_scan_same : solver_propagate_entail_wit_11_9_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_9_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_10_scan_same : solver_propagate_entail_wit_11_10_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_10_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_11_scan_same : solver_propagate_entail_wit_11_11_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_11_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_12_scan_same : solver_propagate_entail_wit_11_12_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_12_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_1_scan_move : solver_propagate_entail_wit_12_1_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_1_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_2_scan_move : solver_propagate_entail_wit_12_2_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_2_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_3_scan_move : solver_propagate_entail_wit_12_3_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_3_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_4_scan_move : solver_propagate_entail_wit_12_4_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_4_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_5_scan_move : solver_propagate_entail_wit_12_5_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_5_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_12_6_scan_move : solver_propagate_entail_wit_12_6_scan_move.
Proof.
  unfold solver_propagate_entail_wit_12_6_scan_move.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_31_1 : solver_propagate_entail_wit_31_1.
Proof.
  unfold solver_propagate_entail_wit_31_1.
  unfold stats_propagations, stats_inspects.
  aggressive_pre_process.
  Left.
  Exists trl_scan_2 rsn_scan_2 prop_count_2 simp_count_2
    scan_caps_pre_2 scan_wcap_2 scan_caps_post_2 scan_wm_pre_2 scan_wm_post_2
    logical_words_2 source_words_2 moved_2 garbage_2 watch_memory_2
    ii_2 jj_2 retained_2 rest_2 Mentry_2.
  Exists Mscan_2.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_entail_wit_31_2 : solver_propagate_entail_wit_31_2.
Proof.
  unfold solver_propagate_entail_wit_31_2.
  unfold stats_propagations, stats_inspects.
  aggressive_pre_process.
  Right.
  Exists trl_scan_2 rsn_scan_2 simp_count_2 prop_count_2
    scan_caps_pre_2 scan_wcap_2 scan_caps_post_2 scan_wm_pre_2 scan_wm_post_2
    logical_words_2 source_words_2 moved_2 garbage_2 watch_memory_2
    ii_2 jj_2 retained_2 rest_2 Mentry_2.
  Exists Mscan_2.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_entail_wit_31_3_binary_conflict : solver_propagate_entail_wit_31_3_binary_conflict.
Proof.
  unfold solver_propagate_entail_wit_31_3_binary_conflict.
  unfold stats_propagations, stats_inspects.
  aggressive_pre_process.
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next
    next_caps_pre next_wcap next_caps_post next_wm_pre next_wm_post
    logical_next source_words_next moved_next garbage_next memory_next
    ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.

Lemma proof_of_solver_propagate_entail_wit_31_5_unit_conflict : solver_propagate_entail_wit_31_5_unit_conflict.
Proof.
  unfold solver_propagate_entail_wit_31_5_unit_conflict.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_31_3_binary_conflict.
Qed.

Lemma proof_of_solver_propagate_entail_wit_31_6_unit_conflict : solver_propagate_entail_wit_31_6_unit_conflict.
Proof.
  unfold solver_propagate_entail_wit_31_6_unit_conflict.
  unfold stats_propagations, stats_inspects.
  aggressive_pre_process.
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Right.
  Exists trl_next rsn_next simp_count_next prop_count_next
    next_caps_pre next_wcap next_caps_post next_wm_pre next_wm_post
    logical_next source_words_next moved_next garbage_next memory_next
    ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.

Lemma proof_of_solver_propagate_entail_wit_31_4_binary_conflict : solver_propagate_entail_wit_31_4_binary_conflict.
Proof.
  unfold solver_propagate_entail_wit_31_4_binary_conflict.
  unfold stats_propagations, stats_inspects. exact proof_of_solver_propagate_entail_wit_31_6_unit_conflict.
Qed.

Lemma proof_of_solver_propagate_entail_wit_32_1 : solver_propagate_entail_wit_32_1.
Proof.
  unfold solver_propagate_entail_wit_32_1.
  unfold stats_propagations, stats_inspects.
  (* The shared scan-finish lemma uses the facts already present in this
     generated context; its conclusion determines the data arguments. *)
  Unfold; intros.
  subst retval_2; subst retval.
  lazymatch goal with
  | |- ?P |-- ?T =>
      lazymatch T with
      | ?L || ?R => transitivity (R || L)
      end
  end.
  - eapply propagation_scan_finish_step__shared_solver_propagate;
      first [eassumption | reflexivity].
  - apply derivable1_orp_elim.
    + apply derivable1_orp_intros2.
    + apply derivable1_orp_intros1.
Qed.

Lemma proof_of_solver_propagate_entail_wit_32_2 : solver_propagate_entail_wit_32_2.
Proof.
  unfold solver_propagate_entail_wit_32_2.
  unfold stats_propagations, stats_inspects.
  (* Same scan-finish note as in [proof_of_solver_propagate_entail_wit_32_1] above. *)
  Unfold; intros.
  subst retval_2; subst retval.
  lazymatch goal with
  | |- ?P |-- ?T =>
      lazymatch T with
      | ?L || ?R => transitivity (R || L)
      end
  end.
  - eapply propagation_scan_finish_step__shared_solver_propagate;
      first [eassumption | reflexivity].
  - apply derivable1_orp_elim.
    + apply derivable1_orp_intros2.
    + apply derivable1_orp_intros1.
Qed.

Lemma proof_of_solver_propagate_entail_wit_33_1 : solver_propagate_entail_wit_33_1.
Proof.
  unfold solver_propagate_entail_wit_33_1.
  unfold solver_propagate_open_at, stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_finish_frame_p7 lvl_finish levels_entry trl_finish rsn_finish Mfinish.
Qed.

Lemma proof_of_solver_propagate_entail_wit_33_2 : solver_propagate_entail_wit_33_2.
Proof.
  unfold solver_propagate_entail_wit_33_2.
  unfold solver_propagate_open_at, stats_propagations, stats_inspects.
  Unfold; left; intros.
  msat_propagate_finish_frame_p7 lvl_finish levels_entry trl_finish rsn_finish Mfinish.
Qed.

(* ===== solver_propagate partial_solve wits (12 proofs) ===== *)
Lemma proof_of_solver_propagate_partial_solve_wit_260_scan_same_pure :
  solver_propagate_partial_solve_wit_260_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_260_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; right; intros.
  msat_propagate_scan_assign_cell_p7 retval_3 Mscan.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_270_scan_move_pure :
  solver_propagate_partial_solve_wit_270_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_270_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  right; intros.
  msat_propagate_scan_assign_cell_p7 retval_3 Mscan.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_272_scan_move_pure :
  solver_propagate_partial_solve_wit_272_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_272_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  right; intros.
  msat_propagate_scan_assign_cell_p7 retval_3 Mscan.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_274_scan_same_pure :
  solver_propagate_partial_solve_wit_274_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_274_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; right; intros.
  msat_propagate_scan_assign_cell_p7 retval_3 Mscan.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_276_scan_same_pure :
  solver_propagate_partial_solve_wit_276_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_276_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; right; intros.
  msat_propagate_scan_assign_cell_p7 retval_3 Mscan.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_277_scan_same_pure :
  solver_propagate_partial_solve_wit_277_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_277_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right; intros.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  msat_propagate_close_scan_assign_cell H_Znth retval_3.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_302_scan_same_pure :
  solver_propagate_partial_solve_wit_302_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_302_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  msat_propagate_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_303_scan_same_pure :
  solver_propagate_partial_solve_wit_303_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_303_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  msat_propagate_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_304_scan_same_pure :
  solver_propagate_partial_solve_wit_304_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_304_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  msat_propagate_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_305_scan_same_pure :
  solver_propagate_partial_solve_wit_305_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_305_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  msat_propagate_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_306_scan_move_pure :
  solver_propagate_partial_solve_wit_306_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_306_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  msat_propagate_close_clause_hdr_word_nonneg.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_307_scan_move_pure :
  solver_propagate_partial_solve_wit_307_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_307_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  msat_propagate_close_clause_hdr_word_nonneg.
Qed.

(* ===== solver_propagate return wits (3 proofs) ===== *)
Lemma proof_of_solver_propagate_return_wit_1 : solver_propagate_return_wit_1.
Proof.
  unfold solver_propagate_return_wit_1.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
  fold (stats_propagations (ms_stats M1)) (stats_inspects (ms_stats M1)).
  bind_fact ( solver_shape M1 ) as H_solver_shape.
  bind_fact ( solver_propagation_loop_inv n F A_arr K M0 M1 cf ) as H_solver_propagation_loop_inv.
  bind_fact ( minisat_propagation_reuse_loop n M0 M1 cf ) as Hreuse.
  destruct Hreuse as [Hcompleted [Hresident Hconflict_resident]].
  unfold solver_propagation_loop_inv in H_solver_propagation_loop_inv.
  destruct H_solver_propagation_loop_inv as [Hframe [Hlive | Hconflict]].
  - destruct Hlive as [Hzero Hinv].
    assert (Hdrained : mt_qhead (ms_core M1) = ms_qtail M1) by lia.
    assert (Hreuse_live : minisat_propagation_reuse_live M0 M1).
    { split.
      - intro Hentry. exact (proj1 (Hcompleted Hentry) Hzero).
      - exact Hresident. }
    transitivity (solver_rep_assigns_levels_at s_pre M1 assigns_entry levels_entry wlists_entry **
      ((conflict_out_pre) # Ptr |-> cf)).
    { rewrite <- (solver_propagation_open_refold__propagate
        s_pre M1 assigns_entry rsn levels_entry trl wlists_entry H_solver_shape).
      set_String_name; sepcon_assoc_change; sepcon_cancel; subst_all_strings. }
    rewrite Hzero.
    unfold solver_propagate_post.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    entailer_with ltac:(lia). Exists M1. entailer_with ltac:(lia).
  - destruct Hconflict as [Hnonzero _]. contradiction.
Qed.

Lemma proof_of_solver_propagate_return_wit_2 : solver_propagate_return_wit_2.
Proof.
  unfold solver_propagate_return_wit_2.
  unfold solver_propagate_open_at, stats_propagations, stats_inspects.
  Unfold.
  right. intros.
  fold (stats_propagations (ms_stats M1)) (stats_inspects (ms_stats M1)).
  bind_fact ( solver_shape M1 ) as H_solver_shape.
  bind_fact ( solver_propagation_loop_inv n F A_arr K M0 M1 cf ) as H_solver_propagation_loop_inv.
  bind_fact ( minisat_propagation_reuse_loop n M0 M1 cf ) as Hreuse.
  destruct Hreuse as [Hcompleted [Hresident Hconflict_resident]].
  unfold solver_propagation_loop_inv in H_solver_propagation_loop_inv.
  destruct H_solver_propagation_loop_inv as [Hframe [Hzero | Hconflict]].
  - destruct Hzero as [Hzero _]. contradiction.
  - destruct Hconflict as
      [Hnonzero [focus [C [Hready [Hcert Hdenotes]]]]].
    assert (Hreuse_conflict : minisat_base_watch_completed M0 ->
      minisat_watch_conflict_ready n M1).
    { intro Hentry. exact (proj2 (Hcompleted Hentry) Hnonzero). }
    pose proof (Hconflict_resident Hnonzero) as Hresident_now.
    transitivity (solver_rep_assigns_levels_at s_pre M1 assigns_entry levels_entry wlists_entry **
      ((conflict_out_pre) # Ptr |-> cf)).
    { rewrite <- (solver_propagation_open_refold__propagate
        s_pre M1 assigns_entry rsn levels_entry trl wlists_entry H_solver_shape).
      set_String_name; sepcon_assoc_change; sepcon_cancel; subst_all_strings. }
    unfold solver_propagate_post.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros2.
    entailer_with ltac:(lia). Exists M1 cf focus C. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_return_wit_3_capacity_copy : solver_propagate_return_wit_3_capacity_copy.
Proof.
  Unfold.
  right. intros. unfold solver_propagate_post.
  rewrite <- derivable1_orp_intros2. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_propagate which_implies wits (11 proofs) ===== *)
Lemma proof_of_solver_propagate_which_implies_wit_19 : solver_propagate_which_implies_wit_19.
Proof.
  Unfold.
  intros.
  bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i.
  bind_fact ( j = begin + copy_dst * sizeof ( PTR ) ) as H_j.
  destruct (Z.eq_dec copy_dst copy_src) as [Heq | Hneq].
  - subst copy_dst.
    Left; intros.
    unfold StorePtrAsElement.storeA.
    (* `sizeof_ptr` yields the unfolded Arch alias; PtrArray's lemmas and `cancel`
              want the derived `ptr_size_Z`, and both match syntactically. *)
    change (sizeof (PTR)) with ptr_size_Z. fold_arch.
    sep_apply_l_atomic (PtrArray.full_split_to_missing_i begin copy_src
      (Zlength source_words) copy_memory 0).
    + dump_pre_spatial. lia.
    + entailer_with ltac:(lia).
      rewrite H_i.
      change (sizeof (PTR)) with ptr_size_Z. fold_arch.
      cancel.
  - assert (Hlt : copy_dst < copy_src) by lia.
    Right; intros.
    prop_apply_p (PtrArray.full_Zlength begin (Zlength source_words)
      copy_memory).
    Intros_p Hlen.
    sep_apply_l_atomic (PtrArray.full_split_to_seg begin copy_dst
      (Zlength source_words) copy_memory).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (PtrArray.seg_split_to_seg begin copy_dst
        (copy_dst + 1) (Zlength source_words)
        (sublist copy_dst (Zlength source_words) copy_memory)).
      * dump_pre_spatial. lia.
      * rewrite !Zsublist_Zsublist by lia.
        replace (0 + copy_dst) with copy_dst by lia.
        replace (copy_dst + 1 - copy_dst + copy_dst)
          with (copy_dst + 1) by lia.
        replace (Zlength source_words - copy_dst + copy_dst)
          with (Zlength source_words) by lia.
        sep_apply_l_atomic (PtrArray.seg_split_to_seg begin
          (copy_dst + 1) copy_src (Zlength source_words)
          (sublist (copy_dst + 1) (Zlength source_words) copy_memory)).
        -- dump_pre_spatial. lia.
        -- rewrite !Zsublist_Zsublist by lia.
           replace (0 + (copy_dst + 1)) with (copy_dst + 1) by lia.
           replace (copy_src - (copy_dst + 1) + (copy_dst + 1))
             with copy_src by lia.
           replace (Zlength source_words - (copy_dst + 1) +
             (copy_dst + 1)) with (Zlength source_words) by lia.
           sep_apply_l_atomic (PtrArray.seg_split_to_seg begin copy_src
             (copy_src + 1) (Zlength source_words)
             (sublist copy_src (Zlength source_words) copy_memory)).
           ++ dump_pre_spatial. lia.
           ++ rewrite !Zsublist_Zsublist by lia.
              replace (0 + copy_src) with copy_src by lia.
              replace (copy_src + 1 - copy_src + copy_src)
                with (copy_src + 1) by lia.
              replace (Zlength source_words - copy_src + copy_src)
                with (Zlength source_words) by lia.
              rewrite (sublist_single 0 copy_src copy_memory) by lia.
              rewrite (sublist_single 0 copy_dst copy_memory) by lia.
              unfold PtrArray.seg at 1 4.
              simpl.
              entailer_with ltac:(lia).
              rewrite H_i, H_j.
              change (sizeof (PTR)) with ptr_size_Z. fold_arch.
              cancel.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_51 : solver_propagate_which_implies_wit_51.
Proof.
 exact proof_of_solver_propagate_which_implies_wit_19.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_64 : solver_propagate_which_implies_wit_64.
Proof.
  unfold solver_propagate_which_implies_wit_64.
  unfold stats_propagations, stats_inspects.
  Unfold.
  left; intros.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_entry.
  bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) (Zlength (propagation_normalized_clause watch0 false_lit clause_contents)) ) as
      H_propagation_replacement_scan_inv.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  bind_fact ( clause_lits_pointer scan_current lits ) as H_clause_lits_pointer.
  bind_fact ( real_watch_pair (Zlength scan_wm_pre) clause_contents ) as H_real_watch_pair.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  bind_fact ( watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  unfold clause_db_pair_frame, enqueue_post_at, enqueue_state_at.
  Intros is_learnt qtail' assigns' levels' reasons' trail' rsn trl.
  unfold enqueue_transition in H; cbn in H.
  destruct H as [Hsame | Hrest].
  - destruct Hsame as [_ [Hret _]]. lia.
  - destruct Hrest as [Hconflict | Hfresh].
    2: { destruct Hfresh as [_ [Hret _]]; lia. }
    destruct Hconflict as
      [Hassigned [Hnotsig [Hret
        [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]]].
    subst conflict_ret assigns' levels' reasons' trail' qtail'.
    pose proof H_solver_propagation_scan_semantics as H_scan_arms.
    destruct H_scan_arms as [Hlive | Hdead].
    2: { destruct Hdead as [Hzero _]; lia. }
    destruct Hlive as
      [_ [Hweak [Hprop [Hheapready [Hheapcovers [Hreasonless
        [Hlevel [Hp [Hprocessed [Hfrontier Hscan]]]]]]]]]].
    unfold clause_db_pair_remainder at 1. Split.
    + Intros co pre post. coq_prop_lift.
      destruct H as [Hprob [Hlits Hlearnt]].
      assert (Hdbwf : db_wf n (msolver_db Mscan)).
      { msat_propagate_project_weak_field Hweak K (@msw_db_wf)
          (@msa_db_wf). }
      assert (Hin : In (scan_current, co) (msolver_db Mscan)).
      { unfold msolver_db. apply in_or_app. left.
        rewrite Hprob. apply in_or_app. right. simpl. auto. }
      destruct (msat_propagate_wit66_scan_shape_p7 n F A_arr K Mscan co
          scan_current p (Zlength scan_wm_pre) watch0 false_lit
          clause_contents Hweak Hdbwf Hin Hlits Hassigned Hnotsig
          H_propagation_replacement_scan_inv H_false_lit H_real_watch_pair
          H_Zlength H_watch0)
        as [a0 [a1 [tail [Hcontents [Hlen [Hall [Hnodup [Hnew_eq [Htail
           [Hperm [Hwatchcases [Hnew_false [Hno_reason_ptr
           Hentry_perm]]]]]]]]]]]]].
      rewrite Hcontents in Hlits. subst clause_contents.
      set (new_lits := watch0 :: false_lit :: tail).
      set (co_new := clause_obj_with_lits co new_lits).
      set (prob_route := pre ++ (scan_current, co_new) :: post).
      set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
        (ms_learnt Mscan) (ms_wm Mscan) (ms_wcaps Mscan)).
      pose proof (msat_propagate_wit66_prob_ready_p7 n F A_arr K Mscan co pre
        post scan_current p watch0 false_lit a0 a1 tail retained rest
        H_solver_propagation_scan_semantics
        Hdbwf Hin Hlits Hprob Hlen Hall Hnodup Hperm Hnew_false H_false_lit
        Hno_reason_ptr Hentry_perm Hwatchcases Hnew_eq) as Hready.
      pose proof (proj1 Hready) as Hupdate_normalized.
      assert (Hreuse_normalized : minisat_propagation_reuse_scan M0 Mroute p 0 rest).
      { unfold Mroute.
        eapply (minisat_propagation_reuse_normalize__api_reentry
          M0 Mscan p 0 rest scan_current a0 a1 tail watch0).
        - rewrite <- H_false_lit. exact Hupdate_normalized.
        - rewrite <- H_false_lit. exact Hwatchcases.
        - exact Hreuse_entry. }
      destruct (db_pair_lits_update_selected_owner__propagate_dbu
        _ _ _ _ _ _ _ Hupdate_normalized) as [selected [Hselected Hselected_words]].
      assert (Hselected_false : clause_false
        (assigns_pv (mt_assigns (ms_core Mroute))) (denote_obj selected)).
      { unfold denote_obj. rewrite Hselected_words, Hnew_eq.
        apply lits_denote_false_iff; [|exact Hnew_false].
        apply Forall_forall. intros word Hword.
        assert (Holdword : In word (a0 :: a1 :: tail)).
        { eapply Permutation_in; [exact Hperm|exact Hword]. }
        pose proof Hall as Hwords_wf. rewrite Forall_forall in Hwords_wf.
        specialize (Hwords_wf word Holdword). destruct Hwords_wf. lia. }
      assert (Hreuse_conflict : minisat_propagation_reuse_scan
        M0 Mroute p scan_current nil).
      { eapply minisat_propagation_reuse_resident_conflict__api_reentry;
          [exact Hreuse_normalized| |exact Hselected|exact Hselected_false].
        pose proof (db_wf_ptr_pos n (msolver_db Mscan) scan_current co Hdbwf Hin). lia. }
      Exists prob_route (ms_learnt Mscan) Mroute.
      split_pure_spatial.
      * unfold prob_route.
        rewrite (msat_propagate_wit66_db_rep_split_p7 pre post
          (scan_current, co_new)), clause_db_rep_cons.
        rewrite Htail.
        unfold MiniSatClause.rep, co_new, clause_obj_with_lits,
          new_lits; cbn [fst snd co_learnt co_lits].
        rewrite Hlearnt.
        rewrite !IntArray.seg_unfold.
        unfold clause_lits_pointer in H_clause_lits_pointer. subst lits.
        subst Mroute.
        unfold solver_propagation_nonwatch_rest_at.
        Exists rsn trl.
        rewrite (msat_propagate_wit66_binary_rep_p7 Mscan prob_route
          (ms_learnt Mscan) (ms_wm Mscan) (ms_wcaps Mscan)).
        rewrite (msat_propagate_wit66_frame_eq_p7 s Mscan prob_route
          (ms_learnt Mscan) (ms_wm Mscan) (ms_wcaps Mscan)
          (msat_propagate_wit66_keys_replace_p7 pre post scan_current co
            co_new _ Hprob) eq_refl).
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
        rewrite H_simp_count, H_prop_count.
        msat_propagate_wit66_route_close_p7 Mscan Hdbwf Hin.
      * split_pures; apply derivable1s_coq_prop_r; try exact Hready; try exact Hreuse_conflict;
          cbn [Mroute msolver_propagation_db_wmap_update
            msolver_propagation_overlay msolver_propagation_update ]; try assumption; try reflexivity.
    + Intros co pre post. coq_prop_lift.
      destruct H as [Hlearnt_split [Hlits Hlearnt]].
      assert (Hdbwf : db_wf n (msolver_db Mscan)).
      { msat_propagate_project_weak_field Hweak K (@msw_db_wf)
          (@msa_db_wf). }
      assert (Hin : In (scan_current, co) (msolver_db Mscan)).
      { unfold msolver_db. apply in_or_app. right.
        rewrite Hlearnt_split. apply in_or_app. right. simpl. auto. }
      destruct (msat_propagate_wit66_scan_shape_p7 n F A_arr K Mscan co
          scan_current p (Zlength scan_wm_pre) watch0 false_lit
          clause_contents Hweak Hdbwf Hin Hlits Hassigned Hnotsig
          H_propagation_replacement_scan_inv H_false_lit H_real_watch_pair
          H_Zlength H_watch0)
        as [a0 [a1 [tail [Hcontents [Hlen [Hall [Hnodup [Hnew_eq [Htail
           [Hperm [Hwatchcases [Hnew_false [Hno_reason_ptr
           Hentry_perm]]]]]]]]]]]]].
      rewrite Hcontents in Hlits. subst clause_contents.
      set (new_lits := watch0 :: false_lit :: tail).
      set (co_new := clause_obj_with_lits co new_lits).
      set (learnt_route := pre ++ (scan_current, co_new) :: post).
      set (Mroute := msolver_propagation_db_wmap_update Mscan (ms_prob Mscan)
        learnt_route (ms_wm Mscan) (ms_wcaps Mscan)).
      pose proof (msat_propagate_wit66_learnt_ready_p7 n F A_arr K Mscan co
        pre post scan_current p watch0 false_lit a0 a1 tail retained rest
        H_solver_propagation_scan_semantics
        Hdbwf Hin Hlits Hlearnt_split Hlen Hall Hnodup Hperm Hnew_false
        H_false_lit Hno_reason_ptr Hentry_perm Hwatchcases Hnew_eq) as Hready.
      pose proof (proj1 Hready) as Hupdate_normalized.
      assert (Hreuse_normalized : minisat_propagation_reuse_scan M0 Mroute p 0 rest).
      { unfold Mroute.
        eapply (minisat_propagation_reuse_normalize__api_reentry
          M0 Mscan p 0 rest scan_current a0 a1 tail watch0).
        - rewrite <- H_false_lit. exact Hupdate_normalized.
        - rewrite <- H_false_lit. exact Hwatchcases.
        - exact Hreuse_entry. }
      destruct (db_pair_lits_update_selected_owner__propagate_dbu
        _ _ _ _ _ _ _ Hupdate_normalized) as [selected [Hselected Hselected_words]].
      assert (Hselected_false : clause_false
        (assigns_pv (mt_assigns (ms_core Mroute))) (denote_obj selected)).
      { unfold denote_obj. rewrite Hselected_words, Hnew_eq.
        apply lits_denote_false_iff; [|exact Hnew_false].
        apply Forall_forall. intros word Hword.
        assert (Holdword : In word (a0 :: a1 :: tail)).
        { eapply Permutation_in; [exact Hperm|exact Hword]. }
        pose proof Hall as Hwords_wf. rewrite Forall_forall in Hwords_wf.
        specialize (Hwords_wf word Holdword). destruct Hwords_wf. lia. }
      assert (Hreuse_conflict : minisat_propagation_reuse_scan
        M0 Mroute p scan_current nil).
      { eapply minisat_propagation_reuse_resident_conflict__api_reentry;
          [exact Hreuse_normalized| |exact Hselected|exact Hselected_false].
        pose proof (db_wf_ptr_pos n (msolver_db Mscan) scan_current co Hdbwf Hin). lia. }
      Exists (ms_prob Mscan) learnt_route Mroute.
      split_pure_spatial.
      * unfold learnt_route.
        rewrite (msat_propagate_wit66_db_rep_split_p7 pre post
          (scan_current, co_new)), clause_db_rep_cons.
        rewrite Htail.
        unfold MiniSatClause.rep, co_new, clause_obj_with_lits,
          new_lits; cbn [fst snd co_learnt co_lits].
        rewrite Hlearnt.
        rewrite !IntArray.seg_unfold.
        unfold clause_lits_pointer in H_clause_lits_pointer. subst lits.
        subst Mroute.
        unfold solver_propagation_nonwatch_rest_at.
        Exists rsn trl.
        rewrite (msat_propagate_wit66_binary_rep_p7 Mscan (ms_prob Mscan)
          learnt_route (ms_wm Mscan) (ms_wcaps Mscan)).
        rewrite (msat_propagate_wit66_frame_eq_p7 s Mscan (ms_prob Mscan)
          learnt_route (ms_wm Mscan) (ms_wcaps Mscan) eq_refl
          (msat_propagate_wit66_keys_replace_p7 pre post scan_current co
            co_new _ Hlearnt_split)).
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
        rewrite H_simp_count, H_prop_count.
        msat_propagate_wit66_route_close_p7 Mscan Hdbwf Hin.
      * split_pures; apply derivable1s_coq_prop_r; try exact Hready; try exact Hreuse_conflict;
          cbn [Mroute msolver_propagation_db_wmap_update
            msolver_propagation_overlay msolver_propagation_update ]; try assumption; try reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_65 : solver_propagate_which_implies_wit_65.
Proof.
  Unfold.
  left; intros.
  bind_fact ( Zlength candidate_post_memory = Zlength source_words ) as H_Zlength.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  assert (jj = ii) by lia; subst jj.
  prop_apply_p (PtrArray.seg_valid begin 0 ii
    (sublist 0 ii candidate_post_memory)).
  prop_apply_p (PtrArray.seg_valid begin (ii + 1) (Zlength source_words)
    (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
  Intros_p Hlo. Intros_p Hhi.
  rewrite <- H_Znth.
  rewrite replace_Znth_Znth by lia.
  unfold propagation_ptr_segment, StorePtrAsElement.storeA.
  (* arch port A03 -- rewriting sizeof_ptr unfolds the Arch alias, but
     PtrArray's lemmas are stated with the derived ptr_size_Z, and
     sep_apply_l_atomic matches syntactically; fold the alias back to
     ptr_size_Z here or the sep_apply below silently fails to fire. *)
  change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply_l_atomic (PtrArray.seg_single begin ii
    (Znth ii candidate_post_memory 0)).
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    (sublist 0 ii candidate_post_memory)
    ((Znth ii candidate_post_memory 0) :: nil)%list).
  - dump_pre_spatial. lia.
  - rewrite <- sublist_single by lia.
    rewrite <- (sublist_split 0 (ii + 1) ii candidate_post_memory) by lia.
    sep_apply_l_atomic (PtrArray.seg_merge_to_full begin 0 (ii + 1)
      (Zlength source_words) (sublist 0 (ii + 1) candidate_post_memory)
      (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
    + dump_pre_spatial. lia.
    + rewrite <- (sublist_split 0 (Zlength source_words) (ii + 1)
        candidate_post_memory) by lia.
      rewrite <- H_Zlength.
      rewrite sublist_self by reflexivity.
      replace (begin + 0 * ptr_size_Z) with begin by ring.
      replace (Zlength candidate_post_memory - 0)
        with (Zlength candidate_post_memory) by lia.
      cancel.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_66 : solver_propagate_which_implies_wit_66.
Proof.
  Unfold.
  left; intros.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Zlength candidate_post_memory = Zlength source_words ) as H_Zlength.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin 0 jj
    (sublist 0 jj candidate_post_memory)).
  prop_apply_p (PtrArray.seg_valid begin (jj + 1) ii
    (sublist (jj + 1) ii candidate_post_memory)).
  Intros_p Hlo. Intros_p Hmid.
  rewrite <- H_Znth.
  unfold StorePtrAsElement.storeA.
  (* Same arch-port-A03 note as in [proof_of_solver_propagate_which_implies_wit_65] above. *)
  change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply_l_atomic (PtrArray.seg_single begin jj
    (Znth ii candidate_post_memory 0)).
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj candidate_post_memory)
    ((Znth ii candidate_post_memory 0) :: nil)%list).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
      (sublist 0 jj candidate_post_memory ++
        ((Znth ii candidate_post_memory 0) :: nil))
      (sublist (jj + 1) ii candidate_post_memory)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (PtrArray.seg_single begin ii
        (Znth ii candidate_post_memory 0)).
      sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
        ((sublist 0 jj candidate_post_memory ++
            ((Znth ii candidate_post_memory 0) :: nil)) ++
          sublist (jj + 1) ii candidate_post_memory)
        ((Znth ii candidate_post_memory 0) :: nil)%list).
      * dump_pre_spatial. lia.
      * prop_apply_p (PtrArray.seg_valid begin (ii + 1)
          (Zlength source_words)
          (sublist (ii + 1) (Zlength source_words)
            candidate_post_memory)).
        Intros_p Hhi.
        sep_apply_l_atomic (PtrArray.seg_merge_to_full begin 0 (ii + 1)
          (Zlength source_words)
          (((sublist 0 jj candidate_post_memory ++
               ((Znth ii candidate_post_memory 0) :: nil)) ++
             sublist (jj + 1) ii candidate_post_memory) ++
            ((Znth ii candidate_post_memory 0) :: nil))
          (sublist (ii + 1) (Zlength source_words)
            candidate_post_memory)).
        -- dump_pre_spatial. lia.
        -- rewrite <- H_Zlength.
           replace (begin + 0 * ptr_size_Z) with begin by ring.
           replace (Zlength candidate_post_memory - 0)
             with (Zlength candidate_post_memory) by lia.
           rewrite (replace_Znth_split 0
             (Znth ii candidate_post_memory 0) jj
             candidate_post_memory) by lia.
           rewrite (sublist_split (jj + 1)
             (Zlength candidate_post_memory) ii
             candidate_post_memory) by lia.
           rewrite (sublist_split ii
             (Zlength candidate_post_memory) (ii + 1)
             candidate_post_memory) by lia.
           rewrite (sublist_single 0 ii candidate_post_memory) by lia.
           simpl.
           assert (HL :
             (((sublist 0 jj candidate_post_memory ++
                  ((Znth ii candidate_post_memory 0) :: nil)) ++
                sublist (jj + 1) ii candidate_post_memory) ++
               ((Znth ii candidate_post_memory 0) :: nil)) ++
              sublist (ii + 1) (Zlength candidate_post_memory)
                candidate_post_memory =
             sublist 0 jj candidate_post_memory ++
               Znth ii candidate_post_memory 0 ::
               sublist (jj + 1) ii candidate_post_memory ++
               Znth ii candidate_post_memory 0 ::
               sublist (ii + 1) (Zlength candidate_post_memory)
                 candidate_post_memory).
           { rewrite <- !app_assoc. reflexivity. }
           rewrite HL.
           cancel.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_67 : solver_propagate_which_implies_wit_67.
Proof.
 exact proof_of_solver_propagate_which_implies_wit_19.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_68 : solver_propagate_which_implies_wit_68.
Proof.
  Unfold.
  right; intros.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src copy_dst
      copy_memory ) as H_binary_watch_copy_progress.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( propagation_unit_conflict_ready n F A_arr K Mscan p scan_current watch0 false_lit clause_contents retained
      rest prob_route learnt_route Mroute ) as H_propagation_unit_conflict_ready.
  unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
  destruct H_binary_watch_copy_progress as
    [copied [copy_rest
      [Hwords [Hrawlen [Hdstle [Hsuffix
        [Hsrc [Hdst [Hcopy Hcopylen]]]]]]]]].
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as [Hscan [Hmem [Hjj [Hii Hwatchlen]]]].
  (* arch port A05 -- the Arch pointer-size constant is opaque to
     micromega ("Cannot find witness"), so unfold it for the current
     arch before the arithmetic below; this names no specific width. *)
  change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i.
  unfold_arch.
  assert (Hsrc_eq : copy_src = Zlength source_words) by lia.
  assert (Hrawprefix : raw_prefix = retained ++ garbage).
  {
  assert (Hraw : sublist 0 ii watch_memory = raw_prefix).
    { rewrite Hwords.
      rewrite <- Hrawlen.
      apply sublist_app_exact1. }
  assert (Hphys : sublist 0 ii watch_memory = retained ++ garbage).
    { rewrite Hmem.
      rewrite app_assoc.
      rewrite <- Hii.
      apply sublist_app_exact1. }
    congruence.
  }
  assert (Hcopy_rest_nil : copy_rest = nil).
  {
    assert (Hrest : rest = scan_current :: raw_suffix).
    { rewrite Hrawprefix in Hwords.
      rewrite Hmem in Hwords.
      rewrite <- app_assoc in Hwords.
      apply app_inv_head in Hwords.
      apply app_inv_head in Hwords.
      exact Hwords. }
    assert (Hrestlen : Zlength rest = 1 + Zlength copied).
    { rewrite Hmem in Hwatchlen.
      rewrite !Zlength_app in Hwatchlen.
      rewrite Zlength_app in Hii.
      rewrite Hsrc_eq in Hsrc.
      lia. }
    rewrite Hrest, Hsuffix, Zlength_cons, Zlength_app in Hrestlen.
    apply Zlength_nil_inv.
    lia.
  }
  subst copy_rest.
  rewrite app_nil_r in Hsuffix.
  assert (Hrest : rest = scan_current :: copied).
  {
    rewrite Hrawprefix in Hwords.
    rewrite Hmem in Hwords.
    rewrite <- app_assoc in Hwords.
    apply app_inv_head in Hwords.
    apply app_inv_head in Hwords.
    rewrite Hsuffix in Hwords.
    exact Hwords.
  }
  assert (Hjj_idx : 0 <= jj < Zlength watch_memory).
  {
    rewrite Hwatchlen.
    pose proof (Zlength_nonneg copied).
    lia.
  }
  assert (Hwatch_prefix : sublist 0 jj watch_memory = retained).
  {
    rewrite Hmem.
    rewrite <- Hjj.
    apply sublist_app_exact1.
  }
  assert (Hrepl_prefix :
    sublist 0 (jj + 1) (replace_Znth jj scan_current watch_memory) =
      retained ++ (scan_current :: nil)%list).
  {
    rewrite (replace_Znth_split 0 scan_current jj watch_memory Hjj_idx).
    rewrite Hwatch_prefix.
    replace (retained ++ scan_current ::
      sublist (jj + 1) (Zlength watch_memory) watch_memory)
      with ((retained ++ (scan_current :: nil)%list) ++
        sublist (jj + 1) (Zlength watch_memory) watch_memory)
      by (rewrite <- app_assoc; reflexivity).
    replace (jj + 1) with
      (Zlength (retained ++ (scan_current :: nil)%list)) by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil, Hjj; lia).
    apply sublist_app_exact1.
  }
  destruct (msat_binary_watch_write_prefix_p7 copied
    (replace_Znth jj scan_current watch_memory)
    (retained ++ (scan_current :: nil)%list) (jj + 1))
    as [garbage_route Hwritten].
  - lia.
  - rewrite Zlength_replace_Znth, Hwatchlen.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hjj. lia.
  - exact Hrepl_prefix.
  - assert (Hcopy_decomp :
      copy_memory = (retained ++ rest) ++ garbage_route).
    {
      rewrite Hcopy, Hwritten, Hrest.
      rewrite <- !app_assoc.
      reflexivity.
    }
    assert (Hfinal : propagation_watch_scan_physical source_words
      (retained ++ rest) moved nil garbage_route copy_memory
      (Zlength source_words) (Zlength (retained ++ rest))).
    {
      unfold propagation_watch_scan_physical.
      repeat split.
      + apply wlist_scan_abort. exact Hscan.
      + rewrite app_nil_r. exact Hcopy_decomp.
      + rewrite <- Hcopy_decomp, Hcopylen, Hwatchlen. reflexivity.
      + rewrite Hcopylen, Hwatchlen. reflexivity.
    }
    assert (Hstep : propagation_scan_conflict_step source_words retained
      moved rest copy_memory garbage_route (retained ++ rest)).
    { unfold propagation_scan_conflict_step. split; [reflexivity|exact Hfinal]. }
    unfold propagation_unit_conflict_ready in H_propagation_unit_conflict_ready.
    destruct H_propagation_unit_conflict_ready as [Hdb Htransition].
    assert (Hsem : solver_propagation_scan_semantics n F A_arr K Mroute p
      scan_current (retained ++ rest) nil).
    { exact (proj2 Htransition). }
    Exists garbage_route.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_69 : solver_propagate_which_implies_wit_69.
Proof.
  unfold solver_propagate_which_implies_wit_69.
  unfold stats_propagations, stats_inspects.
  Unfold.
  left; intros.
  unfold solver_propagation_nonwatch_rest_at.
  Intros rsn_route trl_route.
  Exists trl_route rsn_route.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_70 : solver_propagate_which_implies_wit_70.
Proof.
  Unfold.
  left; intros.
  bind_fact ( Zlength candidate_post_memory = Zlength source_words ) as H_Zlength.
  assert (jj = ii) by lia; subst jj.
  prop_apply_p (PtrArray.seg_valid begin 0 ii
    (sublist 0 ii candidate_post_memory)).
  prop_apply_p (PtrArray.seg_valid begin (ii + 1) (Zlength source_words)
    (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
  Intros_p Hlo. Intros_p Hhi.
  unfold propagation_ptr_segment, StorePtrAsElement.storeA.
  (* Same arch-port-A03 note as in [proof_of_solver_propagate_which_implies_wit_65] above. *)
  change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply_l_atomic (PtrArray.seg_single begin ii scan_current).
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    (sublist 0 ii candidate_post_memory)
    (scan_current :: nil)%list).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic (PtrArray.seg_merge_to_full begin 0 (ii + 1)
      (Zlength source_words)
      (sublist 0 ii candidate_post_memory ++ (scan_current :: nil))
      (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
    + dump_pre_spatial. lia.
    + rewrite (replace_Znth_split 0 scan_current ii candidate_post_memory)
        by lia.
      rewrite <- H_Zlength.
      replace (begin + 0 * ptr_size_Z) with begin by ring.
      replace (Zlength candidate_post_memory - 0)
        with (Zlength candidate_post_memory) by lia.
      replace ((sublist 0 ii candidate_post_memory ++
                  (scan_current :: nil)) ++
                 sublist (ii + 1) (Zlength candidate_post_memory)
                   candidate_post_memory)
        with (sublist 0 ii candidate_post_memory ++
                scan_current :: sublist (ii + 1)
                  (Zlength candidate_post_memory) candidate_post_memory)
        by (rewrite <- app_assoc; reflexivity).
      cancel.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_74 : solver_propagate_which_implies_wit_74.
Proof.
  Unfold.
  right; intros.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ logical_words :: scan_wm_post ) as H_ms_wm.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + ii * sizeof ( PTR ) ) as H_i.
  prop_apply_p (PtrArray.full_Zlength begin (Zlength source_words)
    watch_memory).
  Intros_p Hlen.
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as [Hscan [Hmem [Hjj [Hii Hmemlen]]]].
  (* Same arch-port-A05 note as in [proof_of_solver_propagate_which_implies_wit_68] above. *)
  change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i.
  unfold_arch.
  assert (Hii_upper : ii <= Zlength source_words).
  { rewrite Hmem in Hmemlen.
    rewrite !Zlength_app in Hmemlen.
    rewrite Zlength_app in Hii.
    pose proof (Zlength_nonneg rest).
    lia. }
  assert (Hii_eq : ii = Zlength source_words) by lia.
  assert (Hi_eq : i = endvar) by lia.
  assert (Hrestlen : Zlength rest = 0).
  { rewrite Hmem in Hmemlen.
    rewrite !Zlength_app in Hmemlen.
    rewrite Zlength_app in Hii.
    lia. }
  apply Zlength_nil_inv in Hrestlen.
  subst rest ii.
  assert (Hws : ws = vecp_slot wlists_entry p) by lia.
  assert (Hlogical : logical_words = retained).
  { rewrite H_logical_words, app_nil_r. reflexivity. }
  assert (Hwm : ms_wm Mscan =
    scan_wm_pre ++ retained :: scan_wm_post).
  { rewrite H_ms_wm, Hlogical. reflexivity. }
  sep_apply_l_atomic (PtrArray.full_to_seg begin
    (Zlength source_words) watch_memory).
  rewrite Hlen in *.
  entailer_with ltac:(lia).
  unfold propagation_watch_scan_physical.
  repeat split; try assumption; reflexivity.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_75 : solver_propagate_which_implies_wit_75.
Proof.
  Unfold.
  left; intros.
  subst j.
  entailer_with ltac:(lia).
  replace (begin + jj * sizeof(PTR) - begin) with (jj * sizeof(PTR)) by ring.
  rewrite Z.quot_mul.
  - reflexivity.
  - (* The side condition is `sizeof (PTR) <> 0`; `sizeof_ptr` yields the Arch
          constant, which is opaque to micromega.  `unfold_arch` reduces it for the current
          arch. *)
    change (sizeof (PTR)) with ptr_size_Z. solve_arch.
Qed.

(* ===== solver_reducedb which_implies wits (4 proofs) ===== *)
Lemma proof_of_solver_reducedb_which_implies_wit_9 : solver_reducedb_which_implies_wit_9.
Proof.
  Unfold.
  left.
  intros.
  pre_process_default.
  bind_fact ( msolver_inv n F A_arr A_inst Mcur ) as H_msolver_inv.
  bind_fact ( db_compaction_inv Mcur words i j ) as H_db_compaction_inv.
  bind_fact ( i < Zlength words ) as H_i.
  unfold clause_remove_post at 1.
  Intros wm' stats'.
  coq_prop_lift.
  match goal with
  | Hpost : clause_remove_result _ _ _ wm' /\ _ |- _ =>
      destruct Hpost as [Hremove0 [Hstats [Hreasons Hunlocked]]]
  end.
  unfold clause_db_pair_remainder at 1.
  Split.
  - Intros co pre post. coq_prop_lift.
    match goal with
    | Hdb : db_nil = pre ++ (Znth (i - 0) words 0, co) :: post /\ _ |- _ =>
        destruct Hdb as [Hbad _]
    end.
    destruct pre; simpl in Hbad; discriminate.
  - Intros co pre post. coq_prop_lift.
    match goal with
    | Hdb : ms_learnt Mcur = pre ++ (Znth (i - 0) words 0, co) :: post /\ _ |- _ =>
        destruct Hdb as [Hlearn [Hlits Hlearnt]]
    end.
    set (c := Znth (i - 0) words 0).
    assert (Hfresh : ~ In c (map fst pre)).
    { eapply db_wf_learnt_split_fresh__reducedb.
      - exact (msi_db_wf H_msolver_inv).
      - exact Hlearn. }
    assert (Hremove :
      clause_remove_result c (co_lits co) (ms_wm Mcur) wm').
    { unfold c. rewrite Hlits. exact Hremove0. }
    set (Mnext := msolver_remove_clause Mcur true c wm' stats').
    match goal with
    | Hbase : minisat_base_watch_completed ?entry ->
        minisat_base_watch_completed Mcur |- _ =>
      assert (Hbase_next : minisat_base_watch_completed entry ->
          minisat_base_watch_completed Mnext) by
        (intro Hentry; unfold Mnext;
         apply minisat_base_watch_completed_remove_clause__api_reentry;
         exact (Hbase Hentry))
    end.
    assert (Hcapacity : ms_cap Mnext = ms_cap Mcur) by reflexivity.
    assert (Hinvnext : msolver_inv n F A_arr A_inst Mnext).
    { unfold Mnext.
      eapply msolver_inv_remove_learnt__reducedb;
        eassumption. }
    assert (Hstep : db_compaction_step Mcur c Mnext).
    { unfold Mnext, db_compaction_step. split.
      - right. exists wm', stats'. reflexivity.
      - split; reflexivity. }
    assert (Hcompnext : db_compaction_inv Mnext words (i + 1) j).
    { unfold Mnext, c.
      eapply db_compaction_inv_remove_current__reducedb.
      - exact (msi_weak H_msolver_inv).
      - exact H_db_compaction_inv.
      - exact H_i.
      - replace (i - 0) with i by lia. reflexivity. }
    assert (Hlearnnext : ms_learnt Mnext = pre ++ post).
    { unfold Mnext.
      pose proof (msolver_remove_learnt_split_proj__reducedb
        Mcur c co pre post wm' stats' Hlearn Hfresh) as Hproj.
      exact Hproj. }
    Exists Mnext.
    entailer_with ltac:(lia).
    rewrite Hlearnnext.
    sep_apply (clause_db_rep_app_intro pre post).
    unfold Mnext, c.
    rewrite (solver_db_mutation_frame_at_remove_learnt__reducedb
      s Mcur levels_ptr (Znth (i - 0) words 0) wm' stats').
    unfold msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update.
    cbn.
    unfold db_nil.
    unfold solver_wlists_handle, PtrArray.seg.
    msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_5 : solver_reducedb_which_implies_wit_5.
Proof. exact proof_of_solver_reducedb_which_implies_wit_9. Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_10 : solver_reducedb_which_implies_wit_10.
Proof.
  pose proof msat_clause_fields_to_rep as Hraw.
  pose proof msat_int_cell_le_max_signed as Hcapmax.
  unfold solver_reducedb_which_implies_wit_10.
  left.
  intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mcur ) as H_msolver_inv.
  bind_fact ( msat_fp32_nonnegative activity_now ) as H_msat_fp32_nonnegative.
  pre_process_default.
  prop_apply (Hcapmax (&(s # "solver_t" ->ₛ "learnts" .ₛ "cap"))).
  Intros.
  prop_apply valid_store_int.
  Intros.
  prop_apply valid_store_int.
  Intros.
  prop_apply PtrArray.undef_seg_valid.
  Intros.
  entailer_with ltac:(lia).
  all: (try rewrite Zlength_replace_Znth);
    (try (unfold db_compaction_step; repeat split; auto)).
  unfold vecp_rep_at.
  sep_apply PtrArray.full_to_seg.
  unfold clause_db_pair_remainder.
  entailer_with ltac:(lia).
  all: (try rewrite Zlength_replace_Znth);
    (try lia).
  Split.
  asrt_simpl.
  Intros co pre post.
  match goal with
     | Hdb : db_nil = _ ++ _ :: _ /\ _ |- _ => destruct Hdb as [Hbad _]
     end.
  destruct pre; simpl in Hbad; discriminate.
  asrt_simpl.
  Intros co pre post.
  match goal with
     | Hdb : ms_learnt Mcur = _ ++ _ :: _ /\ _ |- _ =>
         destruct Hdb as [Hlearn [Hlits Hlearnt]]
     end.
  unfold db_nil.
  rewrite clause_db_rep_nil.
  assert (Hcin : In (Znth (i - 0) words 0, co) (msolver_db Mcur)).
  1: { unfold msolver_db. rewrite Hlearn. apply in_or_app. right.
       apply in_or_app. right. left. reflexivity. }
  sep_apply (Hraw n
       (msolver_db Mcur) (Znth (i - 0) words 0) co lits_now activity_now
       (msi_db_wf H_msolver_inv) Hcin Hlits Hlearnt H_msat_fp32_nonnegative).
  rewrite Hlearn.
  assert (Hcons :
       MiniSatClause.rep (Znth (i - 0) words 0) (co_learnt co) (co_lits co) **
       clause_db_rep post
       |-- clause_db_rep ((Znth (i - 0) words 0, co) :: post)).
  1: { rewrite clause_db_rep_cons. entailer_with ltac:(lia). }
  sepcon_lift (clause_db_rep post).
  sepcon_lift
       (MiniSatClause.rep (Znth (i - 0) words 0) (co_learnt co) (co_lits co)).
  sepcon_lift (clause_db_rep pre).
  sepcon_assoc_change.
  sep_apply Hcons.
  sep_apply (clause_db_rep_app_intro pre ((Znth (i - 0) words 0, co) :: post)).
  entailer_with ltac:(lia).
  all: try (unfold vecp_size_addr, vecp_cap_addr, vecp_ptr_addr; csimpl; entailer_with ltac:(lia)).
  all: (try (
    prop_apply (valid_store_int (&(s # "solver_t" ->ₛ "learnts" .ₛ "cap")));
    Intros;
    entailer_with ltac:(lia);
    lia));
    (try lia).
  all: try (
    match goal with
    | Hcomp : db_compaction_inv _ _ _ _ |- _ =>
        unfold db_compaction_inv in Hcomp;
        destruct Hcomp as [Hj0 [Hji [Hil Hmap]]];
        rewrite Hmap;
        replace (i - 0) with i by lia;
        apply msat_db_compaction_shift_p7;
        lia
    end).
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_6 : solver_reducedb_which_implies_wit_6.
Proof. exact proof_of_solver_reducedb_which_implies_wit_10. Qed.

(* ===== solver_search entail wits (3 proofs) ===== *)
Lemma proof_of_solver_search_entail_wit_2_1 : solver_search_entail_wit_2_1.
Proof.
  unfold solver_search_entail_wit_2_1.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  right.
  intros.
  pre_process_default.
  bind_fact ( ms_root_level Manalyzed > Znth (retval_5 - 0) (mt_levels (ms_core Manalyzed)) 0 ) as H_ms_root_level.
  bind_fact ( retval_5 = lit_var_c (Znth (1 - 0) words 0) ) as H_retval_5.
  bind_fact ( analyze_backjump_cert n Manalyzed words backjump ) as H_analyze_backjump_cert.
  entailer_with ltac:(lia).
  unfold analyze_backjump_cert in H_analyze_backjump_cert.
  destruct H_analyze_backjump_cert as [_ [Hback _]].
  assert (Hlt : Z.ltb 1 (Zlength words) = true).
  { apply Z.ltb_lt. lia. }
  rewrite Hlt in Hback.
  rewrite Hback.
  rewrite H_retval_5 in H_ms_root_level.
  replace (1 - 0) with 1 in H_ms_root_level by lia.
  replace (lit_var_c (Znth 1 words 0) - 0)
    with (lit_var_c (Znth 1 words 0)) in H_ms_root_level by lia.
  symmetry.
  apply Z.max_l.
  lia.
Qed.

Lemma proof_of_solver_search_entail_wit_2_2 : solver_search_entail_wit_2_2.
Proof.
  unfold solver_search_entail_wit_2_2.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  right.
  intros.
  pre_process_default.
  bind_fact ( ms_root_level Manalyzed <= Znth (retval_5 - 0) (mt_levels (ms_core Manalyzed)) 0 ) as H_ms_root_level.
  bind_fact ( retval_5 = lit_var_c (Znth (1 - 0) words 0) ) as H_retval_5.
  bind_fact ( analyze_backjump_cert n Manalyzed words backjump ) as H_analyze_backjump_cert.
  entailer_with ltac:(lia).
  unfold analyze_backjump_cert in H_analyze_backjump_cert.
  destruct H_analyze_backjump_cert as [_ [Hback _]].
  assert (Hlt : Z.ltb 1 (Zlength words) = true).
  { apply Z.ltb_lt. lia. }
  rewrite Hlt in Hback.
  rewrite H_retval_5 in H_ms_root_level.
  rewrite H_retval_5.
  replace (1 - 0) with 1 by lia.
  replace (lit_var_c (Znth 1 words 0) - 0)
    with (lit_var_c (Znth 1 words 0)) by lia.
  rewrite Hback.
  replace (1 - 0) with 1 in H_ms_root_level by lia.
  replace (lit_var_c (Znth 1 words 0) - 0)
    with (lit_var_c (Znth 1 words 0)) in H_ms_root_level by lia.
  symmetry.
  apply Z.max_r.
  lia.
Qed.

Lemma proof_of_solver_search_entail_wit_2_3 : solver_search_entail_wit_2_3.
Proof.
  unfold solver_search_entail_wit_2_3.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  right.
  intros.
  pre_process_default.
  bind_fact ( analyze_backjump_cert n Manalyzed words backjump ) as H_analyze_backjump_cert.
  entailer_with ltac:(lia).
  unfold analyze_backjump_cert in H_analyze_backjump_cert.
  destruct H_analyze_backjump_cert as [_ [Hback _]].
  assert (Hnot : Z.ltb 1 (Zlength words) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hnot in Hback.
  symmetry.
  exact Hback.
Qed.

(* ===== solver_search safety wits (4 proofs) ===== *)
Lemma proof_of_solver_search_safety_wit_52 : solver_search_safety_wit_52.
Proof.
  msat_search_safety_qtail_gap_p7.
Qed.

Lemma proof_of_solver_search_safety_wit_53 : solver_search_safety_wit_53.
Proof.
  msat_search_safety_qtail_gap_p7.
Qed.

Lemma proof_of_solver_search_safety_wit_54 : solver_search_safety_wit_54.
Proof.
  msat_search_safety_qtail_gap_p7.
Qed.

Lemma proof_of_solver_search_safety_wit_55 : solver_search_safety_wit_55.
Proof.
  msat_search_safety_qtail_gap_p7.
Qed.

(* ===== solver_search return wits (2 proofs) ===== *)
Lemma proof_of_solver_search_return_wit_7 : solver_search_return_wit_7.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Right.
  Exists Mrecord_cap.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_10 : solver_search_return_wit_10.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Left. Left. Right.
  Exists Mrootconf.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_simplify which_implies wits ===== *)
Lemma proof_of_solver_simplify_which_implies_wit_3 : solver_simplify_which_implies_wit_3.
Proof.
  left. intros.
  apply solver_simplify_pre_split__simplify.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_4 : solver_simplify_which_implies_wit_4.
Proof.
  left. intros.
  apply solver_simplify_lim_join_rep_levels__simplify.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_5 : solver_simplify_which_implies_wit_5.
Proof.
  left. intros.
  apply solver_rep_levels_assigns_split__simplify.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_6 : solver_simplify_which_implies_wit_6.
Proof.
  left. intros.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec M_solver_simplify_spec ) as H_msolver_inv.
  bind_fact ( ms_capacity_root_propagation_pending M_solver_simplify_spec = 0 ) as H_ms_capacity_root_propagation_pending.
  assert (Hprop : solver_propagation_inv smp_n_solver_simplify_spec
    smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    (PropagationAssuming smp_A_arr_solver_simplify_spec)
    M_solver_simplify_spec).
  { unfold solver_propagation_inv. simpl.
    split.
    - exact H_ms_capacity_root_propagation_pending.
    - constructor.
      + exact (msas_weak H_msolver_inv).
      + exact (msas_prop_level H_msolver_inv).
      + exact (msas_watch_frontier H_msolver_inv).
      + left. exact (msas_heap_covers H_msolver_inv).
      + exact (msas_reasonless_current H_msolver_inv). }
  unfold solver_propagate_pre.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_7 : solver_simplify_which_implies_wit_7.
Proof.
  left. intros.
  bind_fact (msolver_inv_assuming_strong smp_n_solver_simplify_spec
    smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec M_solver_simplify_spec) as Hentry.
  bind_fact (Zlength (mt_lim (ms_core M_solver_simplify_spec)) = 0) as Hdepth.
  unfold solver_propagate_post.
  rewrite !orp_sepcon_right_equiv.
  repeat apply derivable1_orp_elim.
  - Intros Mprop.
    match goal with Hpost : solver_propagation_inv _ _ _ _ Mprop /\ _ |- _ =>
      destruct Hpost as [Hinv [Hframe [Hreuse [Hseed Hdrain]]]]
    end.
    pose proof (solver_propagation_drained_assuming_strong
      _ _ _ _ Mprop Hinv Hdrain) as Hstrong.
    destruct Hframe as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
    assert (Hlim0 : Zlength (mt_lim (ms_core Mprop)) = 0).
    { rewrite Hlim. exact Hdepth. }
    assert (Hpending : ms_capacity_root_propagation_pending Mprop = 0).
    { exact (proj1 Hinv). }
    assert (Hready : solver_simplify_reuse M_solver_simplify_spec Mprop).
    { intros [Hcompleted | Hfalse].
      - apply (minisat_base_completion_at_depth_zero__api_reentry
          smp_n_solver_simplify_spec Mprop
          (msa_trail_wf (msas_weak Hstrong))
          (msa_db_wf (msas_weak Hstrong)) Hlim0).
        apply (proj1 Hreuse).
        eapply minisat_full_completion_implies_base__api_reentry;
          [exact (msa_trail_wf (msas_weak Hentry))|
           exact (msa_db_wf (msas_weak Hentry))|exact Hcompleted].
      - exfalso. eapply minisat_resident_false_excludes_drained_success__api_reentry;
          [exact (msa_shape (msas_weak Hstrong))|
           exact (msa_db_wf (msas_weak Hstrong))|
           exact (msa_trail_wf (msas_weak Hstrong))|exact Hdrain|
           exact (msas_watch_frontier Hstrong)|exact (proj2 Hreuse Hfalse)]. }
    assert (Hmodel_empty : ms_model M_solver_simplify_spec = nil -> ms_model Mprop = nil).
    { rewrite Hmodel. tauto. }
    assert (Hdecay_positive : msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
      msat_fp32_positive_finite (ms_cla_decay Mprop)).
    { rewrite Hdecay. tauto. }
    Exists Mprop.
    entailer_with ltac:(lia); try assumption; try lia.
    apply store_int_undef_store_int.
  - Intros Mprop p focus C. entailer_with ltac:(lia).
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_8 : solver_simplify_which_implies_wit_8.
Proof.
  left. intros.
  apply solver_rep_assigns_simplify_control_split__simplify.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_9 : solver_simplify_which_implies_wit_9.
Proof.
  left. intros.
  apply solver_simplify_control_join_rep_assigns__simplify.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_10 : solver_simplify_which_implies_wit_10.
Proof.
  left. intros.
  apply solver_simplify_control_join_rep_reasons__simplify.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_11 : solver_simplify_which_implies_wit_11.
Proof.
  Unfold.
  intros.
  unfold solver_simplify_outer_loop.
  Intros Mtype.
  destruct H as
    [Hcap [Hroot [Hreuse [Htype_range [Hinv [Hlim [Hqhead [Hpending [Hseed [Hmodel Hdecay]]]]]]]]]].
  assert (Htype : type = 0 \/ type = 1) by lia.
  assert (Hlim_nil : mt_lim (ms_core Mtype) = (@nil Z)).
  { apply Zlength_nil_inv. exact Hlim. }
  destruct Htype as [Htype | Htype].
  - subst type.
    rewrite <- derivable1_orp_intros2.
    sep_apply
      (solver_rep_reasons_simplify_open_0__simplify
        s Mtype reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec Hlim_nil).
    Intros asg_type.
    Exists asg_type
      (db_words (solver_selected_db 0 Mtype)) Mtype.
    unfold msat_fp32_same, z_nil.
    entailer_with ltac:(lia).
  - subst type.
    rewrite <- derivable1_orp_intros1.
    sep_apply
      (solver_rep_reasons_simplify_open_1__simplify
        s Mtype reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec Hlim_nil).
    Intros asg_type.
    Exists asg_type
      (db_words (solver_selected_db 1 Mtype)) Mtype.
    unfold msat_fp32_same, z_nil.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_12 : solver_simplify_which_implies_wit_12.
Proof.
  right. intros.
  bind_fact ( 0 <= j ) as H_j.
  bind_fact ( j <= i ) as H_j_2.
  bind_fact ( i < Zlength words ) as H_i.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  replace (i - 0) with i in * by lia.
  replace (0 - 0) with 0 in * by lia.
  destruct
    (solver_simplify_compaction_lookup__simplify
      type Mcur words i j H_j H_j_2 H_i H_solver_simplify_db_compaction_inv)
    as [co [Htype Hin_selected]].
  pose proof (msas_weak H_msolver_inv) as Hweak.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof (msa_size Hweak) as Hsize.
  pose proof (msa_trail_wf Hweak) as Htrail.
  pose proof (mtw_cells Htrail) as Hcells.
  assert (Hin_db :
    In (Znth i words 0, co) (msolver_db Mcur)).
  { eapply solver_selected_db_in;
      [exact Htype | exact Hin_selected]. }
  assert (Hobj : obj_wf smp_n_solver_simplify_spec co).
  { eapply db_wf_obj; [exact (msa_db_wf Hweak) | exact Hin_db]. }
  destruct Hobj as [Hlen [Hlits Hnodup]].
  assert (Hlits_size : Forall (lit_wf_c (ms_size Mcur)) (co_lits co)).
  { rewrite <- Hsize. exact Hlits. }
  assert (Hhead :
    0 <= lit_var_c (Znth 0 (co_lits co) 0) < ms_size Mcur).
  { assert (Hwf : lit_wf_c (ms_size Mcur)
        (Znth 0 (co_lits co) 0)).
    { apply Forall_Znth_elim; [exact Hlits_size | lia]. }
    apply lit_var_c_in_range. exact Hwf. }
  sep_apply
    (solver_selected_clause_focus__simplify
      type Mcur (Znth i words 0) co Htype Hin_selected).
  Exists co.
  unfold solver_simplify_db_rest_at, MiniSatClause.rep.
  unfold solver_shape in Hshape.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_13 : solver_simplify_which_implies_wit_13.
Proof.
  right. intros.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( db_lookup (solver_selected_db type Mcur) (Znth (i - 0) words 0) co ) as H_db_lookup.
  bind_fact ( Znth (lit_var_c (Znth (0 - 0) (co_lits co) 0) - 0) (ms_reason_words Mcur) 0 <> Znth (i - 0) words 0 ) as
      H_Znth.
  bind_fact ( Znth (i - 0) words 0 % 2 = 0 ) as H_Znth_2.
  pose proof (msas_weak H_msolver_inv) as Hweak.
  bind_fact (Zlength (mt_lim (ms_core Mcur)) = 0) as Hdepth.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    smp_n_solver_simplify_spec smp_F_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mcur H_msolver_inv Hdepth) as Hnormal.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof (msa_size Hweak) as Hsize.
  assert (Hin_selected :
    In (Znth (i - 0) words 0, co) (solver_selected_db type Mcur)).
  { exact H_db_lookup. }
  assert (Hin_db : In (Znth (i - 0) words 0, co) (msolver_db Mcur)).
  { eapply solver_selected_db_in_any__simplify.
    exact Hin_selected. }
  assert (Hready_n : clause_remove_ready smp_n_solver_simplify_spec
    (Znth (i - 0) words 0) (co_lits co) (ms_wm Mcur)
    (ms_wcaps Mcur) (ms_stats Mcur)).
  { eapply clause_remove_ready_of_inv__simplify with
      (M := msolver_set_root Mcur 0); [exact Hnormal|exact Hin_db]. }
  assert (Hready : clause_remove_ready (ms_size Mcur)
    (Znth (i - 0) words 0) (co_lits co) (ms_wm Mcur)
    (ms_wcaps Mcur) (ms_stats Mcur)).
  { rewrite <- Hsize. exact Hready_n. }
  assert (Hunlocked : clause_unlocked_words (Znth (i - 0) words 0)
    (ms_reason_words Mcur)).
  { eapply solver_simplify_head_unlocked with (M := msolver_set_root Mcur 0);
      [exact (msi_weak Hnormal) | exact Hin_db |].
    unfold co_watch0.
    replace (0 - 0) with 0 in H_Znth by lia.
    replace (lit_var_c (Znth 0 (co_lits co) 0) - 0)
      with (lit_var_c (Znth 0 (co_lits co) 0)) in H_Znth by lia.
    exact H_Znth. }
  unfold clause_remove_pre, MiniSatClause.rep.
  unfold solver_shape in Hshape.
  entailer_with ltac:(lia).
  rewrite Z.rem_mod_nonneg in H_Znth_2 by lia.
  exact H_Znth_2.
Qed.

(* ===== solver_solve entail wits ===== *)
Lemma proof_of_solver_solve_entail_wit_8_7 : solver_solve_entail_wit_8_7.
Proof.
  Unfold; intros;
  rename n_solver_solve_spec into n;
  rename F_solver_solve_spec into F;
  rename A_arr_solver_solve_spec into A_arr; Right.
  msat_solve_assumption_true_step_p7 n F A_arr raw_2 k_2 Mcur_2 endvar_pre begin_pre.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_8 : solver_solve_entail_wit_8_8.
Proof.
  Unfold; intros;
  rename n_solver_solve_spec into n;
  rename F_solver_solve_spec into F;
  rename A_arr_solver_solve_spec into A_arr; Right.
  msat_solve_assumption_true_step_p7 n F A_arr raw_2 k_2 Mcur_2 endvar_pre begin_pre.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_9 : solver_solve_entail_wit_8_9.
Proof.
  Unfold; intros;
  rename n_solver_solve_spec into n;
  rename F_solver_solve_spec into F;
  rename A_arr_solver_solve_spec into A_arr; Left.
  msat_solve_assumption_prop_step_p7 n F A_arr raw_2 k_2 Mprop endvar_pre begin_pre.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_10 : solver_solve_entail_wit_8_10.
Proof.
  Unfold; intros;
  rename n_solver_solve_spec into n;
  rename F_solver_solve_spec into F;
  rename A_arr_solver_solve_spec into A_arr; Left.
  msat_solve_assumption_prop_step_p7 n F A_arr raw_2 k_2 Mprop endvar_pre begin_pre.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_11 : solver_solve_entail_wit_8_11.
Proof.
  Unfold; intros;
  rename n_solver_solve_spec into n;
  rename F_solver_solve_spec into F;
  rename A_arr_solver_solve_spec into A_arr; Right.
  msat_solve_assumption_prop_step_p7 n F A_arr raw_2 k_2 Mprop endvar_pre begin_pre.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_12 : solver_solve_entail_wit_8_12.
Proof.
  Unfold; intros;
  rename n_solver_solve_spec into n;
  rename F_solver_solve_spec into F;
  rename A_arr_solver_solve_spec into A_arr; Right.
  msat_solve_assumption_prop_step_p7 n F A_arr raw_2 k_2 Mprop endvar_pre begin_pre.
Qed.

Lemma proof_of_solver_solve_entail_wit_9_1 : solver_solve_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( assumption_root_install n F A_arr Mcur Mroot A_inst ) as H_assumption_root_install.
  bind_fact ( endvar_pre = begin_pre + Zlength raw * sizeof ( INT ) ) as H_endvar_pre.
  bind_fact ( A_arr = assumption_prefix raw (Zlength raw) ) as H_A_arr.
  bind_fact ( Forall (lit_wf_c n) raw ) as H_Forall.
  bind_fact ( raw <> nil ) as H_raw.
  assert (HA : A_arr = lits_denote raw).
  { rewrite H_A_arr.
    unfold assumption_prefix.
    rewrite sublist_self by reflexivity.
    reflexivity. }
  unfold assumption_root_install in H_assumption_root_install.
  destruct H_assumption_root_install as
    [HAinst [HMroot [Hinv [Hatroot [Hqhead [Hpending Hshadow]]]]]].
  assert (Hrestart_frame :
      ms_cap Mroot = ms_cap M_solver_solve_spec /\
      (solver_query_reuse_guard M_solver_solve_spec ->
       minisat_base_watch_completed Mroot)).
  { split; assumption. }
  assert (Harray_facts :
      endvar_pre = begin_pre + Zlength raw * sizeof ( INT ) /\
      A_arr = lits_denote raw /\ Forall (lit_wf_c n) raw /\
      (raw = nil -> valid_int_position begin_pre)).
  { split; [exact H_endvar_pre|].
    split; [exact HA|].
    split; [exact H_Forall|].
    intros Hnil.
    exfalso.
    apply H_raw.
    exact Hnil. }
  unfold solver_restart_loop, assumptions_array.
  Exists raw.
  entailer_with ltac:(lia).
  Exists Mroot A_inst.
  unfold solver_search_result, solver_search_reuse.
  Left.
  split_pure_spatial.
  - Right.
    Exists Mroot.
    entailer_with ltac:(lia).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_solver_solve_entail_wit_9_2 : solver_solve_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( assumption_root_install n F A_arr Mcur Mroot A_inst ) as H_assumption_root_install.
  bind_fact ( endvar_pre = begin_pre + Zlength raw * sizeof ( INT ) ) as H_endvar_pre.
  bind_fact ( A_arr = assumption_prefix raw (Zlength raw) ) as H_A_arr.
  bind_fact ( Forall (lit_wf_c n) raw ) as H_Forall.
  bind_fact ( valid_int_position begin_pre ) as H_valid_int_position.
  assert (HA : A_arr = lits_denote raw).
  { rewrite H_A_arr.
    unfold assumption_prefix.
    rewrite sublist_self by reflexivity.
    reflexivity. }
  unfold assumption_root_install in H_assumption_root_install.
  destruct H_assumption_root_install as
    [HAinst [HMroot [Hinv [Hatroot [Hqhead [Hpending Hshadow]]]]]].
  assert (Hrestart_frame :
      ms_cap Mroot = ms_cap M_solver_solve_spec /\
      (solver_query_reuse_guard M_solver_solve_spec ->
       minisat_base_watch_completed Mroot)).
  { split; assumption. }
  assert (Harray_facts :
      endvar_pre = begin_pre + Zlength raw * sizeof ( INT ) /\
      A_arr = lits_denote raw /\ Forall (lit_wf_c n) raw /\
      (raw = nil -> valid_int_position begin_pre)).
  { split; [exact H_endvar_pre|].
    split; [exact HA|].
    split; [exact H_Forall|].
    intros _.
    exact H_valid_int_position. }
  unfold solver_restart_loop, assumptions_array.
  Exists raw.
  entailer_with ltac:(lia).
  Exists Mroot A_inst.
  unfold solver_search_result, solver_search_reuse.
  Left.
  split_pure_spatial.
  - Right.
    Exists Mroot.
    entailer_with ltac:(lia).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_solver_solve_entail_wit_11 : solver_solve_entail_wit_11.
Proof.
  Unfold.
  right.
  intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  unfold solver_prepare_capacity_post.
  Intros M.
  destruct H as (Hexhausted & Hroot & Hshadow & Hcap & Hreuse).
  pose proof (solver_operational_root_size n F M Hroot) as Hsize.
  lazymatch type of Hreuse with
  | minisat_base_watch_completed ?prepared -> _ =>
      lazymatch goal with
      | Hentry : solver_query_reuse ?entry prepared |- _ =>
          assert (Hwatch : solver_query_reuse_guard entry -> solver_query_watch_ready M)
            by (intro Hready; exact (Hreuse (Hentry Hready)))
      end
  end.
  Exists M.
  unfold solver_capacity_arm_at.
  msat_manual_entailer_with ltac:(lia).
Qed.


(* ===== solver_solve which_implies wits (10 proofs) ===== *)
Lemma proof_of_solver_solve_which_implies_wit_6 : solver_solve_which_implies_wit_6.
Proof.
  Unfold. left; intros.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M0.
  rename n_solver_solve_spec into n. rename F_solver_solve_spec into F.
  assert (Hbc : minisat_base_watch_completed (msolver_resume_pending M0))
    by exact (solver_update_watch_ready_base_completed__api_reentry n F M0 PreH1 PreH2).
  assert (Hlim : Zlength (mt_lim (ms_core (msolver_resume_pending M0))) = 0)
    by exact (proj1 (proj2 PreH1)).
  assert (Hcap0 : ms_cap (msolver_resume_pending M0) = ms_cap M0)
    by apply msolver_resume_pending_size_cap__api_reentry.
  unfold solver_propagate_post.
  rewrite !orp_sepcon_right_equiv.
  repeat apply derivable1_orp_elim.
  - Intros Mdone.
    match goal with
    | H : solver_propagation_inv _ _ _ _ _ /\ _ |- _ =>
        destruct H as (Hinv & Hcaller & Hreuse & Hseed & Hdrain)
    end.
    unfold propagation_caller_frame in Hcaller.
    destruct Hcaller as (Hlim' & _ & _ & _ & Hc).
    assert (Hready : solver_query_ready n F Mdone).
    { unfold solver_query_ready. split; [|split; [|split]].
      - exact (solver_propagation_drained_assuming_strong n F nil nil Mdone Hinv Hdrain).
      - rewrite Hlim'. exact Hlim.
      - exact Hdrain.
      - exact (proj1 Hinv). }
    assert (Hreuse' : solver_query_reuse M0 Mdone).
    { intros _. exact ((proj1 Hreuse) Hbc). }
    assert (Hcap : ms_cap Mdone = ms_cap M0) by (rewrite Hc; exact Hcap0).
    Exists Mdone.
    sep_apply (solver_rep_assigns_levels_at_rep
      s Mdone assigns_prop levels_entry solve_wl).
    repeat sep_apply store_int_undef_store_int.
    repeat sep_apply store_ptr_undef_store_ptr.
    entailer_with ltac:(int_auto).
  - Intros Mconf p focus C. entailer_with ltac:(lia).
  - unfold solver_propagation_capacity_raw. Intros Mcap. entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_7 : solver_solve_which_implies_wit_7.
Proof.
  Unfold. left; intros.
  rename Mdrained into Md.
  unfold solver_rep_wl, solver_rep_levels_wl_at, solver_cancel_owned.
  Intros lvl act asg opos rsn trl tgs.
  Exists lvl asg.
  unfold solver_solve_entry_rest_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_vecs_rep,
    solver_vecs_without_clauses_rep, db_words.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma helper_of_solver_solve_which_implies_wit_8_split_goal_spatial :
  solver_solve_which_implies_wit_8_split_goal_spatial.
Proof.
  unfold solver_solve_which_implies_wit_8_split_goal_spatial. intros.
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_solve_entry_rest_at, solver_without_assigns_frame_wl_at,
    solver_without_assigns_cells_at, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_vecs_rep,
    solver_vecs_without_clauses_rep, db_words.
  Intros act opos rsn trl tgs.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_8 : solver_solve_which_implies_wit_8.
Proof.
  left. exact helper_of_solver_solve_which_implies_wit_8_split_goal_spatial.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_9 : solver_solve_which_implies_wit_9.
Proof.
  unfold solver_solve_which_implies_wit_9.
  intros A_arr F n solve_wl_solver_solve_spec M0
    levels_ptr endvar begin values s.
  intros.
  bind_fact ( solver_query_ready n F M0 ) as Hquery.
  destruct Hquery as [Hbase [Hlim [Hqhead Hpending]]].
  pose proof (msas_weak Hbase) as Hinv.
  pose proof (msa_shape Hinv) as Hshape.
  unfold assumptions_array.
  Intros raw.
  lazymatch goal with
  | Harray : endvar = _ /\ A_arr = lits_denote raw /\ _ |- _ =>
      destruct Harray as [Hend [HA [Hrawwf Hempty]]]
  end.
  assert (HAwf : Forall (literal_wf n) A_arr).
  { rewrite HA. apply lits_denote_wf. exact Hrawwf. }
  pose proof (solver_query_assumptions__solve n F M0 A_arr Hbase HAwf) as Hstrong.
  assert (Hprefix : A_arr = assumption_prefix raw (Zlength raw)).
  { unfold assumption_prefix.
    rewrite (sublist_self raw (Zlength raw) eq_refl).
    exact HA. }
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_assigns_focus_frame_wl_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  destruct raw as [|z raw'].
  - assert (Hvalid : valid_int_position begin).
    { apply Hempty. reflexivity. }
    Right. Exists (@nil Z) act opos rsn trl tgs.
    pose proof (msa_size Hinv) as Hsize.
    subst n.
    unfold solver_shape in Hshape.
    unfold solver_scalars_rep, solver_vecs_rep.
    msat_manual_entailer_with ltac:(lia).
  - Left. Exists (z :: raw') act opos rsn trl tgs.
    entailer_with ltac:(lia);
      try discriminate;
      rewrite (msa_size Hinv);
      unfold solver_shape in Hshape;
      entailer_with ltac:(lia);
      unfold solver_scalars_rep, solver_vecs_rep;
      entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_10 : solver_solve_which_implies_wit_10.
Proof.
  left. intros n raw k i begin endvar; intros.
  bind_fact ( i = begin + k * sizeof ( INT ) ) as H_i.
  bind_fact ( endvar = begin + Zlength raw * sizeof ( INT ) ) as H_endvar.
  bind_fact ( Forall (lit_wf_c n) raw ) as H_Forall.
  assert (Hklt : k < Zlength raw).
  { rewrite sizeof_int in H_i, H_endvar. lia. }
  assert (Hlit : lit_wf_c n (Znth k raw 0)).
  { apply (Forall_Znth_elim Z (lit_wf_c n) raw 0 k H_Forall). lia. }
  assert (Hvar : 0 <= lit_var_c (Znth k raw 0) < n).
  { apply lit_var_c_in_range. exact Hlit. }
  unfold lit_wf_c in Hlit.
  replace (k - 0) with k by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_11 : solver_solve_which_implies_wit_11.
Proof.
  left. intros A_arr F n raw M0 k assumption_status; intros.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) M0 ) as H_msolver_inv_assuming_strong.
  bind_fact ( A_arr = assumption_prefix raw (Zlength raw) ) as H_A_arr.
  bind_fact ( Forall (lit_wf_c n) raw ) as H_Forall.
  bind_fact ( Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core M0)) 0 = 1 - 2 * lit_sign_c (Znth k raw 0) ) as
      H_Znth.
  set (current := Znth k raw 0).
  assert (Hlit : lit_wf_c n current).
  { unfold current. apply (Forall_Znth_elim Z (lit_wf_c n) raw 0 k H_Forall).
    lia. }
  assert (Hlit0 : 0 <= current) by (unfold lit_wf_c in Hlit; lia).
  assert (Hvr : 0 <= lit_var_c current < n).
  { apply lit_var_c_in_range. exact Hlit. }
  assert (Hprefix : assumption_prefix raw (k + 1) =
      assumption_prefix raw k ++ (lit_denote current :: nil)).
  { unfold assumption_prefix, current.
    rewrite (sublist_split 0 (k + 1) k raw) by lia.
    rewrite (sublist_single 0 k raw) by lia.
    rewrite lits_denote_app. reflexivity. }
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hold.
  pose proof (msa_trail_wf Hold) as Htrailwf.
  assert (Hcell : Znth (lit_var_c current)
      (mt_assigns (ms_core M0)) 0 = lit_sig current).
  { unfold current in *.
    rewrite H_Znth.
    unfold lit_sig, lit_sign_c.
    destruct (Z.odd (Znth k raw 0)); reflexivity. }
  assert (Htrue : assump_true_at_root (ms_core M0)
      (Zlength (mt_lim (ms_core M0))) (lit_denote current)).
  { unfold assump_true_at_root. split.
    - unfold eval_partial_literal.
      rewrite mt_pv_nonneg by (rewrite lit_var_c_denote; lia).
      apply (proj1 (lit_true_iff (mt_assigns (ms_core M0)) current Hlit0)).
      exact Hcell.
    - assert (Hassigned : Znth (lit_var_c current)
          (mt_assigns (ms_core M0)) 0 <> 0).
      { rewrite Hcell. apply lit_sig_nonzero. }
      pose proof (proj1 (mtw_assigned_iff Htrailwf
        (lit_var_c current) Hvr) Hassigned) as Hin.
      destruct (In_Znth_index
        (map lit_var_c (mt_trail (ms_core M0)))
        (lit_var_c current) Hin) as [j [Hj Hmap]].
      rewrite Zlength_map_Z in Hj.
      assert (Htrailvar : trail_var (ms_core M0) j = lit_var_c current).
      { unfold trail_var.
        rewrite <- (Znth_map Z Z lit_var_c
          (mt_trail (ms_core M0)) j 0 0 Hj).
        exact Hmap. }
      pose proof (mtw_levels_agree Htrailwf j Hj) as Hagree.
      rewrite lit_var_c_denote.
      rewrite <- Htrailvar.
      rewrite Hagree.
      apply prop_level_processed_level_le. }
  assert (Hnew : msolver_inv_assuming n F A_arr
      (assumption_prefix raw (k + 1)) M0).
  { constructor.
    - exact (msa_size Hold).
    - exact (msa_n_range Hold).
    - exact (msa_shape Hold).
    - exact (msa_F_wf Hold).
    - exact (msa_A_wf Hold).
    - exact Htrailwf.
    - exact (msa_level_bound Hold).
    - destruct (msa_decisions Hold) as [A_inst [Hdec Hincl]].
      exists A_inst. split; [exact Hdec|].
      intros x Hx. rewrite Hprefix. apply in_or_app. left.
      apply Hincl. exact Hx.
    - rewrite Hprefix. intros x Hx. apply in_app_or in Hx.
      destruct Hx as [Hx | Hx].
      + apply (msa_proc_incl Hold). exact Hx.
      + simpl in Hx. destruct Hx as [<- | Hcontra]; [|contradiction].
        rewrite H_A_arr. unfold assumption_prefix.
        rewrite (sublist_self raw (Zlength raw) eq_refl).
        apply lits_denote_in. apply Znth_In. lia.
    - rewrite Hprefix. apply Forall_app. split.
      + exact (msa_proc_sat Hold).
      + constructor; [exact Htrue | constructor].
    - exact (msa_stable Hold).
    - exact (msa_reasons_ent Hold).
    - exact (msa_reasons_inj Hold).
    - exact (msa_trail_impl Hold).
    - exact (msa_db_wf Hold).
    - exact (msa_db_matches Hold).
    - exact (msa_db_implied Hold).
    - exact (msa_db_complete Hold).
    - exact (msa_learnt_db Hold).
    - exact (msa_prob_db Hold).
    - exact (msa_binary_out Hold).
    - exact (msa_reasons_mem Hold).
    - exact (msa_reason_head Hold).
    - exact (msa_reason_bin Hold).
    - exact (msa_wmap_exact Hold).
    - exact (msa_tags_clear Hold).
    - exact (msa_heap_wf Hold).
    - exact (msa_cla_inc_nonnegative Hold).
    - exact (msa_seed Hold). }
  assert (Hstrong : msolver_inv_assuming_strong n F A_arr
      (assumption_prefix raw (k + 1)) M0).
  { constructor.
    - exact Hnew.
    - exact (msas_prop_level H_msolver_inv_assuming_strong).
    - exact (msas_watch_frontier H_msolver_inv_assuming_strong).
    - exact (msas_heap_covers H_msolver_inv_assuming_strong).
    - exact (msas_reasonless_current H_msolver_inv_assuming_strong). }
  unfold assumption_true_advance.
  subst assumption_status.
  sep_apply store_char_undef_store_char.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== sort which_implies wits (2 proofs) ===== *)
Lemma proof_of_sort_which_implies_wit_1 : sort_which_implies_wit_1.
Proof.
  Unfold.
  left. intros.
  bind_fact ( learnt_sort_domain db_sort_spec origin_sort_spec ) as H_learnt_sort_domain.
  unfold learnt_sort_domain in H_learnt_sort_domain.
  destruct H_learnt_sort_domain as [Hlearnt Hperm].
  sep_apply
    (clause_db_rep_learnt_to_sort__sortrnd db_sort_spec Hlearnt).
  Intros activities.
  assert (Hsegment :
      learnt_sort_segment_domain db_sort_spec origin_sort_spec).
  { unfold learnt_sort_segment_domain.
    rewrite Forall_forall. intros p Hp.
    eapply Permutation_in; [exact Hperm|exact Hp]. }
  Exists activities.
  unfold learnt_sort_context.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sort_which_implies_wit_2 : sort_which_implies_wit_2.
Proof.
  Unfold.
  left. intros.
  sep_apply_l_atomic
    (learnt_sort_rep_to_clause_db__sortrnd db_sort_spec activities).
  sep_apply store_double_undef_store_double.
  Exists current_2. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== sortrnd which_implies wits (2 proofs) ===== *)
Lemma proof_of_sortrnd_which_implies_wit_3 : sortrnd_which_implies_wit_3.
Proof.
  Unfold.
  left. intros.
  rewrite (PtrArray.seg_0_shift array i size right_after).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_sortrnd_which_implies_wit_4 : sortrnd_which_implies_wit_4.
Proof.
  Unfold.
  left. intros.
  bind_fact ( sortrnd_split srt_db srt_origin current left right size i ) as H_sortrnd_split.
  bind_fact ( Permutation left left_after ) as H_Permutation.
  bind_fact ( Permutation right right_after ) as H_Permutation_2.
  unfold sortrnd_split in H_sortrnd_split.
  destruct H_sortrnd_split as
    [Horigin [Hcurrent [Hcut [Happ [Hleft [Hright [Hleftdom Hrightdom]]]]]]].
  pose proof (Zlength_perm_eq _ _ _ H_Permutation) as Hleft_after.
  pose proof (Zlength_perm_eq _ _ _ H_Permutation_2) as Hright_after.
  assert (Hlen : Zlength (left_after ++ right_after) = size).
  { rewrite Zlength_app. lia. }
  assert (Hperm : Permutation srt_origin (left_after ++ right_after)).
  { eapply Permutation_trans; [exact Horigin|].
    rewrite Happ. apply Permutation_app; assumption. }
  sep_apply_l_atomic
    (PtrArray.seg_merge_to_seg array 0 i size left_after right_after).
  - dump_pre_spatial. lia.
  - Exists (left_after ++ right_after). msat_manual_entailer_with ltac:(lia).
Qed.
