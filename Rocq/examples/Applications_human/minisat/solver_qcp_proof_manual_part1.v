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

(* This part covers ten C functions, in file order: clause_simplify,
   enqueue, solver_analyze, solver_canceluntil_capacity, solver_canceluntil,
   solver_propagate, solver_record, solver_search, solver_simplify,
   solver_solve.  Each family is marked below by a banner comment naming the
   function and its proof count.  Part-local helper lemmas and
   tactics used across those families sit ahead of the
   first VC proof; see the comment above each one for what it captures.
   Every `Lemma proof_of_*` below proves exactly one VC from
   solver_qcp_goal.v -- do not add new lemmas here without a matching
   goal.v entry. *)

(* The six `solver_solve` assumption-check obligations below share one script:
   the caller picks the disjunct, then this closes it -- normalise the `- 0`
   index spellings the array reads introduce, project `mtrail_wf` out of the
   assuming invariant, and finish on the fact that an `lbool` cell survives an
   8-bit sign truncation.  `E` is the cell expression the goal truncates (the
   raw cell, or its negation when the literal is negative); `r1`/`r2` are the
   two `retval` names.  Hypotheses are re-found by shape rather than named,
   because a name introduced inside a `match goal` branch is not in scope for
   the rest of an Ltac body. *)
Ltac msat_solve_lit_assign_bounds_p1 r1 r2 k raw M E :=
  entailer_with lia;
  replace (k - 0) with k in * by lia;
  subst r1; try subst r2;
  replace (lit_var_c (Znth k raw 0) - 0)
    with (lit_var_c (Znth k raw 0)) in * by lia;
  assert (Hcell :
    lbool_cell (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core M)) 0))
    by (eapply Forall_Znth_elim;
        [ match goal with
          | Hinv : msolver_inv_assuming_strong _ _ _ _ _ |- _ =>
              exact (mtw_cells (msa_trail_wf (msas_weak Hinv)))
          end
        | match goal with
          | Hlen : Zlength (mt_assigns (ms_core _)) = _ |- _ => rewrite Hlen
          end; lia ]);
  assert (Hnorm : signed_last_nbits E 8 = E)
    by (apply signed_last_nbits_eq; [lia|];
        unfold lbool_cell in Hcell;
        destruct Hcell as [Hc | [Hc | Hc]]; lia);
  unfold lit_sign_c in *; destruct (Z.odd (Znth k raw 0)); lia.

(* The four `solver_search` backjump obligations differ only in their VC
   statement: each pulls `ms_model Mback = nil` out of the backjump-ready
   bundle and the loop's own `ms_model Mcur = nil`. *)
Ltac msat_search_backjump_model_nil_p1 n F A_arr A_inst Mcur Mback words :=
  let Hready := fresh "H_solver_search_backjump_ready" in
  let Hmodel0 := fresh "H_ms_model" in
  ( bind_fact ( solver_search_backjump_ready n F A_arr A_inst Mcur Mback words )
      as Hready;
    bind_fact ( ms_model Mcur = nil ) as Hmodel0;
    destruct Hready as [_ [_ [_ [_ [_ [_ [Hmodel _]]]]]]];
    assert (Hback_nil : ms_model Mback = (@nil Z))
      by (rewrite Hmodel; exact Hmodel0);
    entailer_with ltac:(lia) ).

(* Both arms of solver_canceluntil_capacity_entail_wit_1 (stable / assuming K)
   share this tail once the arm has projected shape/size/heap_wf out of its own
   weak invariant: seed the reinsertion loop invariant at the trail tail and
   republish the order vector. *)
Ltac msat_capacity_reinsert_arm_tail_p1 Hshape Hheap_wf n M0 order_p retval_2 :=
  unfold solver_shape in Hshape;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst n;
  unfold msolver_heap in Hheap_wf;
  assert (Hinit : cancel_reinserted
    (heap_of_lists (ms_order M0) (ms_orderpos M0))
    (mt_trail (ms_core M0)) (ms_qtail M0 - 1 + 1) (ms_qtail M0))
    by (replace (ms_qtail M0 - 1 + 1) with (ms_qtail M0) by lia;
        apply cancel_reinserted_init);
  assert (Hinv : capacity_reinsert_loop_inv M0 0
    (ms_qtail M0 - 1) (ms_order_cap M0)
    (ms_order M0) (ms_orderpos M0))
    by (unfold capacity_reinsert_loop_inv;
        entailer_with ltac:(lia); apply incl_refl);
  Exists (ms_order_cap M0) (ms_order M0) (ms_orderpos M0);
  unfold veci_rep; Exists order_p retval_2;
  unfold veci_rep_at;
  entailer_with ltac:(lia);
    unfold veci_size_addr, veci_cap_addr, veci_ptr_addr; csimpl;
    entailer_with ltac:(lia).

(* solver_analyze_entail_wit_12_15_learnt and _12_16_learnt carry byte-identical
   proof bodies: once the witness list is in place both show that the literal at
   index `j` is false at a level below the current one, so it joins neither the
   seen set nor the learnt prefix.  The body is split in two because the shipped
   text runs its head on the first goal only and everything after `intuition`
   under `all:`; the two closing bullets stay at each call site, where they name
   hypotheses these tactics introduce. *)
Ltac msat_analyze_scan_stop_head_p1 phase j Ccur clause_words2 :=
  unfold analyze_clause_scan_inv in *;
  subst phase;
  cbn in *;
  replace (j - 0) with j in * by lia;
  assert (HClen : Zlength Ccur = Zlength clause_words2)
    by (match goal with
    | HCwords : Ccur = lits_denote clause_words2 |- _ =>
        rewrite HCwords, lits_denote_length
    end; reflexivity);
  intuition (try lia; try congruence).

(* The tail of that pair: it derives the level and prefix facts for index
   `j` and leaves the two start-set goals the call site closes. *)
Ltac msat_analyze_scan_stop_facts_p1 j Ccur clause_words2 anz_n Mscan_2 K Mact :=
  let Hequiv := fresh "Hequiv" in
  let Hfalse := fresh "Hfalse" in
  let k := fresh "k" in
  let Hpos := fresh "Hpos" in
  let Hdypos := fresh "Hdypos" in
  (  assert (Hrootnonneg : 0 <= ms_root_level Mscan_2) by
    (let Hready := fresh "Hready" in
     match goal with
     | Hready0 : analysis_cancel_ready _ _ _ _ ?Ms _
       |- 0 <= ms_root_level ?Ms =>
         pose proof Hready0 as Hready
     end;
     destruct Hready as [Mready [Hcancel [Hequiv _]]];
     destruct Hcancel as [Hweak _]; destruct Hweak as [_ Hinv];
     assert (Hrootready : 0 <= ms_root_level Mready) by
       (destruct K;
        [pose proof (msw_shape Hinv)
        |pose proof (msa_shape Hinv)];
        match goal with
        | Hshape0 : solver_shape _ |- _ => unfold solver_shape in Hshape0
        end; tauto);
     unfold analysis_core_equiv in Hequiv;
     destruct Hequiv as [_ [_ [_ [_ [Eroot _]]]]];
     rewrite Eroot; exact Hrootready);
  assert (Hwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption);
  assert (HqIn : In (Znth j Ccur (Pos 0)) Ccur) by
    (apply Znth_In; lia);
  assert (Hqnth :
    Znth j Ccur (Pos 0) = lit_denote (Znth j clause_words2 0)) by
    (match goal with
     | HCwords : ?C = lits_denote ?words
       |- Znth ?idx ?C (Pos 0) = lit_denote (Znth ?idx ?words 0) =>
         rewrite HCwords; unfold lits_denote; apply Znth_map; lia
     end);
  match goal with
  | Hequiv0 : analysis_core_equiv ?Ma ?Ms,
    Hcert0 : propagation_conflict_cert _ _ ?Ma _ |- _ =>
      pose proof Hequiv0 as Hequiv;
      destruct Hcert0 as [_ [Hfalse _]]
  end;
  unfold analysis_core_equiv in Hequiv;
  destruct Hequiv as [_ [_ [_ [Ecore _]]]];
  rewrite <- Ecore in Hfalse;
  assert (Hqnonneg :
    0 <= literal_var (Znth j Ccur (Pos 0))) by
    (match goal with
     | HwfC : Forall (literal_wf ?nv) ?C,
       Hin : In (Znth ?idx ?C (Pos 0)) ?C |- _ =>
         rewrite Forall_forall in HwfC;
         pose proof (HwfC _ Hin) as Hlitwf;
         unfold literal_wf, var_in_range in Hlitwf; lia
     end);
  assert (Hqfalse :
    eval_partial_literal (assignment (msolver_view anz_n Mscan_2))
      (Znth j Ccur (Pos 0)) = Some false) by
    (rewrite msolver_view_assignment;
     pose proof (Hfalse _ HqIn) as Hqfalse_raw;
     unfold eval_partial_literal in Hqfalse_raw |- *;
     rewrite mt_pv_nonneg by exact Hqnonneg;
     unfold assigns_pv, assigns_val in Hqfalse_raw;
     exact Hqfalse_raw);
  destruct (eval_partial_false_shape _ _ Hqfalse) as
    [b [Hqassign Hqshape]];
  rewrite msolver_view_assignment in Hqassign;
  destruct (trail_pos (ms_core Mscan_2)
    (literal_var (Znth j Ccur (Pos 0)))) as [k|] eqn:Hpos;
  try (match goal with
    | Hpos0 : trail_pos ?t ?v = None,
      Hwf0 : mtrail_wf ?nv ?t,
      Hassign0 : mt_pv ?t ?v = Some ?b |- _ =>
        exfalso;
        pose proof (proj2 (view_unassigned_iff nv t v Hwf0) Hpos0)
          as Hunassigned;
        congruence
    end);
  assert (Hqlevel :
    level_of (msolver_view anz_n Mscan_2)
      (literal_var (Znth j Ccur (Pos 0))) =
      Some (level_of_index (ms_core Mscan_2) (Z.of_nat k))) by
    (cbn [msolver_view view_of level_of]; rewrite Hpos; reflexivity);
  assert (Hqcell :
    Znth (literal_var (Znth j Ccur (Pos 0)))
      (mt_levels (ms_core Mscan_2)) 0 =
      level_of_index (ms_core Mscan_2) (Z.of_nat k)) by
    (rewrite <- (trail_pos_var _ _ _ Hpos);
     apply (mtw_levels_agree Hwf);
     split; [lia|exact (trail_pos_bound _ _ _ Hpos)]);
  assert (Hqraw :
    Znth (literal_var (Znth j Ccur (Pos 0)))
      (mt_levels (ms_core Mscan_2)) 0 <= 0) by
    (rewrite Hqnth, lit_var_c_denote;
     match goal with
     | Hraw0 : Znth (?rv - 0) ?levels 0 <= 0,
       Heq0 : ?rv = lit_var_c ?word
       |- Znth (lit_var_c ?word) ?levels 0 <= 0 =>
         rewrite <- Heq0;
         replace rv with (rv - 0) by lia;
         exact Hraw0
     end);
  rewrite Hqcell in Hqraw;
  assert (Hat : at_current_level_b (msolver_view anz_n Mact)
    (Znth j Ccur (Pos 0)) = false) by
    (unfold at_current_level_b;
     cbn [msolver_view view_of level_of current_level];
     rewrite <- Ecore, Hpos; cbn [option_map];
     apply Z.eqb_neq; lia);
  assert (Hbelow : below_current_b (msolver_view anz_n Mact)
    (Znth j Ccur (Pos 0)) = false) by
    (unfold below_current_b;
     cbn [msolver_view view_of level_of current_level];
     rewrite <- Ecore, Hpos; cbn [option_map];
     destruct (Z.ltb 0
       (level_of_index (ms_core Mscan_2) (Z.of_nat k))) eqn:Hdypos;
     [apply Z.ltb_lt in Hdypos; lia|reflexivity]);
  assert (Hprefix :
    sublist 0 (j + 1) Ccur =
      sublist 0 j Ccur ++ (Znth j Ccur (Pos 0) :: nil)) by
    (rewrite (sublist_split 0 (j + 1) j Ccur) by lia;
     f_equal; apply sublist_single; lia);
  change (firstn (Z.to_nat (j + 1)) Ccur =
    firstn (Z.to_nat j) Ccur ++ (Znth j Ccur (Pos 0) :: nil)) in Hprefix).

(* Refold the veci handle the solver_search capacity side conditions open; the
   member supplies its own [Intros] names and closing entailer. *)
Ltac msat_search_veci_bounds_open_p1 :=
  Unfold; left; intros; unfold veci_rep, veci_rep_at.

(* Mirror of proof_common's [msat_search_close_learnts_db_vec_bounds] for the
   `right` arm of the same solver_search capacity checks: there the four pure
   conjuncts arrive in the opposite order, innermost the size bound and
   outermost the maximum.  [H] is the conjunction [coq_prop_lift] leaves. *)
Ltac msat_search_close_vec_bounds_rev_p1 H :=
  destruct H as [[Hlen Hcap] [Hpos Hmax]];
  eapply derivable1s_coq_prop_andp_r;
  [ eapply derivable1s_coq_prop_andp_r;
  [ eapply derivable1s_coq_prop_andp_r;
  [ apply (derivable1s_coq_prop_r _); exact Hlen
  | exact Hcap ]
  | exact Hpos ]
  | exact Hmax ].

(* Open the vecp handle the solver_simplify capacity side conditions carry. *)
Ltac msat_simplify_db_words_bounds_p1 :=
  Unfold; left; intros; unfold vecp_rep; Intros p; unfold vecp_rep_at;
  entailer_with lia.

(* The goal states the capacity bounds over `db_words (solver_selected_db ...)`
   while the vector representation predicate has just supplied them under the
   logical name.  Rewriting the defining equation backwards folds the name in,
   so lia sees one term instead of two unrelated ones. *)
Ltac msat_simplify_db_words_fold_p1 :=
  match goal with
  | Hw : ?w = db_words (solver_selected_db _ _) |- _ => rewrite <- Hw
  end; lia.

(* The facts the two model-copy progress obligations share: the solver size and
   the literal bound, read off the model-ready invariant.  The five arguments
   are the specification names the caller's own opener introduces. *)
Ltac msat_search_model_copy_bounds_p1 n F A_arr A_inst Mselected :=
  let Hready := fresh "H_solver_search_model_ready" in
  let Hinv := fresh "Hinv" in
  let Hn := fresh "Hn" in
  let Hsize := fresh "Hsize" in
  let Hshape := fresh "Hshape" in
  let Hbound := fresh "Hbound" in
  bind_fact ( solver_search_model_ready n F A_arr A_inst Mselected ) as Hready;
  unfold solver_search_model_ready in Hready;
  destruct Hready as (Hinv & _ & _ & _ & _ & _);
  assert (Hn : 0 <= n) by exact (msi_n_range Hinv);
  assert (Hsize : ms_size Mselected = n) by (symmetry; exact (msi_size Hinv));
  assert (Hshape : 2 * n <= INT_MAX) by
    (pose proof
       (msolver_inv_literal_bound n F A_arr A_inst Mselected (msi_weak Hinv))
       as Hbound;
     rewrite Hsize in Hbound;
     exact Hbound);
  try (unfold model_copy_progress; simpl; lia);
  try lia;
  try (dump_pre_spatial; exact Hshape);
  try exact Hn;
  try exact Hshape;
  try exact Hsize;
  try assumption;
  try (unfold model_copy_progress; simpl; repeat split; try lia; reflexivity).

(* The enqueue literal-range side conditions: read the bound off enqueue_input.
   The arguments are the names the caller's own opener introduces. *)
Ltac msat_enqueue_input_lit_bound_p1 n l0 qtail asgl lvls rsns trail lpre :=
  let Hin := fresh "H_enqueue_input" in
  let Hlit := fresh "Hlit" in
  bind_fact ( enqueue_input n l0 qtail asgl lvls rsns trail ) as Hin;
  unfold enqueue_input, lit_wf_c in Hin;
  destruct Hin as (Hlit & _);
  subst lpre;
  dump_pre_spatial; lia.

(* The spatial frame both arms of an enqueue onto an already-assigned variable
   share: hand back the unchanged trail state and give the three local C
   variables back as undefined stores. *)
Ltac msat_enqueue_assign_frame_p1 qtail asgl lvls rsns trail rsnp trlp asgp n
    l0 lpre Hsig Heq :=
  unfold enqueue_post_at, enqueue_state_at, enqueue_transition;
  Exists qtail asgl lvls rsns trail rsnp trlp;
  rewrite Hsig in Heq;
  sep_apply_l_atomic (CharArray.full_to_seg asgp n asgl);
  sep_apply_l_atomic
    (store_int_undef_store_int (&( "v")) (lit_var_c l0));
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "values")) asgp);
  sep_apply_l_atomic (store_int_undef_store_int (&( "l")) lpre);
  split_pure_spatial;
  [ entailer_with ltac:(lia) | entailer_with ltac:(lia) ].

(* Enqueue of a literal whose variable already carries a value: [s] is the sign
   the literal denotes, and the arm taken depends on whether that value agrees
   with it.  The remaining arguments are the names the caller's opener
   introduces. *)
Ltac msat_enqueue_assign_keep_close_p1 s rv lpre l0 asgl qtail lvls rsns trail
    rsnp trlp asgp n :=
  let Hrv := fresh "H_retval_2" in
  let Hsig := fresh "Hsig" in
  let Heq := fresh "Heq" in
  bind_fact ( rv = lit_sign_c lpre ) as Hrv;
  rewrite replace_Znth_Znth in *;
  assert (Hsig : lit_sig l0 = s)
    by (subst lpre; unfold lit_sign_c in Hrv; unfold lit_sig;
        destruct (Z.odd l0); lia);
  destruct (Z.eq_dec (Znth (lit_var_c l0) asgl 0) (lit_sig l0)) as [Heq | Heq];
  [ Left;
    msat_enqueue_assign_frame_p1 qtail asgl lvls rsns trail rsnp trlp asgp n l0
      lpre Hsig Heq;
    left
  | Right;
    msat_enqueue_assign_frame_p1 qtail asgl lvls rsns trail rsnp trlp asgp n l0
      lpre Hsig Heq;
    right; left ];
  repeat split; auto; lia.

(* Enqueue of a literal whose variable is still unassigned: [s] is the sign the
   literal denotes, which is written into the assignment array while the level
   and reason arrays record the new decision.  The remaining arguments are the
   names the caller's opener introduces. *)
Ltac msat_enqueue_assign_bump_close_p1 s rv lpre rv3 l0 asgl qtail lvls rsns
    trail rsnp trlp asgp lvlp n lim reasonp :=
  let Hrv := fresh "H_retval_2" in
  let Hsig := fresh "Hsig" in
  bind_fact ( rv = lit_sign_c lpre ) as Hrv;
  rewrite replace_Znth_Znth in *;
  subst lpre; subst rv3;
  assert (Hsig : lit_sig l0 = s)
    by (unfold lit_sign_c in Hrv; unfold lit_sig; destruct (Z.odd l0); lia);
  rewrite !replace_Znth_replace_Znth_Same by lia;
  unfold enqueue_post_at, enqueue_state_at, enqueue_transition;
  Exists (qtail + 1)
    (replace_Znth (lit_var_c l0) (lit_sig l0) asgl)
    (replace_Znth (lit_var_c l0) (Zlength lim) lvls)
    (replace_Znth (lit_var_c l0) reasonp rsns)
    (trail ++ l0 :: nil) rsnp trlp;
  rewrite Hsig;
  sep_apply_l_atomic
    (CharArray.full_to_seg asgp n (replace_Znth (lit_var_c l0) s asgl));
  sep_apply_l_atomic
    (IntArray.full_to_seg lvlp n
       (replace_Znth (lit_var_c l0) (Zlength lim) lvls));
  sep_apply_l_atomic
    (PtrArray.full_to_seg rsnp n
       (replace_Znth (lit_var_c l0) reasonp rsns));
  split_pure_spatial;
  [ entailer_with ltac:(lia)
  | entailer_with ltac:(lia);
    try (rewrite Zlength_replace_Znth; lia);
    try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
    right; right; repeat split; auto ].

(* The whole body of the two analyze scan-stop obligations: hand back the twelve
   loop witnesses, then show the literal at index [j] joins neither the seen set
   nor the learnt prefix, so both filters collapse to the untouched prefix.  The
   three hypotheses the facts tactic asserts are re-found by shape. *)
Ltac msat_analyze_scan_stop_p1 cap opos act S0 R0 learnt0 x Sscan Rscan learnt
    words M phase j Ccur cw anz K Mact :=
  Right;
  Exists cap act opos S0 R0 learnt0 x Sscan Rscan learnt words M;
  entailer_with ltac:(lia);
  msat_analyze_scan_stop_head_p1 phase j Ccur cw;
  msat_analyze_scan_stop_facts_p1 j Ccur cw anz M K Mact;
  [ unfold analyze_start_S in *;
    match goal with
    | Hp : firstn _ _ = firstn _ _ ++ _ |- _ => rewrite Hp in *
    end;
    rewrite filter_app in *; cbn [filter];
    match goal with
    | Ha : at_current_level_b _ _ = false |- _ => rewrite Ha in *
    end;
    cbn in *; rewrite app_nil_r in *; congruence
  | unfold analyze_start_learnt in *;
    match goal with
    | Hp : firstn _ _ = firstn _ _ ++ _ |- _ => rewrite Hp in *
    end;
    rewrite filter_app in *; cbn [filter];
    match goal with
    | Hb : below_current_b _ _ = false |- _ => rewrite Hb in *
    end;
    cbn in *; rewrite app_nil_r in *; congruence ].

(* Refold the five cells of a `vecp_t` back into `vecp_rep`.  `vecp_rep_at` is
   spelled through `vecp_size_addr` and friends, so the raw cells the simplify
   compaction leaves behind do not match it syntactically. *)
Lemma msat_vecp_cells_rep : forall v p l cap,
  0 <= Zlength l <= cap -> 0 < cap <= INT_MAX ->
  &( v # "vecp_t" ->ₛ "size") # Int |-> Zlength l **
  &( v # "vecp_t" ->ₛ "cap") # Int |-> cap **
  &( v # "vecp_t" ->ₛ "ptr") # Ptr |-> p **
  PtrArray.seg p 0 (Zlength l) l **
  PtrArray.undef_seg p (Zlength l) cap
  |-- vecp_rep v l cap.
Proof.
  intros v p l cap Hlen Hcap.
  unfold vecp_rep, vecp_rep_at, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  Exists p. msat_manual_entailer_with lia.
Qed.

(* The learnt-side mirror of lib's
   [solver_rep_reasons_simplify_close_0__simplify], which is stated
   for the problem database (type 0) only.  Both simplify disjuncts need the
   same close direction, and lib supplies only the problem-side one. *)
Lemma msat_simplify_close_learnt :
  forall s M reasons lvl wl asg,
  mt_lim (ms_core M) = (@nil Z) ->
  solver_shape M ->
  vecp_rep (solver_selected_vec s 1)
    (db_words (solver_selected_db 1 M)) (solver_selected_cap 1 M) **
  clause_db_rep (solver_selected_db 1 M) **
  &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  veci_rep &(s # "solver_t" ->ₛ "trail_lim") (@nil Z) (ms_lim_cap M) **
  solver_simplify_db_rest_at s 1 M reasons lvl wl asg
  |-- solver_rep_reasons_levels_wl_at s M reasons lvl wl.
Proof.
  intros s M reasons lvl wl asg Hlim Hshape.
  unfold solver_rep_reasons_levels_wl_at.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_db_rest_at,
    solver_simplify_clause_frame_at, solver_selected_vec, solver_selected_db,
    solver_selected_cap, solver_other_db_vec_rep, solver_other_clause_db_rep,
    solver_wlists_handle, solver_scalars_rep, clause_new_scalars_frame,
    solver_vecs_rep, solver_trail_array_rep, solver_levels_slice_at, db_words.
  Intros act opos trl tgs.
  Exists act asg opos trl tgs.
  cbn. rewrite Hlim. msat_manual_entailer_with lia.
Qed.

(* The facts every `solver_analyze` scan obligation reads off the analysis
   entry bundle: the trail is well-formed, its view is stable, every trail
   literal is implied by the formula, the queue tail is the trail length, and
   a variable assigned at decision level 0 is entailed by the formula as a
   unit clause.  The first four are the three `analysis_cancel_ready` lemmas
   of solver_qcp_lib.v; the fifth is proved here once instead of inline in
   each scan proof. *)
Lemma msat_analysis_ready_scan_facts_p1 :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    stable_view (msolver_view n M) /\
    trail_implied F (ms_core M) /\
    ms_qtail M = Zlength (mt_trail (ms_core M)) /\
    (forall v b,
       assignment (msolver_view n M) v = Some b ->
       level_of (msolver_view n M) v = Some 0 ->
       entails_clause F (satisfying_literal v b :: nil)).
Proof.
  intros n F A_arr K M focus Hready.
  destruct (analysis_cancel_ready_weak_facts__analyze
    n F A_arr K M focus Hready) as (_ & _ & _ & Hwf & _ & _ & Htrailimpl).
  pose proof (analysis_cancel_ready_qtail_eq__analyze
    n F A_arr K M focus Hready) as Hqtail.
  assert (Hstable : stable_view (msolver_view n M)).
  { destruct Hready as [M0 [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak _]. destruct Hweak as [_ Hinv].
    rewrite (analysis_core_equiv_view__analyze n M0 M Hequiv).
    destruct K; [exact (msw_stable Hinv)|exact (msa_stable Hinv)]. }
  split; [exact Hwf|].
  split; [exact Hstable|].
  split; [exact Htrailimpl|].
  split; [symmetry; exact Hqtail|].
  intros v b Hass Hlev.
  destruct Hstable as [Hgrounded _].
  destruct (Hgrounded v b Hass) as [d [r [Hd [Hr _]]]].
  assert (d = 0) by congruence. subst d.
  cbn [msolver_view view_of assignment_rank] in Hr.
  assert (Hrbound :
    0 <= Z.of_nat r < Zlength (mt_trail (ms_core M))).
  { split; [lia|exact (trail_pos_bound _ _ _ Hr)]. }
  pose proof (trail_pos_var _ _ _ Hr) as Hvar.
  assert (Hcell :
    Znth v (mt_assigns (ms_core M)) 0 =
    lit_sig (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
  { rewrite <- Hvar.
    exact (Forall_Znth_elim _ _ _ 0 _ (mtw_trail_true Hwf) Hrbound). }
  assert (Hvnonneg : 0 <= v).
  { pose proof (Forall_Znth_elim _ _ _ 0 (Z.of_nat r)
      (mtw_trail_lits Hwf) Hrbound) as Hlit.
    pose proof (lit_var_c_in_range n
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) Hlit) as Hvrange.
    change (0 <= trail_var (ms_core M) (Z.of_nat r) < n) in Hvrange.
    rewrite Hvar in Hvrange. lia. }
  assert (Hbpol :
    b = lit_pol (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
  { cbn [msolver_view view_of assignment] in Hass.
    rewrite mt_pv_nonneg in Hass by exact Hvnonneg.
    rewrite Hcell, lbool_val_lit_sig in Hass. congruence. }
  specialize (Htrailimpl (Z.of_nat r)
    (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)
    Hrbound eq_refl).
  cbn [msolver_view view_of level_of] in Hlev.
  rewrite Hr in Hlev. cbn [option_map] in Hlev.
  injection Hlev as Hzero.
  rewrite Hzero in Htrailimpl.
  unfold decisions_upto, ztake in Htrailimpl. cbn in Htrailimpl.
  assert (Hvarc : lit_var_c
    (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) = v) by exact Hvar.
  rewrite lit_denote_satisfying, Hvarc, <- Hbpol in Htrailimpl.
  unfold cnf_with_units in Htrailimpl. cbn in Htrailimpl.
  rewrite app_nil_r in Htrailimpl.
  exact Htrailimpl.
Qed.

(* A trail slot in range carries a well-formed literal, so its variable is in
   range.  Both spellings of the index the scan obligations use go through
   this step. *)
Lemma msat_trail_lit_var_range_p1 :
  forall n M idx,
    mtrail_wf n (ms_core M) ->
    0 <= idx < Zlength (mt_trail (ms_core M)) ->
    0 <= lit_var_c (Znth idx (mt_trail (ms_core M)) 0) < n.
Proof.
  intros n M idx Hwf Hidx.
  apply lit_var_c_in_range.
  exact (Forall_Znth_elim _ _ _ 0 idx (mtw_trail_lits Hwf) Hidx).
Qed.

(* Same fact reached from the rank side: a variable that has a trail position
   is a trail literal's variable, hence in range. *)
Lemma msat_trail_pos_var_range_p1 :
  forall n M x k,
    mtrail_wf n (ms_core M) ->
    0 <= k ->
    trail_pos (ms_core M) x = Some (Z.to_nat k) ->
    0 <= x < n.
Proof.
  intros n M x k Hwf Hk Hpos.
  assert (Hidx : 0 <= k < Zlength (mt_trail (ms_core M))).
  { split; [lia|].
    pose proof (trail_pos_bound _ _ _ Hpos) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  pose proof (msat_trail_lit_var_range_p1 n M k Hwf Hidx) as Hrange.
  pose proof (trail_pos_var _ _ _ Hpos) as Hvar.
  rewrite Z2Nat.id in Hvar by lia.
  change (lit_var_c (Znth k (mt_trail (ms_core M)) 0) = x) in Hvar.
  rewrite Hvar in Hrange. exact Hrange.
Qed.

(* The reason clause a tagged variable carries starts with that variable's own
   literal.  Read off the entry bundle's reason bookkeeping, which is the same
   for the two propagation contexts. *)
Lemma msat_analysis_reason_head_var_p1 :
  forall n F A_arr K M focus x Ccur,
    analysis_cancel_ready n F A_arr K M focus ->
    0 <= x < n ->
    ms_reason_of M x = Some Ccur ->
    literal_var (Znth 0 Ccur (Pos 0)) = x.
Proof.
  intros n F A_arr K M focus x Ccur Hready Hxrange Hreason_M.
  destruct Hready as [Mready [Hcancel [Hequiv _]]].
  destruct Hcancel as [Hweak _]. destruct Hweak as [_ Hinv].
  assert (Hsize : n = ms_size Mready) by
    (destruct K; [exact (msw_size Hinv)|exact (msa_size Hinv)]).
  assert (Hmatch : reasons_match n (ms_core Mready) (msolver_db Mready)
    (ms_reason_words Mready) (ms_reason_of Mready)) by
    (destruct K;
     [exact (msw_reasons_mem Hinv)|exact (msa_reasons_mem Hinv)]).
  assert (Hhead : reason_head_ok Mready) by
    (destruct K;
     [exact (msw_reason_head Hinv)|exact (msa_reason_head Hinv)]).
  assert (Hdbwf : db_wf n (msolver_db Mready)) by
    (destruct K; [exact (msw_db_wf Hinv)|exact (msa_db_wf Hinv)]).
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    [_ [_ [_ [_ [_ [_ [Ereason _]]]]]]].
  assert (Hreason : ms_reason_of Mready x = Some Ccur).
  { rewrite <- Ereason. exact Hreason_M. }
  specialize (Hmatch x Hxrange).
  remember (Znth x (ms_reason_words Mready) 0) as w eqn:Hw.
  assert (Hwneq : w <> 0).
  { intro Hw0.
    unfold reason_word_ok in Hmatch.
    rewrite Hw0 in Hmatch. cbn in Hmatch. congruence. }
  assert (Hwzero : Z.eqb w 0 = false) by
    (apply Z.eqb_neq; exact Hwneq).
  destruct (is_tag w) eqn:Htag.
  - unfold reason_word_ok in Hmatch. rewrite Hwzero, Htag in Hmatch.
    destruct Hmatch as [_ Hshape]. rewrite Hreason in Hshape.
    inversion Hshape. cbn.
    rewrite lit_var_c_denote, trail_lit_of_var; lia.
  - unfold reason_word_ok in Hmatch. rewrite Hwzero, Htag in Hmatch.
    destruct Hmatch as [_ [co [Hin Hshape]]].
    rewrite Hreason in Hshape. inversion Hshape; subst Ccur.
    assert (Hxsize : 0 <= x < ms_size Mready) by lia.
    specialize (Hhead x co Hxsize).
    rewrite <- Hw in Hhead.
    specialize (Hhead Htag Hwneq Hin).
    pose proof (db_wf_obj n (msolver_db Mready) w co Hdbwf Hin) as Hobj.
    unfold obj_wf in Hobj. destruct Hobj as [Hlen _].
    unfold denote_obj, lits_denote.
    rewrite (Znth_map Z literal lit_denote (co_lits co) 0 0 (Pos 0)) by lia.
    rewrite lit_var_c_denote.
    exact Hhead.
Qed.

(* The three `analysis_core_equiv` components the scan obligations transport
   between the active state and the state the scan reports.  The trail core
   and the reason map are stated scan-side first, because they are used to
   rewrite a goal about the scan state back to the active state; the view
   equation is stated the other way round, which is how the obligations
   consume it. *)
Lemma msat_analysis_equiv_transport_p1 :
  forall n M M',
    analysis_core_equiv M M' ->
    ms_core M' = ms_core M /\
    ms_reason_of M' = ms_reason_of M /\
    msolver_view n M = msolver_view n M'.
Proof.
  intros n M M' Hequiv.
  pose proof (analysis_core_equiv_view__analyze n M M' Hequiv)
    as Eview.
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as [_ [_ [_ [Ecore [_ [_ [Ereason _]]]]]]].
  split; [exact Ecore|].
  split; [exact Ereason|].
  symmetry. exact Eview.
Qed.

(* The scan obligations state the clause prefix they have consumed as
   `skipn 1 (firstn j Ccur)`; when j is the whole length that is the clause
   tail, and the clause is its own head consed onto that tail. *)
Lemma msat_clause_head_tail_p1 :
  forall Ccur j,
    0 < j ->
    j = Zlength Ccur ->
    Ccur = Znth 0 Ccur (Pos 0) :: tl Ccur /\
    skipn (Pos.to_nat 1) (firstn (Z.to_nat j) Ccur) = tl Ccur.
Proof.
  intros Ccur j Hjpos Hjfull.
  assert (HCcons : Ccur = Znth 0 Ccur (Pos 0) :: tl Ccur).
  { destruct Ccur as [|q qs]; [cbn in Hjfull; lia|reflexivity]. }
  split; [exact HCcons|].
  assert (Hprefixall : firstn (Z.to_nat j) Ccur = Ccur).
  { rewrite Hjfull, Zlength_correct, Nat2Z.id. apply firstn_all. }
  rewrite Hprefixall. cbn [Pos.to_nat]. destruct Ccur; reflexivity.
Qed.

(* Resolving on the reason clause ignores its head literal: the head is the
   resolved variable's own literal and that variable is already tagged, so
   both the pending set and the learnt clause see only the tail. *)
Lemma msat_resolve_head_drop_p1 :
  forall a x Ccur S0 R0 learnt0,
    Ccur = Znth 0 Ccur (Pos 0) :: tl Ccur ->
    literal_var (Znth 0 Ccur (Pos 0)) = x ->
    In x S0 ->
    resolve_S a x Ccur S0 R0 learnt0 =
      resolve_S a x (tl Ccur) S0 R0 learnt0 /\
    resolve_learnt a Ccur S0 R0 learnt0 =
      resolve_learnt a (tl Ccur) S0 R0 learnt0.
Proof.
  intros a x Ccur S0 R0 learnt0 HCcons Hheadvar HinS.
  assert (Htagx : zmem x (analyze_tags S0 R0 learnt0) = true).
  { apply zmem_true_iff. unfold analyze_tags.
    apply in_or_app. left. exact HinS. }
  split.
  - unfold resolve_S, resolve_new_S.
    rewrite HCcons at 1. cbn [filter map].
    destruct (at_current_level_b a (Znth 0 Ccur (Pos 0))); cbn [filter map].
    + rewrite Hheadvar, Htagx. cbn. reflexivity.
    + reflexivity.
  - unfold resolve_learnt, resolve_new_lits.
    rewrite HCcons at 1. cbn [filter].
    rewrite Hheadvar, Htagx, andb_false_r. cbn. reflexivity.
Qed.

(* After one resolution step the pending set sits strictly below the resolved
   variable's rank and the resolved set strictly above it, which is what the
   backward-scan invariant carries as its two rank bounds. *)
Lemma msat_analyze_scan_rank_split_p1 :
  forall F a S0 R0 learnt0 Sscan Rscan learnt_scan x ind,
    0 <= ind ->
    analyze_inv F a Sscan Rscan learnt_scan ->
    analyze_inv F a S0 R0 learnt0 ->
    Rscan = x :: R0 ->
    In x S0 ->
    assignment_rank a x = Some (Z.to_nat (ind + 1)) ->
    (forall y, In y Sscan ->
       exists r, assignment_rank a y = Some r /\ Z.of_nat r <= ind) /\
    (forall y, In y Rscan ->
       exists r, assignment_rank a y = Some r /\ ind < Z.of_nat r).
Proof.
  intros F a S0 R0 learnt0 Sscan Rscan learnt_scan x ind
    Hind Hinvscan Hinv0 HRscan HinS Hrankx.
  split.
  - intros y Hy.
    pose proof Hinvscan as Htmp.
    destruct Htmp as [_ [_ [_ [_ [_ [HrankR _]]]]]].
    rewrite Forall_forall in HrankR.
    specialize (HrankR x ltac:(rewrite HRscan; left; reflexivity) y Hy).
    destruct HrankR as [ry [rx [Hry [Hrx Hlt]]]].
    rewrite Hrankx in Hrx. injection Hrx as <-.
    exists ry. split; [exact Hry|].
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. lia.
  - intros y Hy. rewrite HRscan in Hy. cbn in Hy.
    destruct Hy as [<-|Hy].
    + exists (Z.to_nat (ind + 1)). split; [exact Hrankx|].
      rewrite Z2Nat.id by lia. lia.
    + pose proof Hinv0 as Htmp.
      destruct Htmp as [_ [_ [_ [_ [_ [HrankR _]]]]]].
      rewrite Forall_forall in HrankR.
      specialize (HrankR y Hy x HinS).
      destruct HrankR as [rx [ry [Hrx [Hry Hlt]]]].
      rewrite Hrankx in Hrx. injection Hrx as <-.
      exists ry. split; [exact Hry|].
      apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by lia. lia.
Qed.

(* A generic list fact, kept out of the VC proof that needs it: an all-zero
   list is a run of zeros of its own length. *)
Lemma msat_forall_zero_repeat_p1 :
  forall xs : list Z,
    Forall (fun z => z = 0) xs -> xs = repeat 0 (length xs).
Proof.
  intros xs Hxs. induction Hxs; simpl.
  - reflexivity.
  - subst x. f_equal. exact IHHxs.
Qed.

(* Refolding the statistics block after one counter has been written: the
   other ten fields are untouched by the update, which is what the eleven
   `Znth_replace_Znth_*` steps say. *)
Lemma msat_stats_starts_refold_p1 :
  forall p st v,
    Zlength st = 11 ->
    (&( p # "stats_t" ->ₛ "starts") # UInt64 |-> v) **
    stats_without_starts_rep p st
    |-- stats_rep p (replace_Znth 0 v st).
Proof.
  intros p st v Hlen.
  unfold stats_without_starts_rep, stats_rep.
  unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
    stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
    stats_learnts_literals, stats_max_literals, stats_tot_literals.
  rewrite Zlength_replace_Znth.
  rewrite (Znth_replace_Znth_Same 0 st 0 v) by lia.
  rewrite !Znth_replace_Znth_Diff by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* The freshly built empty `learnt_clause` vector, folded into the vector
   representation predicate: three field cells, an empty segment and the
   undefined tail of a four-element buffer. *)
Lemma msat_learnt_clause_veci_fold_p1 :
  forall learnt_ptr,
    (&((&("learnt_clause"))->ₛ "size") # Int |-> 0) **
    (&((&("learnt_clause"))->ₛ "cap") # Int |-> 4) **
    (&((&("learnt_clause"))->ₛ "ptr") # Ptr |-> learnt_ptr) **
    IntArray.seg learnt_ptr 0 0 (@nil Z) **
    IntArray.undef_seg learnt_ptr 0 4
    |-- veci_rep (&("learnt_clause")) (@nil Z) 4.
Proof.
  intros learnt_ptr.
  unfold veci_rep. Exists learnt_ptr. unfold veci_rep_at.
  apply derivable1s_coq_prop_andp_r.
  2: { rewrite Zlength_nil. lia. }
  cbn [Zlength].
  assert (Hsize :
      &((&("learnt_clause"))->ₛ "size") = veci_size_addr (&("learnt_clause")))
    by (unfold veci_size_addr; csimpl; reflexivity).
  assert (Hcap :
      &((&("learnt_clause"))->ₛ "cap") = veci_cap_addr (&("learnt_clause")))
    by (unfold veci_cap_addr; csimpl; reflexivity).
  assert (Hptr :
      &((&("learnt_clause"))->ₛ "ptr") = veci_ptr_addr (&("learnt_clause")))
    by (unfold veci_ptr_addr; csimpl; reflexivity).
  rewrite Hsize, Hcap, Hptr. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_simplify partial_solve wits (2 proofs) ===== *)
Lemma proof_of_clause_simplify_partial_solve_wit_9_pure : clause_simplify_partial_solve_wit_9_pure.
Proof.
  msat_clause_simplify_lit_range_pure.
Qed.

Lemma proof_of_clause_simplify_partial_solve_wit_10_pure : clause_simplify_partial_solve_wit_10_pure.
Proof.
  msat_clause_simplify_lit_range_pure.
Qed.

(* ===== clause_simplify which_implies wits (2 proofs) ===== *)
Lemma proof_of_clause_simplify_which_implies_wit_1 : clause_simplify_which_implies_wit_1.
Proof.
  aggressive_pre_process;
    bind_fact ( clause_simplify_scan_inv n clause_words assigns0 i ) as H_clause_simplify_scan_inv;
    unfold clause_simplify_scan_inv in H_clause_simplify_scan_inv;
    destruct H_clause_simplify_scan_inv as (Hi & Halen & Hlits & Hcells & Hprefix);
    assert (Hwf : lit_wf_c n (Znth i clause_words 0)) by
      (apply (Forall_Znth_elim Z (lit_wf_c n)
         clause_words 0 i Hlits); lia);
    pose proof (lit_var_c_in_range n (Znth i clause_words 0) Hwf) as Hvar;
    try lia.
  replace (i - 0) with i by lia. reflexivity.
Qed.

Lemma proof_of_clause_simplify_which_implies_wit_2 : clause_simplify_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  replace (lit_var_c current_lit - 0) with (lit_var_c current_lit) by lia.
  reflexivity.
Qed.

(* ===== enqueue entail wits (5 proofs) ===== *)
Lemma proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst l_pre.
  (* The two INT range side-conditions on l0 are FORCED BY THE HEAP -- they do not
     follow from the pure hypotheses, so harvest them from the `l` Int cell.
     `store_int_range` yields Int.min_signed/Int.max_signed, which lia cannot see
     through; `change` normalises them to literals. *)
  prop_rewrite (store_int_range (&( "l")) l0).
  Intros_p Hl_range.
  change (-2147483648 <= l0 <= 2147483647) in Hl_range.
  subst retval.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_enqueue_entail_wit_3_1 : enqueue_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  msat_enqueue_assign_keep_close_p1 (-1) retval_2 l_pre l0 assigns qtail levels0 reasons0 trail rsn trl asg n.
Qed.

Lemma proof_of_enqueue_entail_wit_3_2 : enqueue_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  msat_enqueue_assign_keep_close_p1 1 retval_2 l_pre l0 assigns qtail levels0 reasons0 trail rsn trl asg n.
Qed.

Lemma proof_of_enqueue_entail_wit_4_1 : enqueue_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  msat_enqueue_assign_bump_close_p1 (-1) retval_2 l_pre retval_3 l0 assigns
    qtail levels0 reasons0 trail rsn trl asg lvl n lim reason_pre.
Qed.

Lemma proof_of_enqueue_entail_wit_4_2 : enqueue_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  msat_enqueue_assign_bump_close_p1 1 retval_2 l_pre retval_3 l0 assigns
    qtail levels0 reasons0 trail rsn trl asg lvl n lim reason_pre.
Qed.

(* ===== enqueue partial_solve wits (3 proofs) ===== *)
Lemma proof_of_enqueue_partial_solve_wit_2_pure : enqueue_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  msat_enqueue_input_lit_bound_p1 n l0 qtail assigns levels0 reasons0 trail l_pre.
Qed.

Lemma proof_of_enqueue_partial_solve_wit_5_pure : enqueue_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  msat_enqueue_input_lit_bound_p1 n l0 qtail assigns levels0 reasons0 trail l_pre.
Qed.

Lemma proof_of_enqueue_partial_solve_wit_6_pure : enqueue_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  all: (bind_fact ( Znth (lit_var_c l0) (replace_Znth (lit_var_c l0) (Znth (lit_var_c l0) assigns 0) assigns) 0 = 0 ) as
        H_Znth);
    (bind_fact ( enqueue_input n l0 qtail assigns levels0 reasons0 trail ) as H_enqueue_input);
    (bind_fact ( retval = lit_var_c l_pre ) as H_retval);
    (bind_fact ( l_pre = l0 ) as H_l_pre);
    (assert (Hself :
      replace_Znth (lit_var_c l0) (Znth (lit_var_c l0) assigns 0) assigns =
      assigns) by apply replace_Znth_Znth);
    (rewrite Hself in H_Znth);
    (dump_pre_spatial).
  - (* This conjunct is stated over the call's return value rather than over
       `lit_var_c l0`; the two identity equations re-spell it. *)
    rewrite H_retval, H_l_pre. exact H_Znth.
  - unfold enqueue_input in H_enqueue_input.
    destruct H_enqueue_input as (_ & _ & _ & _ & _ & _ & _ & Hroom & _).
    specialize (Hroom H_Znth). lia.
  - (* The goal also carries the `l_pre`-spelled copy of the same conjunct, so
       it must be discharged a second time. *)
    rewrite H_l_pre. exact H_Znth.
Qed.

(* ===== solver_analyze entail wits (10 proofs) ===== *)
Lemma proof_of_solver_analyze_entail_wit_12_14_learnt : solver_analyze_entail_wit_12_14_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_14_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  Left.
  Exists cap_scan_2 activity_ptr_scan_2 orderpos_ptr_scan_2
    S0_2 R0_2 learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2
    words_scan_2 Mscan_2.
  entailer_with ltac:(lia).
  unfold analyze_clause_scan_inv in *.
  subst phase j Mact.
  cbn in *.
  match goal with
  | Hbundle0 : analysis_cancel_ready anz_n anz_F anz_A_arr K Mscan_2 anz_focus /\ _ |- _ =>
      rename Hbundle0 into Hbundle_scan
  end.
  pose proof Hbundle_scan as Hscan_facts.
  decompose [and] Hscan_facts.
  assert (Hrootnonneg : 0 <= ms_root_level Mscan_2).
  { match goal with
    | Hready0 : analysis_cancel_ready anz_n anz_F anz_A_arr K Mscan_2 anz_focus |- _ =>
        pose proof Hready0 as Hready
    end.
    destruct Hready as [Mready [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak _].
    destruct Hweak as [_ Hinv].
    assert (Hrootready : 0 <= ms_root_level Mready).
    { destruct K.
      - pose proof (msw_shape Hinv) as Hshape.
        unfold solver_shape in Hshape. tauto.
      - pose proof (msa_shape Hinv) as Hshape.
        unfold solver_shape in Hshape. tauto. }
    unfold analysis_core_equiv in Hequiv.
    destruct Hequiv as [_ [_ [_ [_ [Eroot _]]]]].
    rewrite Eroot. exact Hrootready. }
  assert (Hwf : mtrail_wf anz_n (ms_core Mscan_2)) by
    (eapply analysis_cancel_ready_trail_wf__analyze; eassumption).
  pose proof (msat_msolver_view_level_cell anz_n Mscan_2 Hwf) as Hlevelcell.
  assert (HClen : Zlength Ccur = Zlength clause_words2).
  { match goal with
    | HCwords : Ccur = lits_denote clause_words2 |- _ =>
        rewrite HCwords, lits_denote_length
    end. reflexivity. }
  assert (HCsingle :
    sublist 1 2 Ccur = Znth 1 Ccur (Pos 0) :: nil).
  { replace 2 with (1 + 1) by lia. apply sublist_single. lia. }
  assert (Hqnth :
    Znth 1 Ccur (Pos 0) = lit_denote (Znth 1 clause_words2 0)).
  { match goal with
    | HCwords : Ccur = lits_denote clause_words2 |- _ => rewrite HCwords
    end. unfold lits_denote.
    apply Znth_map. lia. }
  assert (Hlevxcur :
    level_of (msolver_view anz_n Mscan_2) x_2 =
      Some (current_level (msolver_view anz_n Mscan_2))).
  { match goal with
    | Hinv0 : analyze_inv anz_F (msolver_view anz_n Mscan_2)
        S0_2 R0_2 learnt0_2 |- _ =>
        destruct Hinv0 as [_ [_ [HlevS _]]]
    end.
    rewrite Forall_forall in HlevS. apply HlevS. assumption. }
  match goal with
  | Hrv : reason_valid (msolver_view anz_n Mscan_2) x_2 Ccur |- _ =>
      destruct Hrv as
        [b [d [r [Hass [Hlevx [Hrank [Hsat Hside]]]]]]]
  end.
  assert (HqIn : In (Znth 1 Ccur (Pos 0)) Ccur).
  { apply Znth_In. lia. }
  assert (Hqraw :
    Znth (literal_var (Znth 1 Ccur (Pos 0)))
      (mt_levels (ms_core Mscan_2)) 0 <= 0).
  { rewrite Hqnth, lit_var_c_denote.
    match goal with
    | Hraw0 : Znth (?rv - 0) (mt_levels (ms_core Mscan_2)) 0 <= 0,
      Heq0 : ?rv = lit_var_c (Znth 1 clause_words2 0) |- _ =>
        rewrite <- Heq0;
        replace rv with (rv - 0) by lia;
        exact Hraw0
    end. }
  assert (Hqneq : literal_var (Znth 1 Ccur (Pos 0)) <> x_2).
  { intro Heq. rewrite Heq in Hqraw.
    pose proof (Hlevelcell x_2
      (current_level (msolver_view anz_n Mscan_2)) Hlevxcur) as Hxcell.
    rewrite Hxcell, msolver_view_current_level in Hqraw. lia. }
  destruct (Hside _ HqIn Hqneq) as
    [_ [dy [ry [Hqlevel [Hqrank [Hdyle Hry]]]]]].
  pose proof (Hlevelcell
    (literal_var (Znth 1 Ccur (Pos 0))) dy Hqlevel) as Hqcell.
  rewrite Hqcell in Hqraw.
  assert (Hat : at_current_level_b (msolver_view anz_n Mscan_2)
    (Znth 1 Ccur (Pos 0)) = false).
  { unfold at_current_level_b. rewrite Hqlevel.
    apply Z.eqb_neq. rewrite msolver_view_current_level. lia. }
  assert (Hbelow : below_current_b (msolver_view anz_n Mscan_2)
    (Znth 1 Ccur (Pos 0)) = false).
  { unfold below_current_b. rewrite Hqlevel.
    destruct (Z.ltb 0 dy) eqn:Hdypos.
    - apply Z.ltb_lt in Hdypos. lia.
    - reflexivity. }
  intuition (try lia).
  - match goal with
    | Hbase0 : Sscan_2 = resolve_S (msolver_view anz_n Mscan_2) x_2
        (skipn (Pos.to_nat 1) (firstn (Pos.to_nat 1) Ccur))
        S0_2 R0_2 learnt0_2 |- _ => pose proof Hbase0 as Hbase
    end.
    change (Sscan_2 = resolve_S (msolver_view anz_n Mscan_2) x_2
      (sublist 1 1 Ccur) S0_2 R0_2 learnt0_2) in Hbase.
    rewrite (Zsublist_nil Ccur 1 1) in Hbase by lia.
    change (Sscan_2 = resolve_S (msolver_view anz_n Mscan_2) x_2
      (sublist 1 2 Ccur) S0_2 R0_2 learnt0_2).
    rewrite HCsingle.
    unfold resolve_S, resolve_new_S. cbn [filter map].
    rewrite Hat. cbn.
    exact Hbase.
  - match goal with
    | Hbase0 : learnt_scan_2 = resolve_learnt (msolver_view anz_n Mscan_2)
        (skipn (Pos.to_nat 1) (firstn (Pos.to_nat 1) Ccur))
        S0_2 R0_2 learnt0_2 |- _ => pose proof Hbase0 as Hbase
    end.
    change (learnt_scan_2 = resolve_learnt (msolver_view anz_n Mscan_2)
      (sublist 1 1 Ccur) S0_2 R0_2 learnt0_2) in Hbase.
    rewrite (Zsublist_nil Ccur 1 1) in Hbase by lia.
    change (learnt_scan_2 = resolve_learnt (msolver_view anz_n Mscan_2)
      (sublist 1 2 Ccur) S0_2 R0_2 learnt0_2).
    rewrite HCsingle.
    unfold resolve_learnt, resolve_new_lits. cbn [filter].
    rewrite Hbelow. cbn.
    exact Hbase.
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_15_learnt : solver_analyze_entail_wit_12_15_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_15_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia). msat_analyze_scan_stop_p1 cap_scan_2 orderpos_ptr_scan_2 activity_ptr_scan_2 S0_2 R0_2
    learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 Mscan_2 phase j Ccur clause_words2 anz_n K Mact.
Qed.

Lemma proof_of_solver_analyze_entail_wit_12_16_learnt : solver_analyze_entail_wit_12_16_learnt.
Proof.
  unfold solver_analyze_entail_wit_12_16_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia). msat_analyze_scan_stop_p1 cap_scan_2 orderpos_ptr_scan_2 activity_ptr_scan_2 S0_2 R0_2
    learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 Mscan_2 phase j Ccur clause_words2 anz_n K Mact.
Qed.

Lemma proof_of_solver_analyze_entail_wit_13_1_learnt : solver_analyze_entail_wit_13_1_learnt.
Proof.
  unfold solver_analyze_entail_wit_13_1_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_core_equiv Mact Mscan ) as H_analysis_core_equiv.
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R0 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  Left.
  Exists cap_scan activity_ptr_scan orderpos_ptr_scan
    words_scan Sscan Rscan learnt_scan Mscan.
  entailer_with lia.
  (* Both residual goals carry the same scan invariant and the same analysis
     entry bundle, so open the invariant once for both and bind each of its
     twenty-seven components to a content name.  The two goals number the
     anonymous hypotheses differently, which is exactly why the rest of this
     proof reads the destructuring pattern below and never an `H<k>`. *)
  all: (unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv);
    (subst phase);
    (cbn in H_analyze_clause_scan_inv);
    (destruct H_analyze_clause_scan_inv as
         (Hready & Hcore & (Hindlo & Hindhi) & Hrootlim & Hlitwf & Hnodup &
          (Hjlo & Hjhi) & Hcnt & (Hwordslo & Hwordshi) & Hwordsden & Htagsexact
          & Htagsperm & Hcntpos & Hjone & HxinS0 & Hxrank & Hrankothers & Hinv0
          & Hreason & Hreasonvalid & Hentails & HSscan & HRscan & Hlearntscan)).
  all: (destruct (msat_analysis_ready_scan_facts_p1 anz_n anz_F anz_A_arr K
         Mscan anz_focus Hready)
         as (Hwf & Hstable & Htrailimpl & Hqtail & Hlevel0));
    (assert (Hindex : 0 <= ind < Zlength (mt_trail (ms_core Mscan))) by lia);
    (pose proof (msat_trail_lit_var_range_p1 anz_n Mscan ind Hwf Hindex)
         as Hvarrange);
    (try (match goal with |- context [?idx - 0] =>
              replace (idx - 0) with idx by lia end));
    (try lia).
  2: {
  destruct (msat_analysis_equiv_transport_p1 anz_n Mact Mscan
    H_analysis_core_equiv) as (Ecore & Ereason & Hview).
  assert (Hxrange : 0 <= x < anz_n).
  { apply (msat_trail_pos_var_range_p1 anz_n Mscan x (ind + 1) Hwf ltac:(lia)).
    rewrite Ecore. exact Hxrank. }
  assert (Hheadvar : literal_var (Znth 0 Ccur (Pos 0)) = x).
  { apply (msat_analysis_reason_head_var_p1 anz_n anz_F anz_A_arr K Mscan
      anz_focus x Ccur Hready Hxrange).
    rewrite Ereason. exact Hreason. }
  assert (Hnewinv : analyze_inv anz_F (msolver_view anz_n Mscan)
    (resolve_S (msolver_view anz_n Mscan) x Ccur S0 R0 learnt0)
    (x :: R0)
    (resolve_learnt (msolver_view anz_n Mscan) Ccur S0 R0 learnt0)).
  { eapply analyze_resolve_step.
    - exact (proj2 Hstable).
    - exact Hlevel0.
    - rewrite <- Hview. exact Hinv0.
    - exact HxinS0.
    - rewrite <- Hview.
      cbn [msolver_view view_of reason_of]. rewrite Hxrank. exact Hreason.
    - rewrite <- Hview. exact Hreasonvalid.
    - exact Hentails.
    - exact Hnodup.
    - intros s Hs Hsx. rewrite <- Hview. apply Hrankothers; assumption. }
  assert (Hjfull : j = Zlength Ccur) by
    (rewrite H_Ccur, lits_denote_length; lia).
  destruct (msat_clause_head_tail_p1 Ccur j ltac:(lia) Hjfull)
    as (HCcons & Hscanpart).
  destruct (msat_resolve_head_drop_p1 (msolver_view anz_n Mscan) x Ccur
    S0 R0 learnt0 HCcons Hheadvar HxinS0) as (HresolveS & HresolveL).
  rewrite Hscanpart, Hview in HSscan, Hlearntscan.
  rewrite <- HresolveS in HSscan. rewrite <- HresolveL in Hlearntscan.
  assert (Hinvscan : analyze_inv anz_F (msolver_view anz_n Mscan)
    Sscan Rscan learnt_scan).
  { rewrite HSscan, HRscan, Hlearntscan. exact Hnewinv. }
  assert (Hrankx : assignment_rank (msolver_view anz_n Mscan) x =
      Some (Z.to_nat (ind + 1))) by (rewrite <- Hview; exact Hxrank).
  destruct (msat_analyze_scan_rank_split_p1 anz_F (msolver_view anz_n Mscan)
    S0 R0 learnt0 Sscan Rscan learnt_scan x ind ltac:(lia) Hinvscan
    ltac:(rewrite <- Hview; exact Hinv0) HRscan HxinS0 Hrankx)
    as (Hpending & Hresolved).
  assert (HexS : exists y, In y Sscan) by
    (destruct Sscan as [|y ys]; [cbn in Hcnt; lia|exists y; left; reflexivity]).
  destruct HexS as [y Hy]. destruct (Hpending y Hy) as [r [Hyr Hri]].
  unfold analyze_backward_scan_inv.
  split; [exact Hready|]. split; [exact Hinvscan|]. split; [exact Hcnt|].
  split; [exact Hcntpos|]. split; [exact (conj Hindlo Hindhi)|].
  split; [exact (conj Hwordslo Hwordshi)|]. split; [exact Hrootlim|]. split; [exact Hwordsden|].
  split; [exact Htagsexact|]. split; [exact Htagsperm|]. split; [exact Hpending|].
  split; [exact Hresolved|]. exists y, r. split; [ | split ]; assumption. }
  intros Htag0.
  destruct (Z.eq_dec ind 0) as [Hzeroind|Hzeroind]; [subst ind|lia].
  destruct (msat_analysis_equiv_transport_p1 anz_n Mact Mscan H_analysis_core_equiv)
    as (_ & _ & Hview0).
  assert (Hjfull0 : j = Zlength Ccur) by
    (rewrite H_Ccur, lits_denote_length; lia).
  destruct (msat_clause_head_tail_p1 Ccur j ltac:(lia) Hjfull0)
    as (HCcons0 & Hscanpart0).
  rewrite Hview0, Hscanpart0 in HSscan.
  assert (Htagx0 : zmem x (analyze_tags S0 R0 learnt0) = true).
  { apply zmem_true_iff. unfold analyze_tags.
    apply in_or_app. left. exact HxinS0. }
  assert (HexS0 : exists y, In y Sscan) by
    (destruct Sscan as [|y ys]; [cbn in Hcnt; lia|exists y; left; reflexivity]).
  destruct HexS0 as [y Hy].
  assert (Hrankyx : rank_lt (msolver_view anz_n Mscan) y x).
  { rewrite HSscan in Hy. unfold resolve_S in Hy.
    apply in_app_or in Hy. destruct Hy as [Hy|Hy].
    - apply In_zremove_iff in Hy. destruct Hy as [HyS Hyx].
      rewrite <- Hview0. apply Hrankothers; assumption.
    - unfold resolve_new_S in Hy. apply filter_In in Hy.
      destruct Hy as [Hymap Hyfresh]. apply negb_true_iff in Hyfresh.
      rewrite in_map_iff in Hymap.
      destruct Hymap as [m [Hmy Hmfilter]].
      apply filter_In in Hmfilter. destruct Hmfilter as [Hm _].
      assert (Hmyx : y <> x).
      { intro Heq. rewrite Heq, Htagx0 in Hyfresh. discriminate. }
      assert (Hmx : literal_var m <> x) by congruence.
      assert (HmC : In m Ccur).
      { rewrite HCcons0. right. exact Hm. }
      pose proof Hreasonvalid as Hrv.
      destruct Hrv as [b [d [rx [Hass [Hlev [Hrank [Hin Hothers]]]]]]].
      destruct (Hothers m HmC Hmx) as
        [_ [dy [ry [Hmlev [Hmrank [Hdy Hry]]]]]].
      rewrite <- Hview0. unfold rank_lt.
      exists ry, rx. split; [ rewrite <- Hmy; exact Hmrank | split; assumption ]. }
  assert (Hrankx0 : assignment_rank (msolver_view anz_n Mscan) x = Some (1%nat)).
  { rewrite <- Hview0. cbn in Hxrank. exact Hxrank. }
  destruct Hrankyx as [ry [rx [Hranky [Hrankx Hlt]]]].
  rewrite Hrankx0 in Hrankx. injection Hrankx as <-.
  assert (ry = 0)%nat by lia. subst ry.
  cbn [msolver_view view_of assignment_rank] in Hranky.
  pose proof (trail_pos_var _ _ _ Hranky) as Hyvar.
  change (lit_var_c (Znth 0 (mt_trail (ms_core Mscan)) 0) = y) in Hyvar.
  assert (Hyv0 : y = lit_var_c
    (Znth 0 (mt_trail (ms_core Mscan)) 0)) by congruence.
  assert (HyAnalyze : In y (analyze_tags Sscan Rscan learnt_scan)).
  { unfold analyze_tags. apply in_or_app. left. exact Hy. }
  assert (HyTagged : In y (ms_tagged Mscan)).
  { eapply Permutation_in; [apply Permutation_sym; exact Htagsperm|exact HyAnalyze]. }
  destruct Htagsexact as [_ [_ [_ [_ Htagiff]]]].
  assert (Hyrange : 0 <= y < anz_n).
  { rewrite Hyv0. exact Hvarrange. }
  pose proof (proj2 (Htagiff y Hyrange) HyTagged) as Htagone.
  replace (0 - 0) with 0 in Htag0 by lia.
  rewrite Hyv0 in Htagone. congruence.
Qed.

Lemma proof_of_solver_analyze_entail_wit_13_2_learnt : solver_analyze_entail_wit_13_2_learnt.
Proof.
  unfold solver_analyze_entail_wit_13_2_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_2 anz_focus phase Ccur j ind S0_2 R0_2
      learnt0_2 x_2 Sscan_2 Rscan_2 learnt_scan_2 words_scan_2 cnt ) as H_analyze_clause_scan_inv.
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
    anz_n anz_F anz_A_arr K Mscan_2 anz_focus Hready_reason) as
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
  assert (Hwf : mtrail_wf anz_n (ms_core Mscan_2)).
  { pose proof Hequiv_entry as Hequiv_wf.
    unfold analysis_core_equiv in Hequiv_wf.
    destruct Hequiv_wf as [_ [_ [_ [Ecore _]]]].
    rewrite Ecore. exact Hwfready. }
  assert (Hdbwf : db_wf anz_n (msolver_db Mscan_2)).
  { pose proof Hequiv_entry as Hequiv_db.
    unfold analysis_core_equiv in Hequiv_db.
    destruct Hequiv_db as
      [_ [_ [_ [_ [_ [_ [_ [Eprob [Elearnt _]]]]]]]]].
    unfold msolver_db in Hdbwfready |- *.
    rewrite Eprob, Elearnt. exact Hdbwfready. }
  cbn [msolver_view view_of assignment_rank] in Hrank.
  assert (Hidx : 0 <= ind + 1 <
    Zlength (mt_trail (ms_core Mscan_2))).
  { split; [lia|].
    pose proof (trail_pos_bound _ _ _ Hrank) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  pose proof (Forall_Znth_elim _ _ _ 0 (ind + 1)
    (mtw_trail_lits Hwf) Hidx) as Hlit.
  pose proof (lit_var_c_in_range anz_n
    (Znth (ind + 1) (mt_trail (ms_core Mscan_2)) 0) Hlit) as Hrange.
  pose proof (trail_pos_var _ _ _ Hrank) as Hvar.
  rewrite Z2Nat.id in Hvar by lia.
  change (lit_var_c (Znth (ind + 1)
    (mt_trail (ms_core Mscan_2)) 0) = x_2) in Hvar.
  assert (Hxrange : 0 <= x_2 < anz_n) by
    (rewrite <- Hvar; exact Hrange).
  specialize (Hmatch x_2 Hxrange).
  remember (Znth x_2 (ms_reason_words Mscan_2) 0) as w eqn:Hw.
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
      pose proof (db_wf_obj anz_n (msolver_db Mscan_2) w co Hdbwf Hin) as Hobj.
      unfold obj_wf in Hobj. destruct Hobj as [Hlen _].
      unfold denote_obj. rewrite lits_denote_length. exact Hlen. }
  rewrite H_Ccur, lits_denote_length in HCge2.
  exfalso. lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_13_3_learnt : solver_analyze_entail_wit_13_3_learnt.
Proof.
  unfold solver_analyze_entail_wit_13_3_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_3 anz_focus phase Ccur j ind S0_3 R0_3
      learnt0_3 x_3 Sscan_3 Rscan_3 learnt_scan_3 words_scan_3 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  pose proof H_analyze_clause_scan_inv as Hscan_original.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  subst phase. cbn in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as
    [Hready [Hequiv_scan [Hind_scan [Hroot
    [HCwf [HCnodup [Hjscan [Hcnt [Hwords [Hden
    [Htags [Hperm Hinitial]]]]]]]]]]]].
  destruct Hinitial as
    [HS0 [HR0 [Hlearnt0 [Hx0 [Hqtail_initial
    [Hconflict [HS [HR Hlearnt]]]]]]]].
  destruct (msat_analysis_ready_scan_facts_p1 anz_n anz_F anz_A_arr K Mscan_3
    anz_focus Hready) as (Hwf & Hstable & Htrailimpl & Hqtrail & Hlevel0).
  destruct (msat_analysis_equiv_transport_p1 anz_n Mact Mscan_3 Hequiv_scan)
    as (_ & _ & Hview).
  destruct Hconflict as
    [Hent [Hfalse_raw [Hconf_wf [Hconf_nd [l [HlC Hllevel]]]]]].
  assert (Hfalse : clause_false
    (assignment (msolver_view anz_n Mact)) Ccur).
  { rewrite msolver_view_assignment.
    intros q HqC. pose proof (Hfalse_raw q HqC) as Hqfalse.
    rewrite Forall_forall in Hconf_wf.
    pose proof (Hconf_wf q HqC) as Hqwf.
    unfold literal_wf, var_in_range in Hqwf.
    unfold eval_partial_literal in Hqfalse |- *.
    rewrite mt_pv_nonneg by lia.
    unfold assigns_pv, assigns_val in Hqfalse. exact Hqfalse. }
  assert (Hstable_act : stable_view (msolver_view anz_n Mact)) by
    (rewrite Hview; exact Hstable).
  assert (Hlevel0_act : forall v b,
    assignment (msolver_view anz_n Mact) v = Some b ->
    level_of (msolver_view anz_n Mact) v = Some 0 ->
    entails_clause anz_F (satisfying_literal v b :: nil)).
  { rewrite Hview. exact Hlevel0. }
  destruct Hstable_act as [Hgrounded_act Hclosed_act].
  pose proof (analyze_init anz_F (msolver_view anz_n Mact) Ccur
    Hgrounded_act Hclosed_act Hlevel0_act Hent Hfalse Hconf_nd) as Hainv.
  assert (HClen : Zlength Ccur = Zlength clause_words2) by
    (rewrite H_Ccur, lits_denote_length; reflexivity).
  assert (Hjfull : j = Zlength Ccur) by lia.
  assert (Hsubfull : sublist 0 j Ccur = Ccur).
  { rewrite Hjfull. apply sublist_self. reflexivity. }
  change (firstn (Z.to_nat j) Ccur = Ccur) in Hsubfull.
  rewrite Hsubfull in HS, Hlearnt.
  unfold analyze_start_S, analyze_start_learnt in Hainv.
  rewrite <- HS, <- HR, <- Hlearnt in Hainv.
  rewrite Hview in Hainv.
  assert (Hqtailind : ms_qtail Mscan_3 = ind + 1).
  { pose proof Hequiv_scan as Hequiv_qtail.
    unfold analysis_core_equiv in Hequiv_qtail.
    destruct Hequiv_qtail as [_ [_ [Eqtail _]]]. lia. }
  assert (HinS : In (literal_var l) Sscan_3).
  { rewrite HS. unfold analyze_start_S.
    apply in_map. apply filter_In. split; [exact HlC|].
    apply at_current_level_b_true_iff.
    rewrite msolver_view_current_level. exact Hllevel. }
  assert (Hcntpos : 0 < cnt).
  { rewrite Hcnt. destruct Sscan_3 as [|s ss].
    - contradiction.
    - rewrite Zlength_cons. pose proof (Zlength_nonneg ss). lia. }
  assert (HSrank : forall v, In v Sscan_3 -> exists r,
    assignment_rank (msolver_view anz_n Mscan_3) v = Some r /\
    Z.of_nat r <= ind).
  { pose proof Hainv as Hainv_fields.
    unfold analyze_inv in Hainv_fields.
    destruct Hainv_fields as [_ [_ [_ [Hassigned _]]]].
    rewrite Forall_forall in Hassigned.
    intros v Hv. destruct (Hassigned v Hv) as [b Hass].
    destruct Hstable as [Hgrounded _].
    destruct (Hgrounded v b Hass) as [d [r [_ [Hrank _]]]].
    exists r. split; [exact Hrank|].
    cbn [msolver_view view_of assignment_rank] in Hrank.
    pose proof (trail_pos_bound _ _ _ Hrank) as Hbound.
    rewrite <- Hqtrail, Hqtailind in Hbound. lia. }
  destruct (HSrank (literal_var l) HinS) as
    [rl [Hlrank Hlrankle]].
  assert (Hbackward : analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mscan_3
    anz_focus words_scan_3 cnt ind Sscan_3 Rscan_3 learnt_scan_3).
  { unfold analyze_backward_scan_inv.
    split; [exact Hready|].
    split; [exact Hainv|].
    split; [exact Hcnt|].
    split; [exact Hcntpos|].
    split; [exact Hind_scan|].
    split; [exact Hwords|].
    split; [exact Hroot|].
    split; [exact Hden|].
    split; [exact Htags|].
    split; [exact Hperm|].
    split; [exact HSrank|].
    split.
    - intros v Hv. rewrite HR in Hv. contradiction.
    - exists (literal_var l), rl. split; [ | split ]; assumption. }
  assert (Hindex : 0 <= ind <
    Zlength (mt_trail (ms_core Mscan_3))) by
    (rewrite <- Hqtrail; exact Hind_scan).
  pose proof (msat_trail_lit_var_range_p1 anz_n Mscan_3 ind Hwf Hindex)
    as Hvarrange.
  assert (Htagzero :
    Znth (lit_var_c (Znth ind (mt_trail (ms_core Mscan_3)) 0))
      (ms_tags Mscan_3) 0 = 0 -> 0 < ind).
  { intro Hzero. destruct (Z.eq_dec ind 0) as [Hind0|]; [|lia].
    subst ind. assert (rl = 0%nat) by lia. subst rl.
    cbn [msolver_view view_of assignment_rank] in Hlrank.
    pose proof (trail_pos_var _ _ _ Hlrank) as Hlvar.
    change (lit_var_c (Znth 0 (mt_trail (ms_core Mscan_3)) 0) =
      literal_var l) in Hlvar.
    assert (HlAnalyze : In (literal_var l)
      (analyze_tags Sscan_3 Rscan_3 learnt_scan_3)).
    { unfold analyze_tags. apply in_or_app. left. exact HinS. }
    assert (HlTagged : In (literal_var l) (ms_tagged Mscan_3)).
    { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact HlAnalyze]. }
    pose proof Htags as Htags_copy.
    destruct Htags_copy as [_ [_ [_ [_ Htagiff]]]].
    assert (Hlrange : 0 <= literal_var l < anz_n) by
      (rewrite <- Hlvar; exact Hvarrange).
    pose proof (proj2 (Htagiff (literal_var l) Hlrange) HlTagged) as Htagone.
    rewrite <- Hlvar in Htagone. congruence. }
  assert (Hscan_box : unit -> analyze_clause_scan_inv anz_n anz_F anz_A_arr K
    Mact Mscan_3 anz_focus AnalyzeInitial Ccur j ind S0_3 R0_3 learnt0_3 x_3
    Sscan_3 Rscan_3 learnt_scan_3 words_scan_3 cnt).
  { intro. exact Hscan_original. }
  destruct Hvarrange as [Hvarlo Hvarhi].
  Right.
  Exists cap_scan activity_ptr_scan orderpos_ptr_scan
    words_scan_3 Sscan_3 Rscan_3 learnt_scan_3 Mscan_3.
  (* Three residual goals, all stated over the `- 0` spelling the array read
     introduces: the tag implication and the two halves of the variable
     range. *)
  entailer_with ltac:(lia);
    replace (ind - 0) with ind by lia;
    [ replace (lit_var_c (Znth ind (mt_trail (ms_core Mscan_3)) 0) - 0)
        with (lit_var_c (Znth ind (mt_trail (ms_core Mscan_3)) 0)) by lia;
      exact Htagzero
    | exact Hvarhi
    | exact Hvarlo ].
Qed.

Lemma proof_of_solver_analyze_entail_wit_13_4_learnt : solver_analyze_entail_wit_13_4_learnt.
Proof.
  unfold solver_analyze_entail_wit_13_4_learnt, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan_4 anz_focus phase Ccur j ind S0_4 R0_4
      learnt0_4 x_4 Sscan_4 Rscan_4 learnt_scan_4 words_scan_4 cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( Ccur = lits_denote clause_words2 ) as H_Ccur.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  subst phase Mact. cbn in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as
    [Hready [Hequiv_scan [Hind_scan [Hroot
    [HCwf [HCnodup [Hjscan [Hcnt [Hwords [Hden
    [Htags [Hperm Hinitial]]]]]]]]]]]].
  destruct Hinitial as
    [HS0 [HR0 [Hlearnt0 [Hx0 [Hqtail_initial
    [Hconflict [HS [HR Hlearnt]]]]]]]].
  destruct Hconflict as
    [Hent [Hfalse [Hconf_wf [Hconf_nd [q [HqC Hqlevel]]]]]].
  assert (HCzero : Zlength Ccur = 0).
  { rewrite H_Ccur, lits_denote_length.
    pose proof (Zlength_nonneg clause_words2). lia. }
  exfalso.
  destruct Ccur as [|a rest].
  - contradiction.
  - rewrite Zlength_cons in HCzero.
    pose proof (Zlength_nonneg rest). lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_14_1 : solver_analyze_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia).
  Exists cap1 words1 S1 R1 learnt1 Mtag; msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_14_2_learnt : solver_analyze_entail_wit_14_2_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame cap_done words_done Sdone Rdone learnt_done Mdone.
Qed.

Lemma proof_of_solver_analyze_entail_wit_14_3_learnt : solver_analyze_entail_wit_14_3_learnt.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_learnt_undef_frame cap_done words_done Sdone Rdone learnt_done Mdone.
Qed.

(* ===== solver_canceluntil_capacity entail wits (1 proofs) ===== *)
Lemma proof_of_solver_canceluntil_capacity_entail_wit_1 : solver_canceluntil_capacity_entail_wit_1.
Proof.
  unfold solver_canceluntil_capacity_entail_wit_1, solver_cancel_open_at.
  Unfold.
  left.
  intros.
  bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  unfold veci_rep at 1.
  Intros order_p.
  unfold veci_rep_at at 1.
  Intros.
  destruct H as [Horderlen Hordercap].
  subst level_pre.
  pose proof H_solver_propagation_inv as Hprop0.
  destruct K; destruct Hprop0 as [_ Hprop].
  - pose proof (msp_weak n F A_arr A_inst M0 Hprop) as Hweak.
    pose proof (msw_shape Hweak) as Hshape.
    pose proof (msw_size Hweak) as Hsize.
    pose proof (msw_heap_wf Hweak) as Hheap_wf.
    msat_capacity_reinsert_arm_tail_p1 Hshape Hheap_wf n M0 order_p p.
  - pose proof (msap_weak n F A_arr A_proc M0 Hprop) as Hweak.
    pose proof (msa_shape Hweak) as Hshape.
    pose proof (msa_size Hweak) as Hsize.
    pose proof (msa_heap_wf Hweak) as Hheap_wf.
    msat_capacity_reinsert_arm_tail_p1 Hshape Hheap_wf n M0 order_p p.
Qed.

(* ===== solver_canceluntil_capacity safety wits (1 proofs) ===== *)
Lemma proof_of_solver_canceluntil_capacity_safety_wit_1 : solver_canceluntil_capacity_safety_wit_1.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  destruct K; destruct H_solver_propagation_inv as [_ Hprop].
  - pose proof (msp_weak n F A_arr A_inst M0 Hprop) as Hweak.
    pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    entailer_with ltac:(lia).
  - pose proof (msap_weak n F A_arr A_proc M0 Hprop) as Hweak.
    pose proof (msa_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_canceluntil partial_solve wits (5 proofs) ===== *)
Lemma proof_of_solver_canceluntil_partial_solve_wit_8_pure : solver_canceluntil_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process;
    replace (c - 0) with c in * by lia; subst retval; msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_partial_solve_wit_9_pure : solver_canceluntil_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process;
    replace (c - 0) with c in * by lia; subst retval; msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_partial_solve_wit_13_pure : solver_canceluntil_partial_solve_wit_13_pure.
Proof.
  Unfold.
  left.
  intros.
  entailer_with ltac:(lia); replace (c - 0) with c by lia; assumption.
Qed.

Lemma proof_of_solver_canceluntil_partial_solve_wit_14_pure : solver_canceluntil_partial_solve_wit_14_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( order_unassigned_pre (ms_size M0) (lit_var_c (Znth c (mt_trail (ms_core M0)) 0)) order_cap_now
      order_now orderpos_now ) as H_order_unassigned_pre.
  entailer_with lia.
  rewrite H_retval.
  replace (c - 0) with c by lia.
  exact H_order_unassigned_pre.
Qed.

Lemma proof_of_solver_canceluntil_partial_solve_wit_16_pure : solver_canceluntil_partial_solve_wit_16_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( cancel_reinsert_loop_inv M0 level_pre c order_cap_now assigns_now reasons_now order_now orderpos_now )
      as H_cancel_reinsert_loop_inv.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  unfold veci_rep, veci_rep_at.
  Intros order_p lim_p.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_canceluntil which_implies wits (5 proofs) ===== *)
Lemma proof_of_solver_canceluntil_which_implies_wit_1 : solver_canceluntil_which_implies_wit_1.
Proof.
  left.
  intros.
  match goal with
  | |- solver_cancel_pre ?s ?level ?M ?wl |-- _ =>
      sep_apply (solver_cancel_pre_open s level M wl)
  end.
  Intros activity assigns orderpos reasons trail.
  Exists activity assigns orderpos reasons trail.
  msat_manual_entailer_with ltac:(intuition lia).
Qed.

Lemma proof_of_solver_canceluntil_which_implies_wit_2 : solver_canceluntil_which_implies_wit_2.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( cancel_clear_loop_inv M0 level c assigns_now reasons_now ) as H_cancel_clear_loop_inv.
  unfold cancel_clear_loop_inv in H_cancel_clear_loop_inv.
  assert (Hlev : 0 <= level < Zlength (mt_lim (ms_core M0))) by tauto.
  pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level H_mtrail_wf Hlev)
    as Hbound.
  assert (Hcrange : 0 <= c < Zlength (mt_trail (ms_core M0))).
  { unfold solver_shape in H_solver_shape. lia. }
  pose proof (Forall_Znth_elim _ _ _ 0 c (mtw_trail_lits H_mtrail_wf) Hcrange)
    as Hlit.
  pose proof (lit_var_c_in_range (ms_size M0)
    (Znth c (mt_trail (ms_core M0)) 0) Hlit) as Hvar.
  unfold lit_wf_c in Hlit.
  unfold solver_shape in H_solver_shape.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_which_implies_wit_3 : solver_canceluntil_which_implies_wit_3.
Proof.
  Unfold.
  left.
  intros.
  sep_apply_l_atomic
    (CharArray.seg_split_to_missing_i assigns_ptr 0 x (ms_size M0)
      assigns_now 0).
  - dump_pre_spatial. lia.
  - replace (x - 0) with x by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_which_implies_wit_4 : solver_canceluntil_which_implies_wit_4.
Proof.
  Unfold.
  left.
  intros.
  sep_apply_l_atomic
    (PtrArray.seg_split_to_missing_i reasons_ptr 0 x (ms_size M0)
      reasons_now 0).
  - dump_pre_spatial. lia.
  - replace (x - 0) with x by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_which_implies_wit_5 : solver_canceluntil_which_implies_wit_5.
Proof.
  Unfold.
  right.
  intros.
  bind_fact ( solver_shape M0 ) as H_solver_shape.
  bind_fact ( mtrail_wf (ms_size M0) (ms_core M0) ) as H_mtrail_wf.
  bind_fact ( cancel_reinsert_loop_inv M0 level c order_cap_now assigns_now reasons_now order_now orderpos_now ) as
      H_cancel_reinsert_loop_inv.
  unfold cancel_reinsert_loop_inv in H_cancel_reinsert_loop_inv.
  assert (Hlev : 0 <= level < Zlength (mt_lim (ms_core M0))) by tauto.
  pose proof (lim_lt_trail (ms_size M0) (ms_core M0) level H_mtrail_wf Hlev)
    as Hbound.
  pose proof (mtw_qhead_range H_mtrail_wf) as Hqhead.
  assert (Hcrange : 0 <= c < Zlength (mt_trail (ms_core M0))) by lia.
  pose proof (Forall_Znth_elim _ _ _ 0 c (mtw_trail_lits H_mtrail_wf) Hcrange)
    as Hlit.
  pose proof (lit_var_c_in_range (ms_size M0)
    (Znth c (mt_trail (ms_core M0)) 0) Hlit) as Hvar.
  unfold lit_wf_c in Hlit.
  unfold solver_shape in H_solver_shape.
  unfold order_unassigned_pre, order_heap_wf, heap_of_lists.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

(* ===== solver_propagate partial_solve wits (12 proofs) ===== *)
Lemma proof_of_solver_propagate_partial_solve_wit_254_scan_move_pure :
  solver_propagate_partial_solve_wit_254_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_254_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_256_scan_same_pure :
  solver_propagate_partial_solve_wit_256_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_256_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_258_scan_move_pure :
  solver_propagate_partial_solve_wit_258_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_258_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_261_scan_same_pure :
  solver_propagate_partial_solve_wit_261_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_261_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_262_scan_move_pure :
  solver_propagate_partial_solve_wit_262_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_262_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_264_scan_move_pure :
  solver_propagate_partial_solve_wit_264_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_264_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  left; intros.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 1 + 1 - 1 ) as H_Znth.
  bind_fact ( retval_3 = lit_var_c (Znth 1 clause_contents 0) ) as H_retval_3.
  bind_fact ( retval_2 = lit_sign_c (Znth 1 clause_contents 0) ) as H_retval_2.
  entailer_with lia;
    rewrite <- ?H_retval_3, <- ?H_retval_2;
    replace retval_3 with (retval_3 - 0) by lia;
    rewrite H_Znth; lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_265_scan_move_pure :
  solver_propagate_partial_solve_wit_265_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_265_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_266_scan_same_pure :
  solver_propagate_partial_solve_wit_266_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_266_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_268_scan_same_pure :
  solver_propagate_partial_solve_wit_268_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_268_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_269_scan_same_pure :
  solver_propagate_partial_solve_wit_269_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_269_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_273_scan_move_pure :
  solver_propagate_partial_solve_wit_273_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_273_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_275_scan_same_pure :
  solver_propagate_partial_solve_wit_275_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_275_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold; left; intros;
    msat_propagate_close_scan_first_lit_assigned Hassign Hprop Hsign Hsimp Hstate Hvar.
Qed.

(* ===== solver_record entail wits (3 proofs) ===== *)
Lemma proof_of_solver_record_entail_wit_6 : solver_record_entail_wit_6.
Proof.
  aggressive_pre_process.
  bind_fact ( msat_fp32_nonnegative cla_inc1 ) as H_msat_fp32_nonnegative.
  bind_fact ( record_enqueue_success rec_n rec_F rec_A_arr rec_A_inst M0 Mstage rec_words c Menq ) as
      H_record_enqueue_success.
  destruct H_record_enqueue_success as
    [Henq [Hinv [Hpending [Hseed [Hmodel [Hmodel_cap [Hdecay [Hcapacity Hreuse]]]]]]]].
  assert (Hstats_len :
    Zlength (record_stats_update rec_words (ms_stats Menq)) = 11).
  { rewrite record_stats_update_length__record.
    pose proof (msi_shape Hinv) as Hshape.
    unfold solver_shape in Hshape.
    tauto. }
  pose proof
    (msolver_inv_with_cla_inc_stats__record
       rec_n rec_F rec_A_arr rec_A_inst Menq cla_inc1
       (record_stats_update rec_words (ms_stats Menq))
       Hinv H_msat_fp32_nonnegative Hstats_len) as Hinv_stats.
  assert (Hreuse_finish : minisat_record_reuse M0 rec_words
    (msolver_record_finish Menq rec_words c cla_inc1)).
  { intros Hentry. apply record_finish_base_completion__record.
    exact (Hreuse Hentry). }
  Exists (msolver_record_finish Menq rec_words c cla_inc1).
  unfold record_finish_success.
  unfold msolver_record_finish.
  destruct (Z.eq_dec c 0); [congruence|].
  subst retval.
  pose proof ulnb64_lo64 as Hlo64.
  rewrite !Hlo64.
  sep_apply
    (solver_record_finish_refold__record
       s_pre Menq levels_ptr rec_words cla_inc1 rec_wl).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_record_entail_wit_7_1 : solver_record_entail_wit_7_1.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_finish_success rec_n rec_F rec_A_arr rec_A_inst M0 Menq rec_words c cla_inc1 Mstats ) as
      H_record_finish_success.
  unfold record_output.
  entailer_with ltac:(lia).
  exists cla_inc1.
  exact H_record_finish_success.
Qed.

Lemma proof_of_solver_record_entail_wit_7_2 : solver_record_entail_wit_7_2.
Proof.
  Unfold.
  right. intros.
  subst c.
  bind_fact ( record_enqueue_success rec_n rec_F rec_A_arr rec_A_inst M0 Mstage rec_words 0 Menq ) as
      H_record_enqueue_success.
  unfold record_output, record_finish_success.
  entailer_with ltac:(lia).
  exists (ms_cla_inc Menq).
  destruct H_record_enqueue_success as
    [Henq [Hinv [Hpending [Hseed [Hmodel [Hmodel_cap [Hdecay [Hcapacity Hreuse]]]]]]]].
  split; [ unfold msolver_record_finish;
           destruct (Z.eq_dec 0 0); [reflexivity|congruence] | ].
  exact (conj Hinv (conj Hpending (conj Hseed
    (conj Hmodel (conj Hmodel_cap (conj Hdecay (conj Hcapacity Hreuse))))))).
Qed.

(* ===== solver_record partial_solve wits ===== *)


Lemma proof_of_solver_record_partial_solve_wit_13_pure : solver_record_partial_solve_wit_13_pure.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_enqueue_success rec_n rec_F rec_A_arr rec_A_inst M0 Mstage rec_words c Menq ) as
      H_record_enqueue_success.
  destruct H_record_enqueue_success as
    [Henq [Hinv [Hpending [Hseed [Hmodel [Hmodel_cap [Hdecay [Hcapacity Hreuse]]]]]]]].
  pose proof (msi_cla_inc_nonnegative Hinv) as Hcla_inc.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_record_partial_solve_wit_14_pure : solver_record_partial_solve_wit_14_pure.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_enqueue_success rec_n rec_F rec_A_arr rec_A_inst M0 Mstage rec_words c Menq ) as
      H_record_enqueue_success.
  bind_fact ( record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage ) as H_record_allocated.
  destruct H_record_enqueue_success as
    [Henq [Hinv [Hpending [Hseed [Hmodel [Hmodel_cap [Hdecay [Hcapacity Hreuse]]]]]]]].
  pose proof (msi_learnt_db Hinv) as Hlearnt.
  unfold record_allocated in H_record_allocated.
  destruct H_record_allocated as [Halloc Hrest].
  destruct Halloc as
    [[Hlen [Hczero Hsame]] | [Hlen [Hcne Htrans]]]; [congruence|].
  pose proof
    (clause_new_success_installs_word__record
       rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage Htrans) as Hin_stage.
  assert (Hlearnt_eq : ms_learnt Menq = ms_learnt Mstage).
  { subst Menq. reflexivity. }
  assert (Hin : In c (db_words (ms_learnt Menq))).
  { rewrite Hlearnt_eq. exact Hin_stage. }
  msat_manual_entailer_with ltac:(lia).
Qed.


(* ===== solver_record return wits (1 proofs) ===== *)
Lemma proof_of_solver_record_return_wit_1 : solver_record_return_wit_1.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_output rec_n rec_F rec_A_arr rec_A_inst M0 Menq rec_words c Mout ) as H_record_output.
  destruct H_record_output as [cla_inc Hfinish].
  unfold record_finish_success in Hfinish.
  destruct Hfinish as
    [Hout [Hinv [Hpending [Hseed [Hmodel [Hmodel_cap [Hdecay [Hcapacity Hreuse]]]]]]]].
  unfold solver_record_post_at.
  Left. Exists Mout.
  entailer_with ltac:(lia).
  apply veci_rep_at_rep.
Qed.

(* ===== solver_record which_implies wits (4 proofs) ===== *)
Lemma proof_of_solver_record_which_implies_wit_1 : solver_record_which_implies_wit_1.
Proof.
  Unfold.
  right. intros.
  unfold solver_record_pre_at, veci_rep.
  Intros learnt_ptr.
  match goal with
  | Hpre : record_clause_cert ?n ?F ?M ?words /\ _ |- _ =>
      pose proof (proj1 (proj1 Hpre)) as H_record_nonempty
  end.
  Exists learnt_ptr.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_record_which_implies_wit_2 : solver_record_which_implies_wit_2.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_clause_cert rec_n rec_F M0 rec_words ) as H_record_clause_cert.
  bind_fact ( msolver_inv rec_n rec_F rec_A_arr rec_A_inst M0 ) as H_msolver_inv.
  unfold record_clause_cert, record_ready_cert in H_record_clause_cert.
  destruct H_record_clause_cert as (Hlen & Hwf & Hnd & Hent & Hhead & Hfalse & Hroot).
  pose proof (msi_weak H_msolver_inv) as Hweak.
  pose proof
    (msolver_inv_literal_bound rec_n rec_F rec_A_arr rec_A_inst M0 Hweak) as Hlitbound.
  pose proof (msat_map_lit_var_c_in_range rec_n rec_words Hwf) as Hall.
  pose proof
    (NoDup_Z_bounded_length (map lit_var_c rec_words) rec_n
       (msw_n_range Hweak) Hnd Hall) as Hwords.
  assert (Hwordn : Zlength rec_words <= rec_n).
  { rewrite Zlength_correct. rewrite <- map_length with (f := lit_var_c).
    exact Hwords. }
  rewrite <- (msw_size Hweak) in Hlitbound.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_record_which_implies_wit_3 : solver_record_which_implies_wit_3.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage ) as H_record_allocated.
  pose proof
    (record_allocated_enqueue_input__record
      rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage H_record_allocated) as Hinput.
  sep_apply solver_rep_levels_wl_at_enqueue_focus__record.
  Intros assigns_ptr.
  Exists assigns_ptr.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_record_which_implies_wit_5 : solver_record_which_implies_wit_5.
Proof.
  Unfold.
  right. intros.
  bind_fact ( record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage ) as H_record_allocated.
  pose proof
    (record_enqueue_success_intro__record
      rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage H_record_allocated) as Hsuccess.
  pose proof
    (msolver_inv_record_enqueue__record
      rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage H_record_allocated) as Hinv_enq.
  pose proof (msi_shape Hinv_enq) as Hshape.
  change (solver_shape
    (msolver_enqueue_fresh Mstage (Znth 0 rec_words 0) c
      (record_reason_opt rec_words c))) in Hshape.
  pose proof H_record_allocated as Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hq [Hpending [Hseed [Hmodel Hmodelcap]]]]]]].
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as [_ [_ [_ [_ [Hfresh _]]]]].
  Exists (msolver_record_enqueue Mstage rec_words c).
  split.
  - exact Hsuccess.
  - pose proof
      (enqueue_post_record_refold_wl
        s assigns_ptr levels_ptr
        (Znth 0 rec_words 0) c
        (ms_size Mstage) (ms_cap Mstage) (ms_qtail Mstage)
        (mt_assigns (ms_core Mstage)) (mt_levels (ms_core Mstage))
        (ms_reason_words Mstage) (mt_trail (ms_core Mstage))
        (mt_lim (ms_core Mstage)) (ms_lim_cap Mstage)
        Mstage (record_reason_opt rec_words c) rec_wl) as Hrefold.
    specialize
      (Hrefold eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        eq_refl eq_refl eq_refl Hshape Hfresh).
    exact (Hrefold m H).
Qed.

(* ===== solver_search entail wits (5 proofs) ===== *)
Lemma proof_of_solver_search_entail_wit_3_1 : solver_search_entail_wit_3_1.
Proof.
  unfold solver_search_entail_wit_3_1.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  msat_search_close_conflict_count_nonneg.
Qed.

Lemma proof_of_solver_search_entail_wit_3_2 : solver_search_entail_wit_3_2.
Proof.
  unfold solver_search_entail_wit_3_2.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  msat_search_close_conflict_count_nonneg.
Qed.

Lemma proof_of_solver_search_entail_wit_3_3 : solver_search_entail_wit_3_3.
Proof.
  unfold solver_search_entail_wit_3_3.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  msat_search_close_conflict_count_nonneg.
Qed.

Lemma proof_of_solver_search_entail_wit_8_1 : solver_search_entail_wit_8_1.
Proof.
  aggressive_pre_process;
    msat_search_model_copy_bounds_p1 n F A_arr A_inst Mselected.
Qed.

Lemma proof_of_solver_search_entail_wit_8_2 : solver_search_entail_wit_8_2.
Proof.
  aggressive_pre_process;
    msat_search_model_copy_bounds_p1 n F A_arr A_inst Mselected.
Qed.

(* ===== solver_search partial_solve wits ===== *)
Lemma proof_of_solver_search_partial_solve_wit_2_pure : solver_search_partial_solve_wit_2_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact ( msolver_inv n F A_arr A_inst M0 ) as H_msolver_inv.
  entailer_with ltac:(lia).
  exact (msi_shape H_msolver_inv).
Qed.

Lemma proof_of_solver_search_partial_solve_wit_8_pure : solver_search_partial_solve_wit_8_pure.
Proof.
  unfold solver_search_partial_solve_wit_8_pure.
  unfold stats_starts.
  msat_search_veci_bounds_open_p1; Intros p; msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_partial_solve_wit_10_pure : solver_search_partial_solve_wit_10_pure.
Proof.
  unfold solver_search_partial_solve_wit_10_pure.
  unfold stats_starts.
  Unfold.
  left; intros.
  entailer_with ltac:(lia).
  exact MSatFloatFacts.fp32_search_decay_positive_finite.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_15_pure : solver_search_partial_solve_wit_15_pure.
Proof.
  msat_search_veci_bounds_open_p1; Intros p; msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_partial_solve_wit_20_pure : solver_search_partial_solve_wit_20_pure.
Proof.
  msat_search_veci_bounds_open_p1; Intros learnt_ptr;
    coq_prop_lift; msat_search_close_learnts_db_vec_bounds H.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_21_pure : solver_search_partial_solve_wit_21_pure.
Proof.
  unfold solver_search_partial_solve_wit_21_pure.
  unfold stats_conflicts.
  msat_search_veci_bounds_open_p1; Intros trail_ptr learnt_ptr;
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_search_partial_solve_wit_29_pure : solver_search_partial_solve_wit_29_pure.
Proof.
  unfold solver_search_partial_solve_wit_29_pure.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold.
  left; intros.
  bind_fact ( Forall (lit_wf_c n) words ) as H_Forall.
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationStable A_inst) Manalyze focus ) as
      H_propagation_cancel_ready.
  assert (Hidx : 0 <= 1 < Zlength words) by lia.
  pose proof (Forall_Znth_elim Z (lit_wf_c n) words 0 1 H_Forall Hidx) as Hlit.
  unfold lit_wf_c in Hlit.
  destruct H_propagation_cancel_ready as [Hweak _].
  destruct Hweak as [_ Hweak].
  pose proof (msw_size Hweak) as Hsize.
  pose proof (msw_shape Hweak) as Hshape.
  unfold solver_shape in Hshape.
  destruct Hshape as [_ [_ [Htwon _]]].
  destruct Hlit as [Hlo Hhi].
  apply derivable1s_coq_prop_andp_r.
  - apply (derivable1s_coq_prop_r _).
    replace (1 - 0) with 1 by lia.
    lia.
  - replace (1 - 0) with 1 by lia.
    lia.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_49_pure : solver_search_partial_solve_wit_49_pure.
Proof.
  unfold solver_search_partial_solve_wit_49_pure.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold; left; intros; msat_search_backjump_model_nil_p1 n F A_arr A_inst Mcur Mback words.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_50_pure : solver_search_partial_solve_wit_50_pure.
Proof.
  unfold solver_search_partial_solve_wit_50_pure.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold; left; intros; msat_search_backjump_model_nil_p1 n F A_arr A_inst Mcur Mback words.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_51_pure : solver_search_partial_solve_wit_51_pure.
Proof.
  unfold solver_search_partial_solve_wit_51_pure.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold; left; intros; msat_search_backjump_model_nil_p1 n F A_arr A_inst Mcur Mback words.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_55_pure : solver_search_partial_solve_wit_55_pure.
Proof.
  unfold solver_search_partial_solve_wit_55_pure.
  unfold stats_conflicts, stats_set_conflicts.
  Unfold; left; intros; msat_search_backjump_model_nil_p1 n F A_arr A_inst Mcur Mback words.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_97_pure : solver_search_partial_solve_wit_97_pure.
Proof.
  Unfold; right; intros; unfold veci_rep, veci_rep_at; Intros learnt_ptr;
    coq_prop_lift; msat_search_close_vec_bounds_rev_p1 H.
Qed.


Lemma proof_of_solver_search_partial_solve_wit_154_pure : solver_search_partial_solve_wit_154_pure.
Proof.
  unfold solver_search_partial_solve_wit_154_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_155_pure : solver_search_partial_solve_wit_155_pure.
Proof.
  unfold solver_search_partial_solve_wit_155_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_156_pure : solver_search_partial_solve_wit_156_pure.
Proof.
  unfold solver_search_partial_solve_wit_156_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_157_pure : solver_search_partial_solve_wit_157_pure.
Proof.
  unfold solver_search_partial_solve_wit_157_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_158_pure : solver_search_partial_solve_wit_158_pure.
Proof.
  unfold solver_search_partial_solve_wit_158_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_159_pure : solver_search_partial_solve_wit_159_pure.
Proof.
  unfold solver_search_partial_solve_wit_159_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_160_pure : solver_search_partial_solve_wit_160_pure.
Proof.
  unfold solver_search_partial_solve_wit_160_pure.
  unfold stats_decisions.
  Unfold; right; LLM_pre_process ltac:(lia).
  msat_search_close_activity_length_from_heap activity_ptr Mdb Hactivity_len.
Qed.

(* ===== solver_search which_implies wits (8 proofs) ===== *)
Lemma proof_of_solver_search_which_implies_wit_6 : solver_search_which_implies_wit_6.
Proof.
  right. intros.
  bind_fact ( msolver_inv n F A_arr A_inst M0 ) as H_msolver_inv.
  bind_fact ( ms_capacity_root_propagation_pending M0 = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow M0 ) as H_msolver_seed_shadow.
  bind_fact ( msat_fp32_positive_finite cd ) as H_msat_fp32_positive_finite.
  rename M0 into Mbase.
  set (Mlive := msolver_runtime_update Mbase (@nil Z) (ms_var_inc Mbase) vd
    (ms_cla_inc Mbase) cd (ms_progress Mbase)
    (replace_Znth 0 starts_now (ms_stats Mbase))).
  pose proof (msi_shape H_msolver_inv) as HshapeM.
  assert (Hshape_live : solver_shape Mlive).
  { unfold solver_shape in HshapeM |- *.
    unfold Mlive, msolver_runtime_update. cbn -[replace_Znth].
    rewrite Zlength_replace_Znth. tauto. }
  assert (Hinv_live : msolver_inv n F A_arr A_inst Mlive).
  { destruct H_msolver_inv. constructor; cbn [Mlive msolver_runtime_update] in *;
      [destruct msi_weak; constructor; cbn [Mlive msolver_runtime_update] in *; assumption
      | assumption | assumption | assumption | assumption ]. }
  assert (Hprop_live :
      solver_propagation_inv n F A_arr (PropagationStable A_inst) Mlive).
  { unfold solver_propagation_inv.
    split.
    - cbn [Mlive msolver_runtime_update]. exact H_ms_capacity_root_propagation_pending.
    - apply msolver_inv_propagation_of_strong. exact Hinv_live. }
  assert (Hseed_live : msolver_seed_shadow Mlive).
  { cbn [Mlive msolver_runtime_update]. exact H_msolver_seed_shadow. }
  assert (Hmodel_live : ms_model Mlive = @nil Z).
  { cbn [Mlive msolver_runtime_update]. reflexivity. }
  assert (Hdecay_live : msat_fp32_positive_finite (ms_cla_decay Mlive)).
  { cbn [Mlive msolver_runtime_update]. exact H_msat_fp32_positive_finite. }
  assert (Hstats_len : Zlength (ms_stats Mbase) = 11).
  { unfold solver_shape in HshapeM. tauto. }

  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hstats_live :
      (&(s # "solver_t" ->ₛ "stats" .ₛ "starts") # UInt64 |-> starts_now) **
      stats_without_starts_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mbase)
      |-- stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mlive)).
  { change (ms_stats Mlive) with (replace_Znth 0 starts_now (ms_stats Mbase)).
    assert (Hstarts_addr :
        &(s # "solver_t" ->ₛ "stats" .ₛ "starts") =
        &(stats_ptr # "stats_t" ->ₛ "starts"))
      by (unfold stats_ptr; csimpl; reflexivity).
    rewrite Hstarts_addr.
    exact (msat_stats_starts_refold_p1 stats_ptr (ms_stats Mbase) starts_now
      Hstats_len). }

  assert (Hscalars_live :
      solver_scalars_rep s Mbase |-- solver_scalars_rep s Mlive).
  { unfold solver_scalars_rep. cbn [Mlive msolver_runtime_update]. entailer_with ltac:(lia). }

  assert (Hfp_live :
      (&(s # "solver_t" ->ₛ "var_decay") # Double |-> vd) **
      (&(s # "solver_t" ->ₛ "cla_decay") # Float |-> cd) **
      solver_fp_without_decays_rep s Mbase |-- solver_fp_rep s Mlive).
  { unfold solver_fp_without_decays_rep, solver_fp_rep, Mlive.
    cbn. entailer_with ltac:(lia). }

  assert (Hvecs_live :
      veci_rep &(s # "solver_t" ->ₛ "model") (@nil Z) (ms_model_cap Mbase) **
      solver_vecs_without_model_rep s Mbase |-- solver_vecs_rep s Mlive).
  { unfold solver_vecs_without_model_rep, solver_vecs_rep, Mlive.
    cbn. entailer_with ltac:(lia). }

  assert (Hlevels_live :
      solver_levels_slice_at s Mbase levels |-- solver_levels_slice_at s Mlive levels).
  { unfold solver_levels_slice_at. cbn [Mlive msolver_runtime_update]. entailer_with ltac:(lia). }

  rewrite Zsublist_nil by lia.
  unfold solver_search_loop.
  Exists Mlive. Exists (@nil Z). Exists 4.
  apply derivable1s_coq_prop_andp_r.
  2: { exact (conj eq_refl (conj (fun Hbase => Hbase)
      (conj Hprop_live (conj Hseed_live (conj Hmodel_live Hdecay_live))))). }
  sep_apply_l_atomic (msat_learnt_clause_veci_fold_p1 learnt_ptr).
  cancel.
  unfold solver_search_init_frame_at, solver_search_bundle_at, solver_search_payload, solver_payload_cells.
  pose (stable_payload := solver_payload_cells s Mbase search_wl).
  fold (solver_payload_cells s Mbase search_wl).
  fold stable_payload.
  assert (Hstable_payload : stable_payload = stable_payload) by reflexivity.
  unfold stable_payload at 2 in Hstable_payload.
  unfold solver_payload_cells in Hstable_payload.
  clearbody stable_payload.
  Intros.
  sep_apply_l_atomic Hscalars_live.
  sep_apply_l_atomic Hfp_live.
  sep_apply_l_atomic Hvecs_live.
  sep_apply_l_atomic Hstats_live.
  sep_apply_l_atomic Hlevels_live.
  assert (Hassemble :
      solver_scalars_rep s Mlive ** solver_fp_rep s Mlive **
      solver_vecs_rep s Mlive **
      stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mlive) **
      stable_payload |-- solver_cancel_owned s Mlive search_wl).
  { rewrite Hstable_payload. unfold solver_cancel_owned.
    Intros act asg opos rsn trl tgs.
    Exists act asg opos rsn trl tgs.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, Mlive. cbn.
    entailer_with ltac:(int_auto). }
  sep_apply_l_atomic Hassemble.
  unfold solver_rep_levels_wl_at.
  apply derivable1s_coq_prop_andp_r.
  2: { exact Hshape_live. }
  unfold solver_cancel_owned.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  cancel.
Qed.

Lemma proof_of_solver_search_which_implies_wit_7 : solver_search_which_implies_wit_7.
Proof.
  right. intros.
  unfold solver_search_loop, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_rep_assigns_levels_at,
    solver_rep_at.
  Intros M words cap.
  Intros act asg opos rsn trl tgs.
  Exists words cap asg M.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_8 : solver_search_which_implies_wit_8.
Proof.
  right. intros.
  unfold solver_propagate_pre.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_9 : solver_search_which_implies_wit_9.
Proof.
  right. intros.
  bind_fact ( ms_model Mcur = nil ) as H_ms_model.
  unfold solver_propagate_post.
  apply derivable1_orp_elim.
  - apply derivable1_orp_elim.
    + Intros Mbad.
      entailer_with ltac:(lia).
    + Intros Mbad p focus C.
      entailer_with ltac:(lia).
  - unfold solver_propagation_capacity_raw.
    entailer_with ltac:(lia); cancel.
    Intros Mcap.
    match goal with
    | Hpost : solver_propagation_inv _ _ _ _ Mcap /\ _ |- _ =>
        destruct Hpost as
          [Hinv [Hcaller [Hreuse [Hseed [Hexhausted [Hwatch Hscan]]]]]]
    end.
    destruct Hcaller as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
    lazymatch goal with
    | Hentry : solver_search_reuse ?entry Mcur |- _ =>
        assert (Hreuse_cap : solver_search_reuse entry Mcap)
          by (intro Hbase; exact (proj1 Hreuse (Hentry Hbase)))
    end.
    assert (Hmodel_nil : ms_model Mcap = nil)
      by (rewrite Hmodel; exact H_ms_model).
    Exists Mcap.
    unfold solver_internal_capacity_ready.
    sep_apply (solver_propagation_capacity_rep_at_refold
      s Mcap assigns_ptr levels search_wl).
    unfold solver_rep_assigns_levels_at, solver_rep_levels_wl_at,
      solver_rep_at, solver_cancel_owned.
    Intros act opos rsn trl tgs.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
    Exists act assigns_ptr opos rsn trl tgs.
    unfold propagation_caller_frame.
    msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_10 : solver_search_which_implies_wit_10.
Proof.
  right. intros.
  bind_fact ( ms_model Mcur = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mcur) ) as H_msat_fp32_positive_finite.
  unfold solver_propagate_post.
  apply derivable1_orp_elim.
  - apply derivable1_orp_elim.
    + Intros Mbad.
      entailer_with ltac:(lia).
    + Intros Mconf p focus C.
      match goal with
      | Hpost : propagation_cancel_ready _ _ _ _ Mconf _ /\ _ |- _ =>
          destruct Hpost as
            [Hcancel [Hcaller [Hwatch [Hresident [Hseed [Hcert Hptr]]]]]]
      end.
      destruct Hcaller as [Hlim [Hroot [Hmodel [Hdecay Hcap]]]].
      lazymatch goal with
      | Hentry : solver_search_reuse ?entry Mcur |- _ =>
          assert (Hreuse_conflict : minisat_base_watch_completed entry ->
              minisat_watch_conflict_ready n Mconf)
            by (intro Hbase; exact (Hwatch (Hentry Hbase)))
      end.
      assert (Hmodel_nil : ms_model Mconf = nil)
        by (rewrite Hmodel; exact H_ms_model).
      assert (Hdecay_finite :
          msat_fp32_positive_finite (ms_cla_decay Mconf))
        by (rewrite Hdecay; exact H_msat_fp32_positive_finite).
      assert (Hdecay_same :
          msat_fp32_same (ms_cla_decay Mconf) (ms_cla_decay Mcur))
        by (unfold msat_fp32_same; exact Hdecay).
      Exists p C focus Mconf.
      entailer_with ltac:(lia).
  - unfold solver_propagation_capacity_raw.
    Intros Mbad.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_12 : solver_search_which_implies_wit_12.
Proof.
  left. intros.
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationStable A_inst) Mconf focus ) as H_propagation_cancel_ready.
  bind_fact ( propagation_conflict_cert n F Mconf Cconf ) as H_propagation_conflict_cert.
  bind_fact ( ms_model Mconf = nil ) as H_ms_model.
  unfold solver_search_conflict_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  Intros act asg opos rsn trl tgs.
  assert (Hsw : solver_propagation_weak n F A_arr
      (PropagationStable A_inst) Mconf) by exact (proj1 H_propagation_cancel_ready).
  assert (Hpending : ms_capacity_root_propagation_pending Mconf = 0)
    by exact (proj1 Hsw).
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mconf)
    by exact (proj2 Hsw).
  assert (Hlevel : prop_level (ms_core Mconf))
    by exact (proj1 (proj2 H_propagation_cancel_ready)).
  assert (Hroot : solver_at_root Mconf).
  { unfold solver_at_root. lia. }
  assert (Hcancel : cancel_bound_ready Mconf 0).
  { unfold cancel_bound_ready.
    destruct (Z_le_dec (Zlength (mt_lim (ms_core Mconf))) 0) as [Hlen|Hlen].
    - left; exact Hlen.
    - right.
      assert (Hidx : 0 <= 0 < Zlength (mt_lim (ms_core Mconf))) by lia.
      exact (Forall_Znth_elim _ _ _ 0 0 Hlevel Hidx). }
  assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)).
  { eapply unsat_endgame_at_root.
    - exact Hweak.
    - exact Hroot.
    - exact (proj1 H_propagation_conflict_cert).
    - exact (proj1 (proj2 H_propagation_conflict_cert)).
    - exact (proj1 (proj2 (proj2 H_propagation_conflict_cert))). }
  set (Mrootconf :=
    msolver_with_cla_inc_stats Mconf (ms_cla_inc Mconf)
      (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  assert (Hshape_root : solver_shape Mrootconf).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn.
    pose proof (msw_shape Hweak) as Hshape.
    assert (Hstats_len :
        Zlength (replace_Znth 4 conflicts_now (ms_stats Mconf)) = 11).
    { rewrite Zlength_replace_Znth.
      unfold solver_shape in Hshape; tauto. }
    unfold solver_shape in Hshape |- *.
    tauto. }
  assert (Hweak_root : msolver_inv_weak n F A_arr A_inst Mrootconf).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn.
    destruct Hweak.
    constructor; try assumption. }
  assert (Hroot_root : solver_at_root Mrootconf).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact Hroot. }
  assert (Hcancel_root : cancel_bound_ready Mrootconf 0).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact Hcancel. }
  assert (Hpending_root : ms_capacity_root_propagation_pending Mrootconf = 0).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact Hpending. }
  assert (Hmodel_root : ms_model Mrootconf = @nil Z).
  { unfold Mrootconf, msolver_with_cla_inc_stats; cbn; exact H_ms_model. }
  bind_fact (msolver_seed_shadow Mconf) as Hseed_conf.
  bind_fact (minisat_resident_false_clause Mconf) as Hresident_conf.
  assert (Hready_root : propagation_cancel_ready n F A_arr
      (PropagationStable A_inst) Mrootconf focus).
  { unfold propagation_cancel_ready. split.
    - split; [exact Hpending_root | exact Hweak_root].
    - unfold Mrootconf, msolver_with_cla_inc_stats; cbn.
      exact (proj2 H_propagation_cancel_ready). }
  lazymatch goal with
  | Hwatch : minisat_base_watch_completed ?entry ->
      minisat_watch_conflict_ready n Mconf |- _ =>
      assert (Hreuse_root : minisat_base_watch_completed entry ->
          solver_search_conflict_reuse n F A_arr A_inst Mrootconf)
        by (intro Hbase; split;
            [change (msolver_seed_shadow Mconf); exact Hseed_conf |
             left; exists focus; split; [exact Hready_root |]; split;
             [change (minisat_watch_conflict_ready n Mconf); exact (Hwatch Hbase) |
              change (minisat_resident_false_clause Mconf); exact Hresident_conf]])
  end.
  assert (Hstats_base_len : Zlength (ms_stats Mconf) = 11).
  { pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape; tauto. }
  assert (Hstats_root_len :
      Zlength (replace_Znth 4 conflicts_now (ms_stats Mconf)) = 11).
  { rewrite Zlength_replace_Znth; exact Hstats_base_len. }
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hconflicts_addr :
      &(s # "solver_t" ->ₛ "stats" .ₛ "conflicts") =
      &(stats_ptr # "stats_t" ->ₛ "conflicts"))
    by (unfold stats_ptr; csimpl; reflexivity).
  assert (Hstats_refold :
      (&(stats_ptr # "stats_t" ->ₛ "conflicts") # UInt64
          |-> conflicts_now) **
      stats_without_conflicts_rep stats_ptr (ms_stats Mconf)
      |-- stats_rep stats_ptr
          (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  { unfold stats_without_conflicts_rep, stats_rep.
    unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
      stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
      stats_learnts_literals, stats_max_literals, stats_tot_literals.
    rewrite Zlength_replace_Znth.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite !Znth_replace_Znth_Diff by lia.
    entailer_with ltac:(lia). }
  Exists Mrootconf.
  unfold Mrootconf.
  rewrite scalars_rep_cla_inc_stats_eq, vecs_rep_cla_inc_stats_eq, fp_rep_cla_inc_stats_eq.
  unfold msolver_with_cla_inc_stats.
  cbn.
  Exists act asg opos rsn trl tgs.
  rewrite Hconflicts_addr.
  fold stats_ptr.
  entailer_with ltac:(lia).
  sep_apply Hstats_refold.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_13 : solver_search_which_implies_wit_13.
Proof.
  unfold solver_search_which_implies_wit_13.
  unfold stats_set_conflicts.
  left. intros.
  bind_fact ( propagation_cancel_ready n F A_arr (PropagationStable A_inst) Mconf focus ) as H_propagation_cancel_ready.
  bind_fact ( propagation_conflict_cert n F Mconf Cconf ) as H_propagation_conflict_cert.
  bind_fact ( conflict_ptr_denotes Mconf p Cconf ) as H_conflict_ptr_denotes.
  bind_fact ( msolver_seed_shadow Mconf ) as H_msolver_seed_shadow.
  bind_fact ( ms_model Mconf = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mconf) ) as H_msat_fp32_positive_finite.
  bind_fact ( msat_fp32_same (ms_cla_decay Mconf) (ms_cla_decay Mcur) ) as H_msat_fp32_same.
  pose proof H_propagation_cancel_ready as Hcancel0.
  destruct H_propagation_cancel_ready as
    [Hsw [Hlevel [Hfocus_wf [Hprocessed [Hfocus_level [Hfrontier
      [Hheap [Hcovers Hreasonless]]]]]]]].
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mconf)
    by exact (proj2 Hsw).
  set (Manalyze :=
    msolver_with_cla_inc_stats Mconf (ms_cla_inc Mconf)
      (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  assert (Hequiv : analysis_core_equiv Mconf Manalyze).
  { unfold Manalyze, msolver_with_cla_inc_stats, analysis_core_equiv.
    cbn. repeat split; reflexivity. }
  assert (Hshape_analyze : solver_shape Manalyze).
  { pose proof (msw_shape Hweak) as Hshape0.
    unfold Manalyze, msolver_with_cla_inc_stats, solver_shape.
    unfold solver_shape in Hshape0. cbn.
    rewrite Zlength_replace_Znth. tauto. }
  assert (Hweak_analyze : msolver_inv_weak n F A_arr A_inst Manalyze).
  { pose proof Hweak as Hweak0. destruct Hweak0.
    constructor; cbn in *; assumption. }
  assert (Hsw_analyze : solver_propagation_weak n F A_arr
      (PropagationStable A_inst) Manalyze).
  { unfold solver_propagation_weak in Hsw |- *. cbn in Hsw |- *.
    split; [exact (proj1 Hsw) | exact Hweak_analyze]. }
  assert (Hcancel_analyze : propagation_cancel_ready n F A_arr
      (PropagationStable A_inst) Manalyze focus).
  { unfold propagation_cancel_ready.
    split; [exact Hsw_analyze |].
    unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    split; [exact Hlevel |]. split; [exact Hfocus_wf |].
    split; [exact Hprocessed |]. split; [exact Hfocus_level |].
    split; [exact Hfrontier |]. split; [exact Hheap |].
    split; [exact Hcovers | exact Hreasonless]. }
  assert (Hanalysis : analysis_cancel_ready n F A_arr
      (PropagationStable A_inst) Manalyze focus).
  { unfold analysis_cancel_ready.
    exists Mconf.
    split; [exact Hcancel0 |]. split; [exact Hequiv |].
    unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    split; [exact Hheap |]. split; [exact Hcovers |].
    split; [exact Hreasonless |]. split; [exact Hfocus_level |].
    exact (msw_cla_inc_nonnegative Hweak). }
  assert (Hcert : propagation_conflict_cert n F Manalyze Cconf).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    unfold propagation_conflict_cert in H_propagation_conflict_cert |- *.
    exact H_propagation_conflict_cert. }
  assert (Hptr : conflict_ptr_denotes Manalyze p Cconf).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    unfold conflict_ptr_denotes in H_conflict_ptr_denotes |- *.
    exact H_conflict_ptr_denotes. }
  assert (Hseed : msolver_seed_shadow Manalyze).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_msolver_seed_shadow. }
  assert (Hmodel : ms_model Manalyze = @nil Z).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_ms_model. }
  assert (Hfinite : msat_fp32_positive_finite (ms_cla_decay Manalyze)).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_msat_fp32_positive_finite. }
  assert (Hsame : msat_fp32_same
      (ms_cla_decay Manalyze) (ms_cla_decay Mcur)).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact H_msat_fp32_same. }
  assert (Hroot_lt :
      ms_root_level Manalyze < Zlength (mt_lim (ms_core Manalyze))).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    pose proof (msw_root_range Hweak); lia. }
  lazymatch goal with
  | Hwatch : minisat_base_watch_completed ?entry ->
      minisat_watch_conflict_ready n Mconf |- _ =>
      assert (Hreuse_analyze : solver_search_reuse entry Manalyze)
  end.
  { intro Hbase.
    lazymatch goal with
    | Hwatch : minisat_base_watch_completed ?entry ->
        minisat_watch_conflict_ready n Mconf |- _ =>
        destruct (Hwatch Hbase) as [watch_focus [Hwatch_level Hexcept]]
    end.
    pose proof (level_of_msolver_view_levels__analyze n Mconf
      (lit_var_c watch_focus) (Zlength (mt_lim (ms_core Mconf)))
      (msw_trail_wf Hweak) Hwatch_level) as Hwatch_cell.
    change (minisat_base_watch_completed Mconf).
    apply (minisat_base_exception_above_zero__api_reentry Mconf watch_focus).
    - pose proof (msw_root_range Hweak). unfold Manalyze in Hroot_lt.
      cbn in Hroot_lt. lia.
    - exact Hexcept. }
  destruct (msw_tags_clear Hweak) as [Hzeros Htagged0].
  assert (Htags_len : Zlength (ms_tags Mconf) = n).
  { pose proof (msw_shape Hweak) as Hshape.
    pose proof (msw_size Hweak) as Hsize.
    unfold solver_shape in Hshape; lia. }
  assert (Hlen_nat : length (ms_tags Mconf) = Z.to_nat n).
  { apply Nat2Z.inj.
    rewrite <- Zlength_correct.
    rewrite Htags_len.
    rewrite Z2Nat.id by exact (msw_n_range Hweak).
    reflexivity. }
  assert (Htags : ms_tags Manalyze = repeat_Z 0 n).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn.
    unfold repeat_Z.
    rewrite <- Hlen_nat.
    apply msat_forall_zero_repeat_p1. exact Hzeros. }
  assert (Htagged : ms_tagged Manalyze = @nil Z).
  { unfold Manalyze, msolver_with_cla_inc_stats; cbn; exact Htagged0. }
  assert (Hlit_bound : 2 * n <= INT_MAX).
  { pose proof (msolver_inv_literal_bound n F A_arr A_inst Mconf Hweak).
    rewrite <- (msw_size Hweak) in H. exact H. }
  assert (Hstats_base_len : Zlength (ms_stats Mconf) = 11).
  { pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape; tauto. }
  set (stats_ptr := &(s # "solver_t" ->ₛ "stats")).
  assert (Hconflicts_addr :
      &(s # "solver_t" ->ₛ "stats" .ₛ "conflicts") =
      &(stats_ptr # "stats_t" ->ₛ "conflicts"))
    by (unfold stats_ptr; csimpl; reflexivity).
  assert (Hstats_refold :
      (&(stats_ptr # "stats_t" ->ₛ "conflicts") # UInt64
          |-> conflicts_now) **
      stats_without_conflicts_rep stats_ptr (ms_stats Mconf)
      |-- stats_rep stats_ptr
          (replace_Znth 4 conflicts_now (ms_stats Mconf))).
  { unfold stats_without_conflicts_rep, stats_rep.
    unfold stats_starts, stats_decisions, stats_propagations, stats_inspects,
      stats_conflicts, stats_clauses, stats_clauses_literals, stats_learnts,
      stats_learnts_literals, stats_max_literals, stats_tot_literals.
    rewrite Zlength_replace_Znth.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite !Znth_replace_Znth_Diff by lia.
    entailer_with ltac:(lia). }
  assert (Hlearnt_frame :
      veci_rep (&("learnt_clause")) (@nil Z) learnt_cap |--
      “ 0 <= learnt_cap <= INT_MAX ” &&
      veci_rep (&("learnt_clause")) (@nil Z) learnt_cap).
  { unfold veci_rep, veci_rep_at.
    Intros lp. Exists lp. entailer_with ltac:(lia). }
  rewrite Zsublist_nil by lia.
  sep_apply Hlearnt_frame.
  unfold solver_search_conflict_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_analyze_pre, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  Intros act asg opos rsn trl tgs.
  Exists Manalyze.
  unfold Manalyze.
  rewrite scalars_rep_cla_inc_stats_eq, vecs_rep_cla_inc_stats_eq, fp_rep_cla_inc_stats_eq.
  unfold msolver_with_cla_inc_stats.
  cbn.
  Exists act asg opos rsn trl tgs.
  rewrite Hconflicts_addr.
  fold stats_ptr.
  entailer_with ltac:(lia).
  sep_apply Hstats_refold.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_14 : solver_search_which_implies_wit_14.
Proof.
  right.
  intros M A_inst A_arr F n search_wl Mcur focus Manalyze levels s; intros.
  bind_fact ( ms_model Manalyze = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Manalyze) ) as H_msat_fp32_positive_finite.
  bind_fact ( msat_fp32_same (ms_cla_decay Manalyze) (ms_cla_decay Mcur) ) as H_msat_fp32_same.
  bind_fact (solver_search_reuse M Manalyze) as Hentry_reuse.
  unfold solver_analyze_post.
  Intros M' words cap_after backjump.
  destruct H as
    [Hanalysis [Hseed [Hmodel_eq [Hcap_eq [Hreuse [Hdecay_eq [Hlen [Hcap
      [Hwords [Hnodup [Hclause [Hbackjump [Htags Htagged]]]]]]]]]]]]].
  assert (Hresult_reuse : solver_search_reuse M M').
  { unfold solver_search_reuse in *. intro Hentry.
    apply Hreuse. exact (Hentry_reuse Hentry). }
  destruct (analysis_cancel_ready_reason_core
    n F A_arr (PropagationStable A_inst) M' focus Hanalysis)
    as [HsizeA [Hreasons Hbinary]].
  assert (Hinc : msat_fp32_nonnegative (ms_cla_inc M')).
  { pose proof Hanalysis as Hanalysis0.
    destruct Hanalysis0 as
      [M0 [_ [_ [_ [_ [_ [_ Hinc]]]]]]].
    exact Hinc. }
  assert (Hmodel : ms_model M' = @nil Z).
  { rewrite Hmodel_eq. exact H_ms_model. }
  assert (Hfinite : msat_fp32_positive_finite (ms_cla_decay M')).
  { rewrite Hdecay_eq. exact H_msat_fp32_positive_finite. }
  assert (Hsame : msat_fp32_same
      (ms_cla_decay M') (ms_cla_decay Mcur)).
  { rewrite Hdecay_eq. exact H_msat_fp32_same. }
  assert (Hvar_range :
      0 <= lit_var_c (Znth 1 words 0) /\
      lit_var_c (Znth 1 words 0) < ms_size M').
  { destruct (Z.eq_dec (Zlength words) 1) as [Hone|Hgt].
    - assert (Hwf0 : lit_wf_c n (Znth 0 words 0)).
      { apply (Forall_Znth_elim Z (lit_wf_c n) words 0 0 Hwords).
        lia. }
      assert (Hnpos : 0 < n) by (destruct Hwf0; lia).
      assert (Hdefault : Znth 1 words 0 = 0).
      { apply znth_out_of_bounds; lia. }
      rewrite Hdefault.
      unfold lit_var_c.
      cbn.
      rewrite <- HsizeA.
      lia.
    - assert (Hidx : 0 <= 1 < Zlength words) by lia.
      assert (Hwf1 : lit_wf_c n (Znth 1 words 0)).
      { apply (Forall_Znth_elim Z (lit_wf_c n) words 0 1 Hwords).
        exact Hidx. }
      pose proof (lit_var_c_in_range n (Znth 1 words 0) Hwf1) as Hv.
      rewrite <- HsizeA.
      exact Hv. }
  replace (1 - 0) with 1 by lia.
  Exists cap_after.
  Exists backjump.
  Exists words.
  Exists M'.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_search return wits (7 proofs) ===== *)
Lemma proof_of_solver_search_return_wit_2 : solver_search_return_wit_2.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Left. Left. Right.
  Exists Msimplify_unsat.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_3 : solver_search_return_wit_3.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Left. Left. Right.
  Exists Msimplify_unsat.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_4 : solver_search_return_wit_4.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Right.
  Exists Msimplify_cap.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_5 : solver_search_return_wit_5.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Right.
  Exists Msimplify_cap.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_6 : solver_search_return_wit_6.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Left. Right.
  Exists Mrestart.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_8 : solver_search_return_wit_8.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Right.
  Exists Mrecord_cap.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_return_wit_9 : solver_search_return_wit_9.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Right.
  Exists Mrecord_cap.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_simplify entail wits (2 proofs) ===== *)
Lemma proof_of_solver_simplify_entail_wit_8 : solver_simplify_entail_wit_8.
Proof.
  Unfold.
  left. intros.
  bind_fact ( solver_simplify_compaction_step smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec type Mcur_2 words_2 i jcur Mnext words_next j )
      as H_solver_simplify_compaction_step.
  Exists asg_2. Exists words_next. Exists Mnext.
  unfold solver_simplify_compaction_step in H_solver_simplify_compaction_step.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_simplify_entail_wit_9 : solver_simplify_entail_wit_9.
Proof.
  Unfold. left. intros.
  bind_fact ( Zlength words <= solver_selected_cap type Mcur ) as H_Zlength.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( Zlength (mt_lim (ms_core Mcur)) = 0 ) as H_Zlength_2.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  unfold solver_simplify_outer_loop. Exists Mcur.
  unfold msat_fp32_same in *.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [[Htype | Htype] [Hj [Hji [Hi Hmap]]]].
  - subst type.
    assert (Htail : sublist i (Zlength words) words = z_nil).
    { unfold z_nil. apply Zsublist_nil. lia. }
    assert (Hdbw : db_words (solver_selected_db 0 Mcur) = sublist 0 j words).
    { unfold db_words. rewrite Hmap, Htail. unfold z_nil.
      rewrite app_nil_r. reflexivity. }
    assert (Hlimnil : mt_lim (ms_core Mcur) = (@nil Z)) by
      (apply Zlength_nil_inv; exact H_Zlength_2).
    pose proof (msa_shape (msas_weak H_msolver_inv)) as Hshape.
    subst cs.
    assert (Hcapb : 0 < solver_selected_cap 0 Mcur <= INT_MAX) by lia.
    assert (Hlenb : 0 <= Zlength (sublist 0 j words) <= solver_selected_cap 0 Mcur)
      by (rewrite PreH1; lia).
    sep_apply (msat_vecp_cells_rep (solver_selected_vec s_pre 0) cls
      (sublist 0 j words) (solver_selected_cap 0 Mcur) Hlenb Hcapb).
    rewrite <- Hdbw.
    unfold z_nil.
    sep_apply (solver_rep_reasons_simplify_close_0__simplify
      s_pre Mcur reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec asg Hlimnil Hshape).
    repeat sep_apply store_ptr_undef_store_ptr.
    repeat sep_apply store_int_undef_store_int.
    entailer_with ltac:(lia).
  - subst type.
    assert (Htail : sublist i (Zlength words) words = z_nil).
    { unfold z_nil. apply Zsublist_nil. lia. }
    assert (Hdbw : db_words (solver_selected_db 1 Mcur) = sublist 0 j words).
    { unfold db_words. rewrite Hmap, Htail. unfold z_nil.
      rewrite app_nil_r. reflexivity. }
    assert (Hlimnil : mt_lim (ms_core Mcur) = (@nil Z)) by
      (apply Zlength_nil_inv; exact H_Zlength_2).
    pose proof (msa_shape (msas_weak H_msolver_inv)) as Hshape.
    subst cs.
    assert (Hcapb : 0 < solver_selected_cap 1 Mcur <= INT_MAX) by lia.
    assert (Hlenb : 0 <= Zlength (sublist 0 j words) <= solver_selected_cap 1 Mcur)
      by (rewrite PreH1; lia).
    sep_apply (msat_vecp_cells_rep (solver_selected_vec s_pre 1) cls
      (sublist 0 j words) (solver_selected_cap 1 Mcur) Hlenb Hcapb).
    rewrite <- Hdbw.
    unfold z_nil.
    sep_apply (msat_simplify_close_learnt
      s_pre Mcur reasons levels_ptr_solver_simplify_spec smp_wl_solver_simplify_spec asg Hlimnil Hshape).
    repeat sep_apply store_ptr_undef_store_ptr.
    repeat sep_apply store_int_undef_store_int.
    msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_simplify partial_solve wits ===== *)


Lemma proof_of_solver_simplify_partial_solve_wit_20_pure : solver_simplify_partial_solve_wit_20_pure.
Proof.
  Unfold. left. intros.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  pose proof H_solver_simplify_db_compaction_inv as Hcompact.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [_ [Hj [Hji _]]].
  assert (Hi : i < Zlength words) by lia. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_partial_solve_wit_28_pure : solver_simplify_partial_solve_wit_28_pure.
Proof.
  Unfold. left. intros.
  bind_fact ( db_lookup (solver_selected_db type Mcur) (Znth (i - 0) words 0) co ) as H_db_lookup.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  unfold db_lookup in H_db_lookup.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [Htype _].
  assert (Hin : In (Znth (i - 0) words 0, co) (msolver_db Mcur)).
  { eapply solver_selected_db_in; [exact Htype | exact H_db_lookup]. }
  pose proof (db_wf_even _ _ _ _ (msa_db_wf (msas_weak H_msolver_inv)) Hin) as Heven.
  pose proof (db_wf_ptr_pos _ _ _ _ (msa_db_wf (msas_weak H_msolver_inv)) Hin) as Hpos.
  apply clause_ptr_mod2 in Heven. entailer_with ltac:(lia).
  rewrite Z.rem_mod_nonneg by lia. exact Heven.
Qed.

Lemma proof_of_solver_simplify_partial_solve_wit_24_pure : solver_simplify_partial_solve_wit_24_pure.
Proof.
  Unfold. left. intros.
  bind_fact ( Forall (lit_wf_c (ms_size Mcur)) (co_lits co) ) as H_Forall.
  rewrite Forall_forall in H_Forall.
  assert (Hlit : lit_wf_c (ms_size Mcur) (Znth (0 - 0) (co_lits co) 0)).
  { apply H_Forall. apply Znth_In. lia. }
  unfold lit_wf_c in Hlit. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_simplify_partial_solve_wit_39_pure : solver_simplify_partial_solve_wit_39_pure.
Proof.
  Unfold. left. intros.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [_ [Hj [Hji [Hi _]]]]. msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_simplify return wits (1 proofs) ===== *)
Lemma proof_of_solver_simplify_return_wit_1 : solver_simplify_return_wit_1.
Proof.
  Unfold.
  left. intros.
  bind_fact ( solver_simplify_finish_transition smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec Mdone
      (MiniSatTarget.uint64_sum_to_int (stats_clauses_literals (ms_stats Mdone))
        (stats_learnts_literals (ms_stats Mdone))) Mfinish ) as H_solver_simplify_finish_transition.
  bind_fact ( ms_model M_solver_simplify_spec = nil -> ms_model Mdone = nil ) as H_model_empty.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay M_solver_simplify_spec) ->
    msat_fp32_positive_finite (ms_cla_decay Mdone) ) as H_decay_positive.
  unfold solver_simplify_post_at.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  entailer_with ltac:(lia).
  Exists Mfinish.
  unfold solver_simplify_finish_transition in H_solver_simplify_finish_transition.
  destruct H_solver_simplify_finish_transition as [Hfinish [Hinv [Hlim [Hqhead [Hpending [Hseed [Hmodel Hdecay]]]]]]].
  bind_fact (solver_simplify_reuse M_solver_simplify_spec Mdone) as Hreuse.
  assert (Hreuse_finish : solver_simplify_reuse M_solver_simplify_spec Mfinish).
  { rewrite Hfinish. exact Hreuse. }
  assert (Hcap_finish : ms_cap Mfinish = ms_cap Mdone).
  { rewrite Hfinish. reflexivity. }
  assert (Hroot_finish : ms_root_level Mfinish = ms_root_level Mdone).
  { rewrite Hfinish. reflexivity. }
  unfold msat_fp32_same in *.
  entailer_with ltac:(lia).
  - intro Hempty. rewrite Hmodel. exact (H_model_empty Hempty).
  - intro Hpositive. rewrite Hdecay. exact (H_decay_positive Hpositive).
Qed.

(* ===== solver_solve partial_solve wits (12 proofs) ===== *)
Lemma proof_of_solver_solve_partial_solve_wit_17_pure : solver_solve_partial_solve_wit_17_pure.
Proof.
  Unfold.
  msat_solve_close_assumption_lit_bounds k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_19_pure : solver_solve_partial_solve_wit_19_pure.
Proof.
  Unfold.
  msat_solve_close_assumption_lit_bounds k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_22_pure : solver_solve_partial_solve_wit_22_pure.
Proof.
  Unfold.
  msat_solve_close_assumption_lit_bounds k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_25_pure : solver_solve_partial_solve_wit_25_pure.
Proof.
  Unfold.
  msat_solve_close_assumption_lit_bounds k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_27_pure : solver_solve_partial_solve_wit_27_pure.
Proof.
  Unfold.
  msat_solve_close_assumption_lit_bounds k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_30_pure : solver_solve_partial_solve_wit_30_pure.
Proof.
  Unfold.
  msat_solve_close_assumption_lit_bounds k.
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_32_pure : solver_solve_partial_solve_wit_32_pure.
Proof.
  Unfold; left; intros; msat_solve_lit_assign_bounds_p1 retval_2 retval k raw Mcur
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_33_pure : solver_solve_partial_solve_wit_33_pure.
Proof.
  Unfold.
  right; intros.
  msat_solve_lit_assign_bounds_p1 retval_2 retval k raw Mcur
    (- Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_34_pure : solver_solve_partial_solve_wit_34_pure.
Proof.
  Unfold.
  right; intros.
  msat_solve_lit_assign_bounds_p1 retval_2 retval k raw Mcur
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_35_pure : solver_solve_partial_solve_wit_35_pure.
Proof.
  Unfold; left; intros; msat_solve_lit_assign_bounds_p1 retval_2 retval k raw Mcur
    (- Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_36_pure : solver_solve_partial_solve_wit_36_pure.
Proof.
  Unfold; left; intros; msat_solve_lit_assign_bounds_p1 retval_2 retval k raw Mcur
    (Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
Qed.

Lemma proof_of_solver_solve_partial_solve_wit_37_pure : solver_solve_partial_solve_wit_37_pure.
Proof.
  Unfold; left; intros; msat_solve_lit_assign_bounds_p1 retval_2 retval k raw Mcur
    (- Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0).
Qed.

(* ===== solver_solve which_implies wits (11 proofs) ===== *)
Lemma proof_of_solver_solve_which_implies_wit_23 : solver_solve_which_implies_wit_23.
Proof.
  Unfold.
  left; intros.
  assert (Hstatus : propagation_status = -2) by lia.
  subst propagation_status.
  unfold solver_propagate_post.
  Split.
  - Split.
    + Intros Mbad. Intros. cancel. exfalso; lia.
    + Intros Mbad pbad focusbad Cbad. Intros. cancel. exfalso; lia.
  - sep_apply (store_int_undef_store_int &("propagation_status") (-2)).
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_24 : solver_solve_which_implies_wit_24.
Proof.
  Unfold.
  left; intros.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M.
  bind_fact (ms_cap Mdecide = ms_cap M) as Hentry_cap.
  bind_fact (solver_query_reuse M Mdecide) as Hentry_reuse.
  unfold solver_propagation_capacity_raw.
  Intros Mcap.
  match goal with
  | H : solver_propagation_inv _ _ _ _ _ /\ _ |- _ =>
      destruct H as (Hinv & Hcaller & Hreuse & Hseed & Hexhausted & Hwatch & Hscan)
  end.
  assert (Hcap : ms_cap Mcap = ms_cap M).
  { unfold propagation_caller_frame in Hcaller. intuition congruence. }
  assert (Hquery_reuse : solver_query_reuse M Mcap).
  { intro Hentry. exact ((proj1 Hreuse) (Hentry_reuse Hentry)). }
  sep_apply (solver_propagation_capacity_rep_at_refold s Mcap values levels_ptr solve_wl).
  sep_apply (solver_rep_assigns_levels_at_rep s Mcap values levels_ptr solve_wl).
  sep_apply (store_ptr_undef_store_ptr &("values") values).
  Exists Mcap.
  unfold solver_prepare_capacity_pre.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_25 : solver_solve_which_implies_wit_25.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  bind_fact ( msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur ) as H_msolver_inv_assuming_strong.
  bind_fact ( A_arr = assumption_prefix raw (Zlength raw) ) as H_A_arr.
  bind_fact ( Forall (lit_wf_c n) raw ) as H_Forall.
  bind_fact ( Znth (lit_var_c (Znth k raw 0)) (mt_assigns (ms_core Mcur)) 0 = 2 * lit_sign_c (Znth k raw 0) - 1 ) as
      H_Znth.
  set (current := Znth k raw 0).
  pose proof (msas_weak H_msolver_inv_assuming_strong) as Hweak.
  pose proof (msa_trail_wf Hweak) as Hwf.
  assert (Hcurrent_wf : lit_wf_c n current).
  { unfold current.
    apply (Forall_Znth_elim Z (lit_wf_c n) raw 0 k H_Forall).
    lia. }
  assert (Hfalse : lit_false (mt_assigns (ms_core Mcur)) current).
  { unfold lit_false, current.
    rewrite H_Znth.
    unfold lit_sig, lit_sign_c.
    destruct (Z.odd (Znth k raw 0)); lia. }
  assert (Hneg_true :
      lit_true (mt_assigns (ms_core Mcur)) (lit_neg_c current)).
  { apply lit_false_neg_true. exact Hfalse. }
  pose proof (mtrail_wf_trail_covers n (ms_core Mcur) Hwf) as Hcovers.
  destruct (Hcovers (lit_neg_c current)
    (lit_neg_c_wf n current Hcurrent_wf) Hneg_true) as [i [Hi Hlit]].
  assert (HA : A_arr = lits_denote raw).
  { rewrite H_A_arr.
    unfold assumption_prefix.
    rewrite sublist_self by reflexivity.
    reflexivity. }
  assert (Hin : In (lit_denote current) A_arr).
  { rewrite HA. unfold lits_denote.
    apply in_map. unfold current. apply Znth_In. lia. }
  assert (Hunsat : cnf_unsat n (cnf_with_units F A_arr)).
  { eapply assuming_false_assumption_unsat with
      (A_proc := assumption_prefix raw k)
      (a := lit_denote current) (i := i); eauto.
    rewrite Hlit.
    apply lit_denote_neg.
    destruct Hcurrent_wf. lia. }
  subst assumption_status.
  sep_apply store_char_undef_store_char.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_solve_which_implies_wit_27 : solver_solve_which_implies_wit_27.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  rename M_solver_solve_spec into M.
  bind_fact (msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) Mcur) as Hstrong.
  bind_fact (solver_query_reuse M Mcur) as Hreuse.
  bind_fact (ms_capacity_root_propagation_pending Mcur = 0) as Hpending.
  bind_fact (msolver_seed_shadow Mcur) as Hseed.
  bind_fact (ms_size Mcur = n) as Hsize.
  bind_fact (mt_qhead (ms_core Mcur) = ms_qtail Mcur) as Hdrain.
  unfold solver_cancel_post.
  Split.
  - Intros.
    assert (Hlen : Zlength (mt_lim (ms_core Mcur)) <= 0) by assumption.
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mcur /\ solver_query_reentry n F Mcur /\ msolver_seed_shadow Mcur).
    { intro Hentry.
      destruct (solver_assuming_empty_base_recovery__api_reentry
        n F A_arr (assumption_prefix raw k) Mcur Hstrong Hpending
        (Hreuse Hentry) Hseed Hlen) as [Hbase [_ Hseed_current]].
      split; [exact Hbase|]. split; [|exact Hseed_current].
      exact (solver_base_recovery_drained_reentry__api_reentry
        n F Mcur Hbase Hdrain). }
    Exists Mcur. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + sep_apply (solver_cancel_join_rep s Mcur levels_ptr solve_wl).
      entailer_with ltac:(lia).
    + entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hreinserted).
    set (Mpost := msolver_cancel_project Mcur 0 orderpos order order_cap
      (ms_root_level Mcur)).
    assert (Hpositive : 0 < Zlength (mt_lim (ms_core Mcur))) by lia.
    assert (Hheap_n : heap_wf n (heap_of_lists order orderpos)).
    { rewrite <- Hsize. exact Hheap. }
    assert (Hrecovery : solver_query_reuse_guard M ->
      solver_base_recovery n F Mpost /\ solver_query_reentry n F Mpost /\ msolver_seed_shadow Mpost).
    { intro Hentry.
      destruct (solver_assuming_cancel_zero_base_recovery__api_reentry
        n F A_arr (assumption_prefix raw k) Mcur orderpos order order_cap
        Hstrong Hpending (Hreuse Hentry) Hseed Hpositive Hcap Hheap_n
        Hincl Hreinserted) as [Hbase [_ Hseed_post]].
      split; [exact Hbase|]. split; [|exact Hseed_post].
      exact (solver_cancel_project_reentry__api_reentry
        n F Mcur orderpos order order_cap (ms_root_level Mcur) Hbase). }
    Exists Mpost. unfold solver_unsat_arm_at.
    split_pure_spatial.
    + unfold Mpost.
      sep_apply (solver_cancel_project_join_rep s Mcur levels_ptr 0
        orderpos order order_cap (ms_root_level Mcur) solve_wl).
      entailer_with ltac:(lia).
    + unfold Mpost, msolver_cancel_project, msolver_core_heap_update.
      cbn. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_28 : solver_solve_which_implies_wit_28.
Proof.
  Unfold.
  left; intros.
  bind_fact ( i = begin + k * sizeof ( INT ) ) as H_i.
  bind_fact ( endvar = begin + Zlength raw * sizeof ( INT ) ) as H_endvar.
  assert (Hk : k = Zlength raw).
  { rewrite sizeof_int in H_i, H_endvar. lia. }
  subst k.
  sep_apply (store_ptr_undef_store_ptr &("i") i).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_29 : solver_solve_which_implies_wit_29.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  prop_apply (CharArray.seg_Zlength values 0 n (mt_assigns (ms_core Mcur))).
  Intros_p Hassigns_len.
  unfold solver_assigns_focus_frame_wl_at, solver_root_install_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  assert (Hn : n = ms_size Mcur).
  { match goal with
    | Hshape : solver_shape Mcur |- _ => unfold solver_shape in Hshape; lia
    end. }
  subst n.
  unfold solver_scalars_rep, solver_scalars_without_root_rep,
    solver_vecs_rep, solver_vecs_without_lim_rep.
  Exists act opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_30 : solver_solve_which_implies_wit_30.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  set (L := Zlength (mt_lim (ms_core Mcur))).
  set (Mroot := msolver_set_root Mcur L).
  set (A_inst := decisions_upto (ms_core Mcur) L).
  assert (Hinstall : assumption_root_install n F A_arr Mcur Mroot A_inst).
  { unfold Mroot, A_inst, L.
    apply assumption_root_install_intro__solve; assumption. }
  pose proof Hinstall as Hinstall_copy.
  unfold assumption_root_install in Hinstall_copy.
  destruct Hinstall_copy as
    (HA & HM & Hinv & Hroot & Hdrain & Hpending & Hseed).
  lazymatch goal with
  | Hreuse : solver_query_reuse ?entry Mcur |- _ =>
      assert (Hreuse_root : solver_query_reuse entry Mroot)
        by (intro Hready; exact (Hreuse Hready))
  end.
  Exists A_inst Mroot.
  split_pure_spatial.
  - pose proof (msi_shape Hinv) as Hshape.
    sep_apply (store_ptr_undef_store_ptr &("values") values).
    unfold solver_root_install_frame_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
    Intros act opos rsn trl tgs.
    unfold solver_rep_wl, solver_rep_levels_wl_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_trail_array_rep.
    Exists levels_ptr act values opos rsn trl tgs.
    unfold Mroot, L.
    rewrite fp_rep_set_root_eq, vecs_rep_set_root_eq.
    sep_apply join_vecs_trail_lim.
    sep_apply join_scalars_set_root.
    unfold msolver_set_root, msolver_core_heap_update in Hshape |- *.
    cbn in Hshape |- *.
    entailer_with ltac:(int_auto).
  - msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_31 : solver_solve_which_implies_wit_31.
Proof.
  Unfold.
  left; intros.
  assert (Hstatus : status = 0) by lia.
  subst status.
  unfold solver_restart_loop.
  Intros search_entry A_inst.
  match goal with
  | Hentry : ms_cap search_entry = ms_cap ?public_entry /\ _ |- _ =>
      destruct Hentry as (Hentry_cap & Hentry_watch)
  end.
  unfold solver_search_result.
  Split.
  - Split.
    + Split.
      * Intros Mbad. Intros. cancel. exfalso; lia.
      * Intros Mbad. Intros. cancel. exfalso; lia.
    + Intros Msearch.
      match goal with
      | Hpost : ms_cap Msearch = ms_cap search_entry /\ _ |- _ =>
          destruct Hpost as (Hcap & Hreuse & Hinv & Hroot & Hdrain & Hpending & Hseed)
      end.
      lazymatch type of Hentry_watch with
      | solver_query_reuse_guard ?entry -> _ =>
          assert (Hwatch : solver_query_reuse_guard entry ->
              minisat_base_watch_completed Msearch)
            by (intro Hready; exact (Hreuse (Hentry_watch Hready)))
      end.
      sep_apply (store_int_undef_store_int &("status") 0).
      Exists A_inst Msearch.
      unfold solver_search_pre.
      entailer_with ltac:(int_auto).
  - Intros Mbad. Intros. cancel. exfalso; lia.
Qed.

Lemma proof_of_solver_solve_which_implies_wit_32 : solver_solve_which_implies_wit_32.
Proof.
  Unfold. left; intros.
  unfold solver_restart_loop.
  Exists Msearch A_search.
  msat_manual_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_33 : solver_solve_which_implies_wit_33.
Proof.
  Unfold.
  left; intros.
  assert (Hstatus : status = -2) by lia.
  subst status.
  unfold solver_restart_loop.
  Intros search_entry A_inst.
  match goal with
  | Hentry : ms_cap search_entry = ms_cap ?public_entry /\ _ |- _ =>
      destruct Hentry as (Hentry_cap & Hentry_watch)
  end.
  unfold solver_search_result.
  Split.
  - Split.
    + Split.
      * Intros Mbad. Intros. cancel. exfalso; lia.
      * Intros Mbad. Intros. cancel. exfalso; lia.
    + Intros Mbad. Intros. cancel. exfalso; lia.
  - Intros Mcapacity.
    match goal with
    | Hpost : ms_cap Mcapacity = ms_cap search_entry /\ _ |- _ =>
        destruct Hpost as (Hcap & Hreuse & Hcapacity)
    end.
    lazymatch type of Hentry_watch with
    | solver_query_reuse_guard ?entry -> _ =>
        assert (Hwatch : solver_query_reuse entry Mcapacity)
          by (intro Hready; exact (Hreuse (Hentry_watch Hready)))
    end.
    unfold solver_internal_capacity_ready.
    sep_apply (store_int_undef_store_int &("status") (-2)).
    Exists A_inst Mcapacity.
    unfold solver_prepare_capacity_pre.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_solve_which_implies_wit_34 : solver_solve_which_implies_wit_34.
Proof.
  Unfold.
  left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename A_arr_solver_solve_spec into A_arr.
  rename solve_wl_solver_solve_spec into solve_wl.
  unfold solver_restart_loop.
  Intros search_entry A_inst.
  match goal with
  | Hentry : ms_cap search_entry = ms_cap ?public_entry /\ _ |- _ =>
      destruct Hentry as (Hentry_cap & Hentry_watch)
  end.
  unfold solver_search_result.
  Split.
  - Split.
    + Split.
      * Intros Mterminal.
        assert (Hstatus : status = 1) by lia.
        subst status.
        match goal with
        | Hfacts : ms_cap Mterminal = ms_cap search_entry /\ _ |- _ =>
            destruct Hfacts as (Hcap & Hreuse & Hinv & Hroot & Hdrain & Hpending & Hseed & Hmodel)
        end.
        lazymatch type of Hentry_watch with
        | solver_query_reuse_guard ?entry -> _ =>
            assert (Hterminal_reuse : solver_terminal_reuse n F A_arr entry Mterminal 1)
              by (intro Hready; split;
                  [intros _; exact (Hreuse (Hentry_watch Hready))
                  |intro Hbad; discriminate])
        end.
        assert (Hsat_ready : solver_sat_cancel_ready n F A_arr Mterminal).
        { exists A_inst. split; [exact Hinv|]. split; [exact Hdrain|].
          split; [exact Hpending|exact Hseed]. }
        pose proof (msi_size Hinv) as Hsize.
        pose proof (msi_prop_level Hinv) as Hprop.
        assert (Hcancel : cancel_bound_ready Mterminal 0).
        { unfold cancel_bound_ready.
          destruct (Z_lt_ge_dec 0 (Zlength (mt_lim (ms_core Mterminal)))).
          - right. unfold prop_level in Hprop.
            apply (Forall_Znth_elim Z
              (fun b => b <= mt_qhead (ms_core Mterminal))
              (mt_lim (ms_core Mterminal)) 0 0 Hprop). lia.
          - left. pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))). lia. }
        sep_apply (solver_rep_cancel_split s Mterminal solve_wl).
        Intros terminal_levels.
        Exists terminal_levels Mterminal.
        unfold solver_cancel_pre.
        entailer_with ltac:(lia);
          [ exact (msi_shape Hinv)
          | rewrite <- Hsize; exact (msi_trail_wf Hinv)
          | rewrite <- Hsize; exact (msi_heap_wf Hinv)
          | pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))); lia ].
      * Intros Mterminal.
        assert (Hstatus : status = -1) by lia.
        subst status.
        match goal with
        | Hfacts : ms_cap Mterminal = ms_cap search_entry /\ _ |- _ =>
            destruct Hfacts as (Hcap & Hreuse & Hweak & Hroot & Hcancel & Hpending & Hunsat)
        end.
        lazymatch type of Hentry_watch with
        | solver_query_reuse_guard ?entry -> _ =>
            assert (Hterminal_reuse : solver_terminal_reuse n F A_arr entry Mterminal (-1))
              by (intro Hready; split;
                  [intro Hbad; discriminate
                  |intros _; exists A_inst; exact (Hreuse (Hentry_watch Hready))])
        end.
        pose proof (msw_size Hweak) as Hsize.
        sep_apply (solver_rep_cancel_split s Mterminal solve_wl).
        Intros terminal_levels.
        Exists terminal_levels Mterminal.
        unfold solver_cancel_pre.
        entailer_with ltac:(lia);
          [ exact (msw_shape Hweak)
          | rewrite <- Hsize; exact (msw_trail_wf Hweak)
          | rewrite <- Hsize; exact (msw_heap_wf Hweak)
          | pose proof (Zlength_nonneg (mt_lim (ms_core Mterminal))); lia ].
    + Intros Mbad. Intros. cancel. exfalso; lia.
  - Intros Mbad. Intros. cancel. exfalso; lia.
Qed.
