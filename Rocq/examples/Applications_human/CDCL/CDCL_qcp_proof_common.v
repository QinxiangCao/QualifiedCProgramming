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
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_goal.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.CDCL.CDCL_qcp_lib.
Local Open Scope sac.

(* FILE INDEX: QCPSAT PROOF MANUAL
 * ================================
 *
 * This file contains 166 manual proofs (plus one local helper) organized by
 * proof family.  Each family's proofs are marked with a section header comment.
 *
 * The 1,083 generated obligations are partitioned 166 here / 917 in
 * CDCL_qcp_proof_auto.v, where they are discharged by the QCP tool rather
 * than proved in Coq.  There is no overlap and no gap; the
 * partition is what goal_check.v's Module Type ascription checks.  (Folding the
 * four helper contracts added one obligation, on the auto side: it split
 * clause_learning's partial_solve chain, which is also what renumbered this
 * file's one clause_learning partial_solve proof from wit_9_pure to
 * wit_10_pure.  The previous revision of this line said 1,081 / 915, one short
 * on the auto side of the then-current 1,082 / 916.)
 *
 * NOTE ON SCOPE: what is proved is PARTIAL correctness.  No termination
 * theorem exists here or anywhere in the development, and QCP has no syntax
 * for a loop variant.  (Well-founded induction *is* used inside the library --
 * see lt_wf_ind in root_assignment_agrees_at_rank -- but that is induction on
 * a ghost rank, not a proof that any loop terminates.)
 *
 * Families (in file order):
     fill_ints: 3 proofs - Initialization: clear array with integer values
     clause_resolution: 8 proofs - Resolution prefix tracking: advancing resolution state
     clause_learning: 13 proofs - Clause learning: deriving new clauses from conflicts
     conflict_analysis: 9 proofs - Conflict analysis: analyzing unsatisfiable clauses
     bcp_safety: 3 proofs - Boolean constraint propagation: propagation safety invariants
     bcp_entail: 69 proofs - Boolean constraint propagation: entailment lemmas for BCP steps
     bcp_return: 1 proofs - BCP return: postcondition for BCP function
     backtrack_safety: 0 proofs - (all reclassified to the auto module)
     backtrack_entail: 29 proofs - Backtracking: entailment during backtrack steps
     backtrack_return: 1 proofs - Backtrack return: postcondition for backtrack function
     decide_safety: 0 proofs - (all reclassified to the auto module)
     decide_entail: 12 proofs - Decision: entailment lemmas for decision steps
     decide_return: 2 proofs - Decision return: postcondition for decide function
     cdcl_solver: 16 proofs - CDCL solver: solver analysis and returns
                              (8 entail + 3 partial_solve + 5 return)
 *
 * HISTORY: an earlier revision of this index claimed 253 proofs, with
 * bcp_safety 59 / backtrack_safety 28 / decide_safety 3.  Those 87 obligations
 * were reclassified into the auto module; all eleven other family counts were
 * and remain exact.  Every reclassified obligation is a *safety* wit (memory
 * and integer side conditions) -- no entailment, return, or partial_solve
 * obligation has ever moved out of this file.
 *)


(* ============================================================
 * READING THE LOCAL TACTIC LAYER
 * ============================================================
 * The ~500 lines below are file-local tactics.  They exist because the
 * generated obligations come in families that differ by one or two
 * parameters, so collapsing each family to a one-line application is what
 * keeps this file at 166 proofs instead of several hundred near-copies.
 * They are NOT a good entry point for a new reader -- start at the verdict
 * proofs (search for cdcl_solver_return_wit_) and work backwards.
 *
 * Naming conventions, all five load-bearing:
 *   derive_*    produces a named fact into the context; proves nothing on
 *               its own.
 *   solve_*     discharges an entire obligation; a proof body is one call.
 *   *_prelude   shared HEAD of a family -- context reshaping before the
 *               interesting step.
 *   *_epilogue  shared TAIL of a family -- witness supply and cancellation
 *               after the interesting step.
 *   *_absurd    closes a goal that is unreachable, by deriving a
 *               contradiction from the snapshot invariants.  These are the
 *               dense-encoding domain facts ({-1,0,1} cells, in-range
 *               indices) showing a branch cannot be taken.
 *   bind_fact   names ONE context fact by its statement:
 *                 bind_fact (<fact>) as H.
 *               The pattern must be closed -- copy the fact from the
 *               obligation statement in goal.v (drop the coq_prop quotes).
 *               For shape-based binding with holes, use an inline
 *               [match goal] as the rest of this layer does.
 *
 * REGENERATION FRAGILITY -- read before editing:
 *   Proofs and tactics bind context facts BY CONTENT (bind_fact /
 *   match goal with ...), never by PreH number, and that is deliberate:
 *   PreH numbering is a function of the generated hypothesis list and
 *   shifts whenever an annotation's pure conjuncts change.  No tactic
 *   takes a hypothesis positionally, and no proof body may name a PreH:
 *   a fact is bound once at the top of the proof (bind_fact) and used by
 *   its semantic name after that.
 *   Separately, `Exists` supplies a PREFIX of a goal's EX binders in
 *   generated order -- an order that is not the order the C annotation
 *   writes them in, and that can permute when spatial atoms move.  Any
 *   annotation change therefore requires re-reading goal.v, not just
 *   re-running the proofs.
 * ============================================================ *)

(* BEGIN local tactics (simplification pass) *)
(* Content-addressed hypothesis naming (PreH-elimination pass): finds the one
   context fact whose statement is [ty] and renames it.  [ty] must be a closed
   term -- copy it from the obligation statement in goal.v; a pure conjunct
   quoted there as a coq_prop is introduced with the quotes stripped.  This is
   what makes proof bodies survive PreH renumbering: the generated name is
   never written down, only the fact itself. *)
Tactic Notation "bind_fact" constr(ty) "as" ident(na) :=
  match goal with H : ty |- _ => rename H into na end.

(* Setter notations (simplification pass): file-local (only parsing) shorthands for the
   two most-repeated dense_snapshot record-update literals. Notations elaborate
   byte-identically, so every apply/rewrite/destruct over these terms is unchanged. *)
Notation snapshot_after_scan S R states tc ua :=
  {| snap_values := snap_values S;
     snap_reasons := snap_reasons S;
     snap_levels := snap_levels S;
     snap_rows := snap_rows R;
     snap_states := states;
     snap_true_counts := tc;
     snap_unassigned := ua |} (only parsing).
Notation snapshot_set_at snap x b reason d :=
  {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap);
     snap_reasons := replace_Znth x reason (snap_reasons snap);
     snap_levels := replace_Znth x d (snap_levels snap);
     snap_rows := snap_rows snap;
     snap_states := snap_states snap;
     snap_true_counts := snap_true_counts snap;
     snap_unassigned := snap_unassigned snap |} (only parsing).
(* decide: re-merge the focused clause row back into the full row table.
   Shared head of the decide entailments -- they all focus row j to read it,
   then must hand the table back whole. *)
Ltac decide_rows_prelude row_table j live row_ptr snap :=
  pose proof (IntPtrArray2.missing_i_merge_to_full
    row_table j live row_ptr (snap_rows snap)
    (Znth j (snap_rows snap) nil)) as Hmerge;
  unfold StorePtrAsElement.storeA in Hmerge;
  try rewrite sizeof_ptr;
  fold_arch;
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth j (snap_rows snap) nil))
    (Znth j (snap_rows snap) nil)) with
    (IntArray.full row_ptr
      (Zlength (Znth j (snap_rows snap) nil))
      (Znth j (snap_rows snap) nil)) in Hmerge;
  sep_apply Hmerge; try lia;
  rewrite replace_Znth_Znth by lia;
  unfold installed_rows_capacity_rep.
(* Choose an arm of a goal-side disjunction by rewriting with the supplied
   introduction lemma (orp_intro1 / orp_intro2).  Needed because QCP leaves
   the two Ensure arms as a top-level ||, and only the proof knows which one
   the current path establishes. *)
Ltac pick_disjunct lem :=
  match goal with
  | |- ?P |-- (?Q || ?R) => rewrite <- (lem Q R)
  end.

(* Post-W2b scan-loop shapes: the states array reaches the bcp entailments as
   IntArray.full(states, live, replace_Znth i current_state cur_states) — the
   rule-10 merge of the read focus — with the read identity
   Znth i (replace_Znth i current_state l) 0 = current_state published as a
   PreH, and bcp_clause_scan now a pure PreH instead of a spatial atom. *)

Lemma bcp_replace_Znth_collapse : forall (l : list Z) (i v w : Z),
  replace_Znth i v (replace_Znth i w l) = replace_Znth i v l.
Proof.
  intros l i v w.
  unfold replace_Znth.
  set (m := Z.to_nat i); clearbody m; clear i.
  revert m; induction l as [|a l IH]; intros m; destruct m; simpl; auto.
  rewrite IH; reflexivity.
Qed.

(* Rebind the mixed-summaries payload from the (now Prop) scan_rep hypothesis
   and derive current_state's literal value from the published read identity.
   [current_state] is a parameter (definition-time resolution). *)
Ltac bcp_scan_prelude current_state Hmixed Hcs :=
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end;
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj2 (proj2 Hs)) as Hmixed
  end;
  try match goal with
  | Hread : Znth ?i (replace_Znth ?i current_state ?l) 0 = current_state,
    Hval : Znth ?i (replace_Znth ?i current_state ?l) 0 = ?v |- _ =>
      first [ constr_eq Hread Hval; fail 1 | idtac ];
      assert (Hcs : current_state = v) by (rewrite <- Hread; exact Hval)
  end;
  (* normalize hypotheses and goal through the published read identities so
     the guard facts regain their pre-W2b current_state form; identities are
     consumed (cleared) once folded in *)
  repeat match goal with
  | Hread : Znth ?i (replace_Znth ?i ?v ?l) 0 = ?v |- _ =>
      repeat match goal with
      | Hx : context [ Znth i (replace_Znth i v l) 0 ] |- _ =>
          first [ constr_eq Hx Hread; fail 1 | rewrite Hread in Hx ]
      end;
      try rewrite Hread;
      clear Hread
  end.

(* Derive the bcp_advance_false_dense delta for the current scan step.
   Binds every context fact by content (never a hard-coded PreH number);
   [bval] fixes the assigned polarity and [new_state] the resulting cell.
   The decode lemma and the state-transition disjunction are selected by
   [first], so a single body serves both polarities and both new-state shapes
   (literal 2 for the -2 -> 2 transition, current_state+1 otherwise). *)

Ltac derive_bcp_advance_false bval new_state b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap :=
  assert (Hb : b_2 = bval) by
    (first [ eapply assigns_one_replaced_zero_false__bcp_assignment_summary_d
           | eapply assigns_one_replaced_one_true__bcp_assignment_summary_d ];
     try eassumption; try (split; lia);
     match goal with
     | Hvc : value_cell_2 = _, Hve : snap_values new_snap_2 = _ |- _ =>
         rewrite Hvc in Hve; exact Hve
     end);
  match goal with
  | Hmix_conj : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _,
    Hcoh : coherent_snapshot _ _ _ _ snap,
    Hassign : assigns_one _ _ bcpvar b_2 logical_dl unitcl,
    Hready : bcp_ready _,
    Hneq : i_3 <> unitcl,
    Hunit : Znth bcpvar (Znth unitcl (snap_rows snap) (@nil Z)) 0 = _,
    Hrow : Znth bcpvar (Znth i_3 (snap_rows snap) (@nil Z)) 0 = _,
    Hold : current_state = Znth i_3 cur_states_2 0,
    Hs0 : current_state <> 0,
    Hs1 : current_state <> 1,
    Hs2 : current_state <> 2 |- _ =>
      pose proof (bcp_advance_false_dense__bcp_assignment_summary_d
        F n live original_count snap ranks logical_dl
        (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
        bcpvar b_2 logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
        cap i_3 unitcl current_state new_state Hcoh Hassign Hready (proj2 (proj2 Hmix_conj))
        ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hneq
        ltac:(rewrite Hb; exact Hunit)
        ltac:(rewrite Hb; exact Hrow) Hold Hs0 Hs1 Hs2
        ltac:(first [ left; split; lia | right; split; [lia|reflexivity] ]))
        as [Hadvance Hnext]
  end.

Ltac cdcl_pack_bcp_advance :=
  match goal with
  | Hmix_conj : ?Hassign /\ ?Hrange /\ _, Hadvance : ?Hmix_next |-
      ?Hassign /\ ?Hrange /\ ?Hmix_next =>
      split; [ exact (proj1 Hmix_conj) | split; [ exact (proj1 (proj2 Hmix_conj)) | exact Hadvance ] ]
  | Hassign : ?A, Hrange : ?R, Hadvance : ?M |- ?A /\ ?R /\ ?M =>
      split; [ exact Hassign | split; [ exact Hrange | exact Hadvance ] ]
  end.

(* Collapse of the false-outcome scan-step proofs 10_32/10_35/10_38/10_41.
   [bval] = assigned polarity, [new_state] = clause state stored at i_3. *)

Ltac solve_bcp_scan_step_false bval new_state i_3 cur_unassigned_2 cur_true_2 s_cl_data_5 s_v_data_5 b_2 value_cell_2 new_snap_2 ranks1_2 cur_states_2 states live row_table cap conflict snap bcpvar logical_dl unitcl current_state F n original_count ranks row_ptr Hnext Hcell :=
  LLM_pre_process ltac:(int_auto);
  (* callers pass a folded variable_arrays_rep; unfold before the
     witness supply, as everywhere else *)
  unfold variable_arrays_rep;
  let Hmix_pre := fresh "Hmix_pre" in
  let Hcs_pre := fresh "Hcs_pre" in
  bcp_scan_prelude current_state Hmix_pre Hcs_pre;
  rewrite ?bcp_replace_Znth_collapse;
  Right;
  Exists (replace_Znth i_3 (Znth i_3 cur_unassigned_2 0 - 1) cur_unassigned_2)
    cur_true_2 s_cl_data_5 s_v_data_5 b_2 value_cell_2 new_snap_2 ranks1_2
    (replace_Znth i_3 new_state cur_states_2) (i_3 + 1);
  unfold bcp_clause_scan, bcp_ready;
  try poly_store_unfold; asrt_simpl_pure; sepcon_assoc_change;
  andp_cancel; try simpl_entail; (* retained inside the multi-goal helper *)
  [ derive_bcp_advance_false bval new_state b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap;
    try rewrite IntArray.seg_shape_empty;
    let Hmerge := fresh "Hmerge_rt" in
    pose proof (installed_row_focus_merge
      row_table live i_3 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge;
    unfold installed_row_focus_rep in Hmerge;
    unfold StorePtrAsElement.storeA in Hmerge;
    try rewrite sizeof_ptr;
    fold_arch;
    sep_apply Hmerge;
    unfold installed_rows_capacity_rep;
    cancel (PtrArray.undef_seg row_table live cap);
    entailer!
  | derive_bcp_advance_false bval new_state b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; cdcl_pack_bcp_advance
  | derive_bcp_advance_false bval new_state b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; exact Hnext
  | match goal with Hmix_conj : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj2 (proj2 Hmix_conj)) as Hlens; unfold mixed_clause_summaries in Hlens;
      destruct Hlens as [_ [Hstates _]];
      intros Hconflict k Hk;
      destruct (Z.eq_dec k i_3) as [->|Hki];
      [ rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia); lia
      | rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia);
        match goal with Hclear : conflict = -1 -> _ |- _ => apply (Hclear Hconflict k); lia end ]
    end
  | match goal with Hmix_conj : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj2 (proj2 Hmix_conj)) as Hlens; unfold mixed_clause_summaries in Hlens;
      destruct Hlens as [_ [Hstates _]];
      intros Hconflict;
      match goal with Hfound : conflict <> -1 -> _ |- _ =>
        pose proof (Hfound Hconflict) as [[Hc0 Hci] Hcell] end;
      split; [lia|];
      rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia); exact Hcell
    end ].

(* Derive the bcp_advance_same_dense delta for the current scan step.
   The i_3=unitcl vs i_3<>unitcl case split is discharged by [first]. *)

Ltac derive_bcp_advance_same bval b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap :=
  assert (Hb : b_2 = bval) by
    (first [ eapply assigns_one_replaced_zero_false__bcp_assignment_summary_d
           | eapply assigns_one_replaced_one_true__bcp_assignment_summary_d ];
     try eassumption; try (split; lia);
     match goal with
     | Hvc : value_cell_2 = _, Hve : snap_values new_snap_2 = _ |- _ =>
         rewrite Hvc in Hve; exact Hve
     end);
  match goal with
  | Hmix_conj : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _,
    Hcoh : coherent_snapshot _ _ _ _ snap,
    Hassign : assigns_one _ _ bcpvar b_2 logical_dl unitcl,
    Hready : bcp_ready _,
    Hunit : Znth bcpvar (Znth unitcl (snap_rows snap) (@nil Z)) 0 = _ |- _ =>
      pose proof (proj2 (proj2 Hmix_conj)) as Hmixed;
      pose proof (bcp_advance_same_dense__bcp_assignment_summary_d
        F n live original_count snap ranks logical_dl
        (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
        bcpvar b_2 logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
        cap i_3 unitcl Hcoh Hassign Hready Hmixed
        ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
        ltac:(rewrite Hb; exact Hunit)
        ltac:(first [ left; assumption
                    | right; split; [ intro Heq; subst i_3; congruence | assumption ] ]))
        as [Hadvance Hnext]
  end.

(* Collapse of the same-outcome scan-step proofs 10_43/10_44/10_45/10_46. *)

Ltac solve_bcp_scan_step_same bval cur_unassigned_2 cur_true_2 s_cl_data_5 s_v_data_5 b_2 value_cell_2 new_snap_2 ranks1_2 cur_states_2 i_3 states live row_table cap current_state conflict snap bcpvar logical_dl unitcl F n original_count ranks row_ptr Hmixed Hnext :=
  LLM_pre_process ltac:(int_auto);
  (* callers pass a folded variable_arrays_rep; unfold before the
     witness supply, as everywhere else *)
  unfold variable_arrays_rep;
  let Hmix_pre := fresh "Hmix_pre" in
  let Hcs_pre := fresh "Hcs_pre" in
  bcp_scan_prelude current_state Hmix_pre Hcs_pre;
  (* fold the untouched states focus back to cur_states_2 *)
  let Hlens_pre := fresh "Hlens_pre" in
  let Hstates_pre := fresh "Hstates_pre" in
  pose proof Hmix_pre as Hlens_pre;
  unfold mixed_clause_summaries in Hlens_pre;
  destruct Hlens_pre as [_ [Hstates_pre _]];
  match goal with
  | Hcur : current_state = Znth i_3 cur_states_2 0 |- _ => rewrite Hcur
  end;
  rewrite replace_Znth_Znth by (rewrite Hstates_pre; lia);
  Right;
  Exists cur_unassigned_2 cur_true_2 s_cl_data_5 s_v_data_5 b_2
    value_cell_2 new_snap_2 ranks1_2 cur_states_2 (i_3 + 1);
  unfold bcp_clause_scan, bcp_ready;
  try poly_store_unfold; asrt_simpl_pure; sepcon_assoc_change;
  andp_cancel; try simpl_entail; (* retained inside the multi-goal helper *)
  [ derive_bcp_advance_same bval b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap;
    try rewrite IntArray.seg_shape_empty;
    let Hmerge := fresh "Hmerge_rt" in
    pose proof (installed_row_focus_merge
      row_table live i_3 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge;
    unfold installed_row_focus_rep in Hmerge;
    unfold StorePtrAsElement.storeA in Hmerge;
    try rewrite sizeof_ptr;
    fold_arch;
    sep_apply Hmerge;
    unfold installed_rows_capacity_rep;
    cancel (PtrArray.undef_seg row_table live cap);
    entailer!
  | derive_bcp_advance_same bval b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; cdcl_pack_bcp_advance
  | derive_bcp_advance_same bval b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_3 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; exact Hnext
  | match goal with
    | Hclear : conflict = -1 -> _,
      Hcur : current_state = Znth i_3 cur_states_2 0,
      Hne1 : current_state <> 1 |- _ =>
        eapply conflict_prefix_extend_same__bcp_assignment_summary_d;
        [ exact Hclear | rewrite <- Hcur; exact Hne1 ]
    end ].

(* Avoid the large [andp_cancel] search on the repeated BCP scan VCs.  The
   generated goals already separate cleanly into one spatial entailment and
   pure conjuncts, so split them directly and discharge the routine facts. *)
Ltac cdcl_split_pure_spatial :=
  split_pure_spatial;
  [ idtac
  | split_pures;
    dump_pre_spatial;
    try assumption;
    try reflexivity;
    try lia ].

Ltac cdcl_solve_bcp_prefix_advance :=
  match goal with
  | Hprefix : bcp_conflict_prefix ?conflict ?i ?states,
    Hmixed : mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |-
      bcp_conflict_prefix ?conflict (?i + 1)
        (replace_Znth ?i ?new_state ?states) =>
      let Hconflict_wit := fresh "Hconflict_wit" in
      let Hno_conflict := fresh "Hno_conflict" in
      let Hlens := fresh "Hlens" in
      let Hnz := fresh "Hconflict_nz" in
      let Heq := fresh "Hconflict_eq" in
      let Hk := fresh "Hk" in
      pose proof Hprefix as (Hconflict_wit & Hno_conflict);
      pose proof Hmixed as Hlens;
      unfold mixed_clause_summaries in Hlens;
      destruct Hlens as [_ [Hstates _]];
      split;
      [ intro Hnz;
        pose proof (Hconflict_wit Hnz) as [Hc0 [Hci Hcell]];
        split; [lia | split; [lia |]];
        rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia);
        exact Hcell
      | intros Heq k Hk;
        destruct (Z.eq_dec k i) as [->|Hki];
        [ rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia); lia
        | rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia);
          apply (Hno_conflict Heq k); lia ] ]
  end.

(* Small exact/near-clone bcp_entail cliques, regeneration-robust. *)

Ltac solve_bcp_row_domain_absurd F n live original_count snap i_3 bcpvar Hrow_wf :=
  aggressive_pre_process;
  match goal with
  | Hcoh : coherent_snapshot _ _ _ _ snap |- _ =>
      pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
        F n live original_count snap i_3 Hcoh ltac:(lia)) as Hrow_wf
  end;
  pose proof (row_wf_cell_domain n
    (Znth i_3 (snap_rows snap) (@nil Z)) bcpvar Hrow_wf ltac:(split; lia)) as Hcell;
  destruct Hcell as [Hcell|[Hcell|Hcell]]; contradiction.


(* False-goal closer: the hypothesis set claims a row cell outside {-1,0,1},
   which coherent_snapshot forbids.  Derive the domain fact, then lia. *)
Ltac solve_bcp_cell_domain_absurd F n live original_count snap i bcpvar :=
  aggressive_pre_process;
  match goal with
  | Hcoh : coherent_snapshot _ _ _ _ snap |- _ =>
      pose proof (coherent_snapshot_row_cell_domain__bcp_assignment_summary_b
        F n live original_count snap i bcpvar Hcoh ltac:(lia) ltac:(lia)) as Hdomain
  end;
  lia.


(* False-goal closer: the hypotheses claim a value for the just-written cell
   that contradicts what snapshot_replace_cell says was stored. *)
Ltac solve_bcp_snapshot_replace_absurd F n live original_count snap new_snap_2 bcpvar value_cell_2 :=
  aggressive_pre_process;
  match goal with
  | Hcoh : coherent_snapshot _ _ _ _ snap,
    Hve : snap_values new_snap_2 = _ |- _ =>
      pose proof (snapshot_replace_cell__bcp_assignment_summary_b
        F n live original_count snap new_snap_2 bcpvar value_cell_2 0
        Hcoh ltac:(lia) Hve) as Hcell
  end;
  lia.


(* False-goal closer, read-back form: unfold coherent_snapshot for the values
   length, then read the written cell back with Znth_replace_Znth_Same and let
   lia (or contradiction) close the mismatch. *)
Ltac solve_bcp_values_replaced_absurd snap new_snap_2 value_cell_2 bcpvar Hcoherent :=
  aggressive_pre_process;
  match goal with
  | Hcoh : coherent_snapshot _ _ _ _ snap |- _ => pose proof Hcoh as Hcoherent
  end;
  unfold coherent_snapshot in Hcoherent;
  destruct Hcoherent as (_ & _ & Hlengths & _ & _ & _);
  destruct Hlengths as (Hvalues_length & _);
  match goal with
  | Hve : snap_values new_snap_2 = _,
    Hvc : value_cell_2 = _,
    Htgt : Znth bcpvar (snap_values new_snap_2) 0 = _ |- _ =>
      rewrite Hve, Hvc in Htgt;
      rewrite Znth_replace_Znth_Same in Htgt by (rewrite Hvalues_length; lia);
      (lia || contradiction)
  end.


(* False-goal closer for the unchanged-value branch: the cell is shown equal
   to value_cell_2, contradicting the branch's disequality hypothesis.  The
   value-cell equation is found by content, so no PreH name is written down. *)
Ltac solve_bcp_replaced_value_same_absurd bcpvar new_snap_2 value_cell_2 :=
  LLM_pre_process ltac:(int_auto);
  assert (Hcell : Znth bcpvar (snap_values new_snap_2) 0 = value_cell_2)
    by (eapply coherent_replaced_value_same__bcp_assignment_summary_d; eauto; split; lia);
  match goal with
  | Hne : value_cell_2 = _ |- _ => rewrite Hne in Hcell; contradiction
  end.


(* Publish the two row facts every scan-loop entailment needs -- that index i
   is inside snap_rows, and that row i has length n -- both projected out of
   coherent_snapshot, then discharge the entailment.  The Znth_indep rewrite
   reconciles the generated default argument with the nil used here.
   The coherence fact, the assigned value-cell equation and the values-array
   update equation are found by content, so no PreH name is written down. *)
Ltac solve_bcp_scan_row_bounds_publish i snap n b_2 new_snap_2 ranks1_2 cur_states_2 values ranks logical_dl bcpvar unitcl live cur_true_2 cur_unassigned_2 cap __default__List_Z :=
  aggressive_pre_process;
  (* callers pass a folded variable_arrays_rep; unfold before the
     witness supply, as everywhere else *)
  unfold variable_arrays_rep;
  let Hcoh := fresh "Hcoh" in
  (match goal with
   | H : coherent_snapshot _ n live _ snap |- _ => rename H into Hcoh
   end);
  assert (Hrow_bound : 0 <= i < Zlength (snap_rows snap));
  [ pose proof Hcoh as Hcoherent;
    unfold coherent_snapshot in Hcoherent;
    destruct Hcoherent as (_ & _ & Hlengths & _ & _ & _);
    destruct Hlengths as (_ & _ & _ & Hrows_length & _ & _ & _);
    lia
  | ];
  assert (Hrow_length : Zlength (Znth i (snap_rows snap) (@nil Z)) = n);
  [ pose proof Hcoh as Hcoherent;
    unfold coherent_snapshot in Hcoherent;
    destruct Hcoherent as (_ & _ & _ & Hcells & _ & _);
    destruct Hcells as (_ & Hrows_wf);
    rewrite Forall_forall in Hrows_wf;
    apply Hrows_wf;
    unfold Znth;
    apply nth_In;
    rewrite Zlength_correct in Hrow_bound;
    lia
  | ];
  Exists b_2 new_snap_2 ranks1_2 cur_states_2;
  unfold bcp_clause_scan, bcp_ready;
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end;
  entailer!;
  [ rewrite (Znth_indep (snap_rows snap) i __default__List_Z (@nil Z)) by exact Hrow_bound;
    try rewrite (IntArray.seg_shape_empty values n);
    entailer!
  | match goal with
    | Hfact : snap_values new_snap_2 = replace_Znth bcpvar ?vc (snap_values snap),
      Hrw : ?vc = _ |- _ => rewrite <- Hrw; exact Hfact
    end ].


(* Show the unit clause's unassigned counter reaches 0 after the decrement,
   which is what makes it unit-propagatable.  Needs the values-array default
   reconciliation (-1 vs 0) before the counter arithmetic.  The coherence fact
   and the unassigned reading of the scanned variable are found by content, so
   no PreH name is written down. *)
Ltac solve_bcp_unit_unassigned_zero unitcl F n live original_count snap i :=
  aggressive_pre_process;
  (* callers pass a folded variable_arrays_rep; unfold before the
     witness supply, as everywhere else *)
  unfold variable_arrays_rep;
  replace (unitcl - 0) with unitcl by lia;
  let Hcoh := fresh "Hcoh" in
  let Hval := fresh "Hval" in
  (match goal with
   | H : coherent_snapshot F n live original_count snap |- _ => rename H into Hcoh
   end);
  (match goal with
   | H : Znth i (snap_values snap) 0 = (-1) |- _ => rename H into Hval
   end);
  pose proof (snapshot_value_defaults_eq__bcp_unit_to_assignment
    F n live original_count snap i 0 (-1) Hcoh ltac:(unfold var_in_range; lia)) as Hdefaults;
  assert (Hvalueminus : Znth i (snap_values snap) (-1) = -1) by (rewrite <- Hdefaults; exact Hval);
  assert (Hunassigned_len : Zlength (snap_unassigned snap) = live) by
    (unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto);
  assert (Hupdated :
    Znth unitcl (replace_Znth unitcl (Znth unitcl (snap_unassigned snap) 0 - 1)
      (snap_unassigned snap)) 0 = 0)
    by (rewrite Znth_replace_Znth_Same; [lia|]; rewrite Hunassigned_len; lia);
  Exists i;
  entailer!.
(* Copy backtrack_inner out of the context and split it into its five
   components (target, index range, cleared prefix, clear witness, mixed
   summaries).  Copies rather than destructs in place so the original
   hypothesis survives for later steps. *)
Ltac backtrack_destruct_inner Hinner_copy :=
  match goal with
  | H : backtrack_inner _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof H as Hinner_copy; unfold backtrack_inner in Hinner_copy
  end;
  destruct Hinner_copy as [Htarget [Hirange [Hprefix [Hclear Hmix]]]].


(* Project the values-array length out of the snapshot_lengths hypothesis for
   [snap].  Binds the hypothesis by content; if several snapshots have length
   facts in context, [match goal] backtracks until the projection fits the
   expected type of the ltac:() argument slot. *)
Ltac get_values_len snap :=
  let H' := fresh "Hlen_copy" in
  match goal with
  | H : snapshot_lengths _ _ snap |- _ =>
      pose proof H as H'; unfold snapshot_lengths in H'; exact (proj1 H')
  end.


(* Common tail of the backtrack advance steps: supply the four witnesses,
   then merge the focused row back into the full table and close.  The
   change/assert pair exists because the focused row arrives as an IntArray
   but the table expects an IntPtrArray2 element -- definitionally equal,
   not syntactically. *)
Ltac backtrack_advance_epilogue current_ranks_2 after_ranks_2 after_snap_2 current_snap_2 row_ptr j row_table live :=
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2;
  unfold installed_rows_capacity_rep;
  change (IntArray.full row_ptr
    (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)))
    (Znth j (snap_rows current_snap_2) (@nil Z))) with
    (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)))
      (Znth j (snap_rows current_snap_2) (@nil Z)));
  assert (Hfocus_merge :
      IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)))
        (Znth j (snap_rows current_snap_2) (@nil Z)) **
      IntPtrArray2.missing_i row_table live j row_ptr
        (snap_rows current_snap_2) **
      StorePtrAsElement.storeA row_table j row_ptr |--
      IntPtrArray2.full row_table live (snap_rows current_snap_2));
  [ sep_apply (IntPtrArray2.missing_i_merge_to_full
      row_table j live row_ptr (snap_rows current_snap_2)
      (Znth j (snap_rows current_snap_2) (@nil Z)) ltac:(lia));
    rewrite replace_Znth_Znth; cancel
  | sep_apply Hfocus_merge; unfold backtrack_inner; entailer! ].


(* Merge a focused row pointer back into the full row table (backtrack side).
   Same IntArray/IntPtrArray2 element reconciliation as the epilogue, but
   used where only the merge is wanted, not the witness supply. *)
Ltac backtrack_row_merge row_table j live row_ptr current_snap_2 :=
  pose proof (IntPtrArray2.missing_i_merge_to_full
    row_table j live row_ptr (snap_rows current_snap_2)
    (Znth j (snap_rows current_snap_2) (@nil Z))) as Hmerge_b;
  unfold StorePtrAsElement.storeA in Hmerge_b;
  try rewrite sizeof_ptr;
  fold_arch;
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)))
    (Znth j (snap_rows current_snap_2) (@nil Z))) with
    (IntArray.full row_ptr
      (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)))
      (Znth j (snap_rows current_snap_2) (@nil Z))) in Hmerge_b;
  sep_apply Hmerge_b; try lia;
  rewrite replace_Znth_Znth by lia;
  unfold installed_rows_capacity_rep;
  cancel.


(* Pull the PRE-clear summary for clause j out of mixed_clause_summaries.
   The seventh component is the per-clause disjunction; specialising it at j
   and taking the second arm gives the old (not-yet-restored) summary. *)
Ltac extract_old_summary_at_j Hcl Hmix j :=
  pose proof Hmix as Hpoints_copy;
  unfold mixed_clause_summaries in Hpoints_copy;
  destruct Hpoints_copy as [_ [_ [_ [_ [_ [_ Hpoints_copy]]]]]];
  specialize (Hpoints_copy j ltac:(lia));
  destruct Hpoints_copy as [_ Hold_summary];
  specialize (Hold_summary ltac:(split; [lia | discriminate]));
  unfold summary_at in Hold_summary;
  rewrite Hcl in Hold_summary.


(* False-goal closer: the hypotheses put a row cell outside {-1,0,1}.
   Reaches the domain fact via row_wf on row j, extracted from the snapshot's
   Forall over snap_rows.  Both snapshot facts are found by content, so no
   PreH name is written down. *)
Ltac backtrack_row_domain_absurd n j current_snap_2 i :=
  exfalso;
  let Hlen := fresh "Hlen_a" in
  let Hcells := fresh "Hcells_a" in
  (match goal with
   | H : snapshot_lengths n _ current_snap_2 |- _ => rename H into Hlen
   end);
  (match goal with
   | H : snapshot_cells_wf n _ current_snap_2 |- _ => rename H into Hcells
   end);
  destruct Hlen as [? [? [? [Hrows_len_a ?]]]];
  destruct Hcells as [? Hcells_rows_a];
  assert (Hrow_wf_a : row_wf n (Znth j (snap_rows current_snap_2) (nil : list Z)))
    by (apply (Forall_Znth_elim (list Z) (row_wf n)
         (snap_rows current_snap_2) (nil : list Z) j Hcells_rows_a);
        rewrite Hrows_len_a; lia);
  pose proof (row_wf_cell_domain n
    (Znth j (snap_rows current_snap_2) (nil : list Z)) i Hrow_wf_a
    ltac:(unfold var_in_range; lia)) as Hdom_a;
  destruct Hdom_a as [Hd_a | [Hd_a | Hd_a]]; lia.


(* Exfalso for the clause-state-zero contradictions in the backtrack clear
   loop: a literal of clause j is true under the restored assignment, so the
   pre-clear state of clause j cannot be 0. [bpol] = polarity of the restored
   assignment; [assign_lemma] = the snapshot_nonzero_assignment_{false,true}
   fact matching bpol; [inj] = or_intror for a -1 cell / or_introl for +1.
   Every generated fact it consumes is found by content -- the row cell at i,
   the pre-clear state of clause j, the two snapshot facts, the two value
   readings, the rows-map equation and the row length -- so no PreH name is
   written down; [Hmix] and [Hold_summary] are caller-local names. *)
Ltac backtrack_state_zero_absurd bpol assign_lemma inj Hmix n current_snap_2 current_ranks_2 back_dl_pre i live j snap ranks conflict_dl cur_states_2 cur_true_2 cur_unassigned_2 Hold_summary :=
  let Hcell := fresh "Hcell_z" in
  let Hstate := fresh "Hstate_z" in
  (match goal with
   | H : Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = _ |- _ =>
       rename H into Hcell
   end);
  (match goal with
   | H : Znth j cur_states_2 0 = _ |- _ => rename H into Hstate
   end);
  assert (Hassign_z :
      assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some bpol)
    by (match goal with
        | Hlen : snapshot_lengths n live current_snap_2,
          Hcells : snapshot_cells_wf n live current_snap_2,
          Hval : Znth i (snap_values current_snap_2) 0 <> _,
          Hvalne : Znth i (snap_values current_snap_2) (-1) <> (-1) |- _ =>
            exact (assign_lemma
                n live current_snap_2 i Hlen Hcells ltac:(lia) Hval Hvalne)
        end);
  assert (Hclause_z :
      Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (nil : clause)
      = dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z)))
    by (rewrite installed_clause_Znth_dense_decode__backtrack_clear_b;
        match goal with
        | Hmaprows : snap_rows current_snap_2 = snap_rows snap |- _ =>
            rewrite <- Hmaprows; reflexivity
        end);
  pose proof (literal_counts_dense_decode_true__backtrack_clear_b
    (Znth j (snap_rows current_snap_2) (nil : list Z)) i bpol
    ltac:(match goal with
          | Hrowlen : Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n |- _ =>
              rewrite Hrowlen; lia
          end) (inj _ _ (conj Hcell eq_refl))) as [Hvd_z Htd_z];
  extract_old_summary_at_j Hclause_z Hmix j;
  pose proof (clause_summary_true_literal_state_zero__backtrack_clear_b
    (assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre))
    (dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z)))
    i bpol (Znth j cur_states_2 0) (Znth j cur_true_2 0) (Znth j cur_unassigned_2 0)
    Hassign_z Htd_z Hold_summary) as Hz_z;
  rewrite Hstate in Hz_z; discriminate Hz_z.


(* Spatial epilogue shared by the backtrack_finish_decide_bounds advance cases
   (4_20/4_22): re-merge the focused row j back into the full row table. *)
Ltac backtrack_finish_spatial row_table live j row_ptr current_snap_2 :=
  unfold installed_rows_capacity_rep;
  pose proof (installed_row_focus_merge row_table live j row_ptr
    (snap_rows current_snap_2) ltac:(lia)) as Hmerge;
  unfold installed_row_focus_rep in Hmerge;
  assert (Hmerge_ordered :
    IntArray.full row_ptr
      (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)))
      (Znth j (snap_rows current_snap_2) (@nil Z)) **
    IntPtrArray2.missing_i row_table live j row_ptr
      (snap_rows current_snap_2) **
    StorePtrAsElement.storeA row_table j row_ptr |--
    IntPtrArray2.full row_table live (snap_rows current_snap_2))
    by (sep_apply Hmerge; entailer!);
  unfold StorePtrAsElement.storeA in Hmerge_ordered;
  sep_apply Hmerge_ordered;
  entailer!.


(* Extract the pre-clear summary at clause j from the mixed-summaries fact
   [Hmixed], leaving [Hold : summary_at ...] unfolded. Shared by 4_20/4_22. *)
Ltac backtrack_finish_old_summary j Hmixed :=
  pose proof Hmixed as Hmixed_parts;
  unfold mixed_clause_summaries in Hmixed_parts;
  destruct Hmixed_parts as
    [Hlive [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hsummaries]]]]]];
  specialize (Hsummaries j ltac:(lia));
  destruct Hsummaries as [_ Hold];
  specialize (Hold ltac:(split; [lia|discriminate]));
  unfold summary_at in Hold |- *.


(* Exfalso prelude shared by the state-domain contradictions 4_19/4_21:
   pull the pre-clear clause state equality [Hstate] out of the inner rep. *)
Ltac backtrack_old_clause_state j :=
  right; intros;
  let Hsrc := fresh "Hsrc" in
  (match goal with
   | H : backtrack_inner _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as Hsrc
   end);
  unfold backtrack_inner, mixed_clause_summaries, summary_at,
    clause_summary_ok in Hsrc;
  exfalso;
  destruct Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hjrange & Hsummary);
  specialize (Hsummary j ltac:(lia));
  destruct Hsummary as [_ Hold];
  specialize (Hold ltac:(split; [lia | discriminate]));
  destruct Hold as [_ [_ Hstate]].
(* END local tactics *)


(* ===== qcpsat_fill_ints entail wits (2 proofs) ===== *)
