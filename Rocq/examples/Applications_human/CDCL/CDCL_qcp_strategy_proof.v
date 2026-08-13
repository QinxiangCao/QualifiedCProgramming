Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.CDCL.CDCL_qcp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma CDCL_qcp_strategy3_correctness : CDCL_qcp_strategy3.
Proof.
  pre_process_default.
  unfold installed_rows_capacity_rep.
  prop_apply (IntPtrArray2.full_Zlength p live rows).
  Intros.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i p i live rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z)) with
      (IntArray.full row_ptr
        (Zlength (Znth i rows __default_app1_Z))
        (Znth i rows __default_app1_Z)).
    entailer!.
    Intros_r v.
    apply_sepcon_adjoint.
    Intros.
    subst v.
    fold_arch.
    cancel.
Qed.

Lemma CDCL_qcp_strategy5_correctness : CDCL_qcp_strategy5.
Proof.
  pre_process_default.
  sep_apply (installed_rows_capacity_expose p live cap rows).
  2: lia.
  cancel (IntPtrArray2.full p live rows).
  cancel (PtrArray.undef_seg p (live + 1) cap).
  apply_sepcon_adjoint.
  elim_emp.
  unfold StorePtrAsElement.undefstoreA.
  fold_arch.
  cancel.
Qed.

Lemma CDCL_qcp_strategy4_correctness : CDCL_qcp_strategy4.
Proof.
  pre_process_default.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    p i live row_ptr rows (Znth i rows __default_app1_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  fold_arch.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows __default_app1_Z))
    (Znth i rows __default_app1_Z)) with
    (IntArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  unfold installed_rows_capacity_rep.
  cancel.
Qed.

Lemma CDCL_qcp_strategy6_correctness : CDCL_qcp_strategy6.
Proof.
  pre_process_default.
  pose proof (installed_rows_capacity_publish
    p live cap rows newp row) as Hpublish.
  unfold StorePtrAsElement.storeA in Hpublish.
  fold_arch.
  sep_apply Hpublish; try lia.
  cancel.
Qed.

(* Rules 31/32 name the focused row.  Definitional like 11-18, with one extra
   step: the generated statement spells the row-table cell as
   [poly_store FET_ptr (p + i * sizeof_front_end_type FET_ptr) row_ptr] while
   [installed_row_focus_rep] writes [StorePtrAsElement.storeA p i row_ptr],
   whose body uses [ptr_size_Z].  The two are convertible, and [fold_arch] is
   how rules 3-6 above say so. *)

Lemma CDCL_qcp_strategy31_correctness : CDCL_qcp_strategy31.
Proof.
  pre_process_default.
  unfold installed_row_focus_rep, StorePtrAsElement.storeA.
  fold_arch.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy32_correctness : CDCL_qcp_strategy32.
Proof.
  pre_process_default.
  unfold installed_row_focus_rep, StorePtrAsElement.storeA.
  fold_arch.
  entailer!.
Qed.

(* ===== rules 7/8 (R1/R2 enrichment) soundness ===== *)

Lemma strategy7_bounds :
  forall (old current after_clear : cdcl_view)
         (n target variable j live cap n2 dl : Z)
         (snap : dense_snapshot) (ranks : Z -> option nat)
         (F : cnf) (original_count : Z)
         (st tc un : list Z),
    backtrack_inner old current after_clear n target variable j live cap
       (installed_clauses (cdcl_view_of_snapshot n2 snap ranks dl)) st tc un ->
    coherent_snapshot F n live original_count snap ->
    0 <= j ->
    j < live ->
    (0 <= Znth j tc 0 <= n) /\
    (0 <= Znth j un 0 <= n) /\
    (- n <= Znth j st 0 <= 2).
Proof.
  intros old current after_clear n target variable j live cap n2 dl
    snap ranks F original_count st tc un Hbir Hcoh Hj0 Hjlive.
  unfold backtrack_inner in Hbir.
  destruct Hbir as [_ [_ [_ [_ Hmixed]]]].
  change (installed_clauses (cdcl_view_of_snapshot n2 snap ranks dl))
    with (map dense_decode (snap_rows snap)) in Hmixed.
  pose proof (coherent_snapshot_row_wf__learning_row_and_scan
    F n live original_count snap j Hcoh ltac:(lia)) as Hrowwf.
  unfold row_wf in Hrowwf.
  destruct Hrowwf as [Hrowlen _].
  exact (backtrack_current_summary_bounds__backtrack_safety_a
    (assignment current) (assignment after_clear) (snap_rows snap)
    st tc un live cap j n Hmixed ltac:(lia) Hrowlen).
Qed.

Lemma strategy8_bounds :
  forall (old new : cdcl_view)
         (x j live cap n n2 dl : Z)
         (snap : dense_snapshot) (ranks : Z -> option nat)
         (F : cnf) (original_count : Z)
         (st tc un : list Z),
    decision_update old new x j live cap
       (installed_clauses (cdcl_view_of_snapshot n2 snap ranks dl)) st tc un ->
    coherent_snapshot F n live original_count snap ->
    0 <= j ->
    j < live ->
    (0 <= Znth j tc 0 <= n) /\
    (0 <= Znth j un 0 <= n) /\
    (- n <= Znth j st 0 <= 2).
Proof.
  intros old new x j live cap n n2 dl snap ranks F original_count st tc un
    Hdur Hcoh Hj0 Hjlive.
  unfold decision_update in Hdur.
  destruct Hdur as [_ Hmixed].
  change (installed_clauses (cdcl_view_of_snapshot n2 snap ranks dl))
    with (map dense_decode (snap_rows snap)) in Hmixed.
  pose proof (coherent_snapshot_row_wf__learning_row_and_scan
    F n live original_count snap j Hcoh ltac:(lia)) as Hrowwf.
  unfold row_wf in Hrowwf.
  destruct Hrowwf as [Hrowlen _].
  exact (backtrack_current_summary_bounds__backtrack_safety_a
    (assignment old) (assignment new) (snap_rows snap)
    st tc un live cap j n Hmixed ltac:(lia) Hrowlen).
Qed.


Lemma CDCL_qcp_strategy7_correctness : CDCL_qcp_strategy7.
Proof.
  pre_process_default.
  match goal with
  | Hbir : backtrack_inner _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hcoh : coherent_snapshot _ _ _ _ _ |- _ =>
    pose proof (strategy7_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hbir Hcoh ltac:(lia) ltac:(lia)) as Hb
  end.
  destruct Hb as [[Htc1 Htc2] [[Hun1 Hun2] [Hst1 Hst2]]].
  entailer!.
Qed.

Lemma CDCL_qcp_strategy8_correctness : CDCL_qcp_strategy8.
Proof.
  pre_process_default.
  match goal with
  | Hdur : decision_update _ _ _ _ _ _ _ _ _ _,
    Hcoh : coherent_snapshot _ _ _ _ _ |- _ =>
    pose proof (strategy8_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hdur Hcoh ltac:(lia) ltac:(lia)) as Hb
  end.
  destruct Hb as [[Htc1 Htc2] [[Hun1 Hun2] [Hst1 Hst2]]].
  entailer!.
Qed.

(* ===== rules 9/10 (R3 + read-back normalization) soundness ===== *)

Lemma strategy9_mixed_bounds :
  forall old_sigma new_sigma dense_rows states true_counts unassigned
         live cap processed exempt j n,
    mixed_clause_summaries old_sigma new_sigma
      (map dense_decode dense_rows) states true_counts unassigned
      live cap processed (Some exempt) ->
    0 <= j < live ->
    Zlength (Znth j dense_rows (@nil Z)) = n ->
    0 <= Znth j true_counts 0 <= n /\
    0 <= Znth j unassigned 0 <= n /\
    - n <= Znth j states 0 <= 2.
Proof.
  intros old_sigma new_sigma dense_rows states true_counts unassigned
    live cap processed exempt j n Hmixed Hj Hrowlen.
  unfold mixed_clause_summaries in Hmixed.
  destruct Hmixed as [_ [_ [_ [_ [_ [_ Hall]]]]]].
  specialize (Hall j Hj).
  destruct Hall as [Hnew Hold].
  assert (Hsummary : exists sigma,
    summary_at sigma (map dense_decode dense_rows)
      states true_counts unassigned j).
  {
    destruct (Z_lt_ge_dec j processed) as [Hlt | Hge].
    - exists new_sigma. apply Hnew. left. exact Hlt.
    - destruct (Z.eq_dec exempt j) as [-> | Hne].
      + exists new_sigma. apply Hnew. right. reflexivity.
      + exists old_sigma. apply Hold. split; [lia | congruence].
  }
  destruct Hsummary as [sigma Hsummary].
  unfold summary_at, clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  rewrite (Znth_map_dense_decode__bcp_safety_bounds_a dense_rows j)
    in Htrue, Hunassigned, Hstate.
  pose proof (clause_true_count_bounds__bcp_safety_bounds_a
    sigma (dense_decode (Znth j dense_rows (@nil Z)))) as Ht.
  pose proof (clause_unassigned_count_bounds__bcp_safety_bounds_a
    sigma (dense_decode (Znth j dense_rows (@nil Z)))) as Hu.
  pose proof (expected_clause_state_bounds__bcp_safety_bounds_a
    sigma (dense_decode (Znth j dense_rows (@nil Z)))) as Hs.
  pose proof (dense_decode_Zlength_le__bcp_safety_bounds_a
    (Znth j dense_rows (@nil Z))) as Hdecode.
  rewrite Htrue, Hunassigned, Hstate.
  rewrite Hrowlen in Hdecode.
  repeat split; lia.
Qed.

Lemma strategy9_bounds :
  forall (old new : cdcl_view) (b : bool)
         (x d reason j exempt live cap n n2 dl : Z)
         (snap : dense_snapshot) (ranks : Z -> option nat)
         (F : cnf) (original_count : Z)
         (st tc un : list Z),
    bcp_clause_scan old new x b d reason j exempt live cap
       (installed_clauses (cdcl_view_of_snapshot n2 snap ranks dl)) st tc un ->
    coherent_snapshot F n live original_count snap ->
    0 <= j ->
    j < live ->
    (0 <= Znth j tc 0 <= n) /\
    (0 <= Znth j un 0 <= n) /\
    (- n <= Znth j st 0 <= 2).
Proof.
  intros old new b x d reason j exempt live cap n n2 dl
    snap ranks F original_count st tc un Hscan Hcoh Hj0 Hjlive.
  unfold bcp_clause_scan in Hscan.
  destruct Hscan as [_ [_ Hmixed]].
  change (installed_clauses (cdcl_view_of_snapshot n2 snap ranks dl))
    with (map dense_decode (snap_rows snap)) in Hmixed.
  pose proof (coherent_snapshot_row_wf__learning_row_and_scan
    F n live original_count snap j Hcoh ltac:(lia)) as Hrowwf.
  unfold row_wf in Hrowwf.
  destruct Hrowwf as [Hrowlen _].
  exact (strategy9_mixed_bounds
    (assignment old) (assignment new) (snap_rows snap)
    st tc un live cap j exempt j n Hmixed ltac:(lia) Hrowlen).
Qed.

Lemma CDCL_qcp_strategy9_correctness : CDCL_qcp_strategy9.
Proof.
  pre_process_default.
  match goal with
  | Hscan : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hcoh : coherent_snapshot _ _ _ _ _ |- _ =>
    pose proof (strategy9_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hscan Hcoh ltac:(lia) ltac:(lia)) as Hb
  end.
  destruct Hb as [[Htc1 Htc2] [[Hun1 Hun2] [Hst1 Hst2]]].
  entailer!.
Qed.

(* ===== rule 10 (replace_Znth read-back normalization) soundness ===== *)

Lemma CDCL_qcp_strategy10_correctness : CDCL_qcp_strategy10.
Proof.
  pre_process_default.
  prop_apply (IntArray.full_Zlength p live2 (replace_Znth i v l)).
  Intros.
  match goal with
  | Hlen : Zlength (replace_Znth i v l) = live2 |- _ =>
    rewrite (Zlength_replace_Znth l i v) in Hlen;
    rewrite (Znth_replace_Znth_Same 0 l i v) by lia
  end.
  entailer!.
Qed.

(* The two bundle-unfold rules.  Both are definitional: the predicate IS the
   separating conjunction on the right, so the entailment is an unfold plus the
   trivial [emp -* emp] frame the strategy shape carries. *)

Lemma CDCL_qcp_strategy12_correctness : CDCL_qcp_strategy12.
Proof.
  pre_process_default.
  unfold variable_arrays_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy14_correctness : CDCL_qcp_strategy14.
Proof.
  pre_process_default.
  unfold solver_arrays_rep.
  entailer!.
Qed.

(* The matching refold rules.  Same definitional content as 12/14, but in the
   wand direction: the atoms are handed back and re-packed into the bundle. *)

Lemma CDCL_qcp_strategy11_correctness : CDCL_qcp_strategy11.
Proof.
  pre_process_default.
  unfold variable_arrays_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy13_correctness : CDCL_qcp_strategy13.
Proof.
  pre_process_default.
  unfold solver_arrays_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy15_correctness : CDCL_qcp_strategy15.
Proof.
  pre_process_default.
  unfold var_header_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy16_correctness : CDCL_qcp_strategy16.
Proof.
  pre_process_default.
  unfold var_header_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy17_correctness : CDCL_qcp_strategy17.
Proof.
  pre_process_default.
  unfold clause_header_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy18_correctness : CDCL_qcp_strategy18.
Proof.
  pre_process_default.
  unfold clause_header_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy19_correctness : CDCL_qcp_strategy19.
Proof.
  pre_process_default.
  unfold sat_header_rep.
  repeat cancel.
  Intros_r_any.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma CDCL_qcp_strategy20_correctness : CDCL_qcp_strategy20.
Proof.
  pre_process_default.
  unfold sat_header_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy21_correctness : CDCL_qcp_strategy21.
Proof.
  pre_process_default.
  unfold sat_entry_header_rep.
  entailer!.
  Intros_r_any.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma CDCL_qcp_strategy22_correctness : CDCL_qcp_strategy22.
Proof.
  pre_process_default.
  unfold sat_entry_header_rep.
  entailer!.
Qed.

(* Rules 23/24 need no tactic beyond preprocessing; rules 29/30 below do.  The
   discriminator is the KIND of atom the action emits, NOT how deeply it
   unfolds -- both rules emit exactly their predicate's top-level conjuncts.

   23/24's conjuncts are opaque project-level predicate applications
   ([clause_summaries_explicit_rep], [installed_rows_capacity_rep]).
   Preprocessing leaves those alone, so the two sides match literally and the
   goal closes.  29/30's conjuncts are library array atoms ([IntArray.full],
   [IntArray.seg_shape]), which preprocessing normalises; that perturbs the
   literal match, so both sides must be brought to a common normal form by
   [unfold] + [entailer!].  Before the split, 23/24 emitted seven library array
   atoms and needed the unfold for exactly the 29/30 reason.

   Measured, not reasoned: [pre_process_default] alone closes 23 and 24, and
   fails on 29 with remaining open goals. *)

Lemma CDCL_qcp_strategy23_correctness : CDCL_qcp_strategy23.
Proof.
  pre_process_default.
Qed.

Lemma CDCL_qcp_strategy24_correctness : CDCL_qcp_strategy24.
Proof.
  pre_process_default.
Qed.

Lemma CDCL_qcp_strategy29_correctness : CDCL_qcp_strategy29.
Proof.
  pre_process_default.
  unfold clause_summaries_explicit_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy30_correctness : CDCL_qcp_strategy30.
Proof.
  pre_process_default.
  unfold clause_summaries_explicit_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy25_correctness : CDCL_qcp_strategy25.
Proof.
  pre_process_default.
  unfold resolution_rows_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy26_correctness : CDCL_qcp_strategy26.
Proof.
  pre_process_default.
  unfold resolution_rows_rep.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy27_correctness : CDCL_qcp_strategy27.
Proof.
  pre_process_default.
  unfold conflict_levels_rep.
  repeat cancel.
  do 5 Intros_r_any.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma CDCL_qcp_strategy28_correctness : CDCL_qcp_strategy28.
Proof.
  pre_process_default.
  unfold conflict_levels_rep.
  entailer!.
Qed.

(* ===== rules 33-48: the public solver-contract vocabulary =====

   THE LEVER, for whoever authors the next rule pair -- TWO independent counts
   over the GENERATED statement, not over the atoms:

     pure conjuncts in the generated statement  ->  is [unfold <pred>] needed?
     EX binders in the predicate                ->  are witnesses needed?

     neither    ->  [pre_process_default.] alone closes it
     pure only  ->  [unfold <pred>.] then [entailer!.]
     EX, with or without pure:
         right rule:  [unfold <pred>. Exists <ws>. entailer!.]
         left rule:   [unfold <pred>. Intros <ws>. Exists <ws>. entailer!.]

   [pre_process_default] will not thread a pure hypothesis through a wand into
   the folded predicate's pure part, and it will not invent existential
   witnesses.  Everything else it settles by delta-conversion, which is why a
   pure-free, EX-free rule needs no tactic at all.  The two counts are
   orthogonal: 33-48 never exhibited EX without pure, so the pure count alone
   appeared to decide the unfold.  Rules 49-54 below are that missing cell, and
   the [unfold] is there for the [EX], not for a pure conjunct -- a witness
   cannot be supplied through a folded head.

   Derived by diffing a rule that closes bare against one that does not.
   Rule 23's wand antecedent is [TT && emp ** atoms]; rule 33's is
   [TT && (“ coherent_snapshot ... ”) && emp ** (solver_arrays_rep ...)].  The
   pure conjunct is the entire difference.

   This SUPERSEDES an earlier "opaque project predicate vs library array atom"
   reading, which was an artefact of the sample it was measured on: there the
   only bare-closing rules happened also to be the pure-free ones.  [store_cnf]
   is an opaque project predicate and still needs the unfold, because it
   carries [coherent_snapshot]; conversely [unconstrained_Assignment] is a
   plain alias for a library-atom bundle and closes bare.

   Pure-conjunct count in the generated statement, and what each rule got:

     33-38   1 each   unfold + entailer!
     39/40   0        bare                    <- the only pure-free new pair
     41/42   8        unfold + witnesses + entailer!
     43/44   2        unfold + witnesses + entailer!
     45/46   2        unfold + witnesses + entailer!
     47/48   3        unfold + witnesses + entailer!

   [Exists] is positional, and the generated binder order is scrambled relative
   to the rule argument order in all sixteen, so the witness lists below are
   read off the generated declarations rather than off the .strategies heads.
   In every left rule the generated right-hand EX order does coincide with the
   definition's binder order in CDCL_qcp_lib.v, which is what lets one list
   serve both the [Intros] and the [Exists].  In every right rule the witnesses
   are already ALL-bound by the generated statement, so no [Intros] is needed.

   On method: none of these was hedged with a [try] that would have closed it
   either way.  The failure pattern is what produced the lever above -- a [try]
   would have hidden it, and it would also sit next to the forbidden blanket
   [all: try unfold]. *)

Lemma CDCL_qcp_strategy33_correctness : CDCL_qcp_strategy33.
Proof.
  pre_process_default. unfold store_cnf. entailer!.
Qed.

Lemma CDCL_qcp_strategy34_correctness : CDCL_qcp_strategy34.
Proof.
  pre_process_default. unfold store_cnf. entailer!.
Qed.

Lemma CDCL_qcp_strategy35_correctness : CDCL_qcp_strategy35.
Proof.
  pre_process_default. unfold uninitialized_Assignment. entailer!.
Qed.

Lemma CDCL_qcp_strategy36_correctness : CDCL_qcp_strategy36.
Proof.
  pre_process_default. unfold uninitialized_Assignment. entailer!.
Qed.

Lemma CDCL_qcp_strategy37_correctness : CDCL_qcp_strategy37.
Proof.
  pre_process_default. unfold store_Assignment. entailer!.
Qed.

Lemma CDCL_qcp_strategy38_correctness : CDCL_qcp_strategy38.
Proof.
  pre_process_default. unfold store_Assignment. entailer!.
Qed.

Lemma CDCL_qcp_strategy39_correctness : CDCL_qcp_strategy39.
Proof.
  pre_process_default.
Qed.

Lemma CDCL_qcp_strategy40_correctness : CDCL_qcp_strategy40.
Proof.
  pre_process_default.
Qed.

(* The four arm cores.  Witnesses are the definition's EX binders, in order:
   solver_input_core has two (the struct-pointer intermediates); the SAT and
   UNSAT arms have five; the capacity arm has six. *)

Lemma CDCL_qcp_strategy41_correctness : CDCL_qcp_strategy41.
Proof.
  pre_process_default.
  unfold solver_input_core.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy42_correctness : CDCL_qcp_strategy42.
Proof.
  pre_process_default.
  unfold solver_input_core.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy43_correctness : CDCL_qcp_strategy43.
Proof.
  pre_process_default.
  unfold solver_sat_arm_core.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy44_correctness : CDCL_qcp_strategy44.
Proof.
  pre_process_default.
  unfold solver_sat_arm_core.
  Intros final_snap final_dl final_live v_data cl_data.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy45_correctness : CDCL_qcp_strategy45.
Proof.
  pre_process_default.
  unfold solver_unsat_arm_core.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy46_correctness : CDCL_qcp_strategy46.
Proof.
  pre_process_default.
  unfold solver_unsat_arm_core.
  Intros final_snap final_dl final_live v_data cl_data.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

(* The capacity arm carries the orphan row as well. *)

Lemma CDCL_qcp_strategy47_correctness : CDCL_qcp_strategy47.
Proof.
  pre_process_default.
  unfold solver_capacity_exhausted_arm_core.
  Exists conflict_snap conflict_dl row_ptr row v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy48_correctness : CDCL_qcp_strategy48.
Proof.
  pre_process_default.
  unfold solver_capacity_exhausted_arm_core.
  Intros conflict_snap conflict_dl row_ptr row v_data cl_data.
  Exists conflict_snap conflict_dl row_ptr row v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

(* ===== rules 49-56: the helper-contract vocabulary =====

   Four predicates, one pair each: [solver_state], [learning_state],
   [backjump_state], [propagation_result].

   49-54 are the cell the 33-48 sample never contained: ZERO pure conjuncts
   together WITH EX binders.  The pure count alone would say "closes bare"; the
   EX count says "needs witnesses", and it wins, because a witness cannot be
   supplied through a folded head -- the [unfold] is what exposes the [EX] for
   [Exists] to instantiate, not what discharges a pure conjunct.  Nothing here
   closes by delta-conversion the way 39/40 did: [unconstrained_Assignment] is a
   plain alias of one atom, whereas these four are genuine bundles.

   Pure conjuncts in the generated statement, and EX binders in the definition:

     49/50   0   solver_state         2 EX  (v_data, cl_data)
     51/52   0   learning_state       2 EX  (v_data, cl_data)
     53/54   0   backjump_state       2 EX  (v_data, cl_data)
     55/56   1   propagation_result   3 EX  (pre_snap, pre_ranks, last)

   55/56 are the case the lever already covered: one pure conjunct
   ([dense_conflict_batch]) plus witnesses.  They also carry this corpus's first
   arrow-typed existential, [pre_ranks : Z -> option nat]; it is bound by
   [Intros] and instantiated by [Exists] exactly like a [Z], with no special
   handling.  [solver_state] occurs inside [propagation_result] and stays FOLDED
   on both sides of 55 and 56 -- the two sides are head-identical there, so
   unfolding it would only enlarge the goal.

   As in 33-48, nothing below is hedged with a [try].  Each proof is the
   shortest one the lever predicts, so an over-proof fails loudly with "No such
   goal" at the first superfluous tactic instead of passing silently. *)

Lemma CDCL_qcp_strategy49_correctness : CDCL_qcp_strategy49.
Proof.
  pre_process_default.
  unfold solver_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy50_correctness : CDCL_qcp_strategy50.
Proof.
  pre_process_default.
  unfold solver_state.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy51_correctness : CDCL_qcp_strategy51.
Proof.
  pre_process_default.
  unfold learning_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy52_correctness : CDCL_qcp_strategy52.
Proof.
  pre_process_default.
  unfold learning_state.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy53_correctness : CDCL_qcp_strategy53.
Proof.
  pre_process_default.
  unfold backjump_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy54_correctness : CDCL_qcp_strategy54.
Proof.
  pre_process_default.
  unfold backjump_state.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy55_correctness : CDCL_qcp_strategy55.
Proof.
  pre_process_default.
  unfold propagation_result.
  Exists pre_snap pre_ranks last.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy56_correctness : CDCL_qcp_strategy56.
Proof.
  pre_process_default.
  unfold propagation_result.
  Intros pre_snap pre_ranks last.
  Exists pre_snap pre_ranks last.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy57_correctness : CDCL_qcp_strategy57.
Proof.
  pre_process_default.
  unfold solver_loop_state.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy58_correctness : CDCL_qcp_strategy58.
Proof.
  pre_process_default.
  unfold solver_loop_state.
  entailer!.
Qed.

(* Rules 59-68: the five remaining cdcl_solver phase states.  Same shape as
   57/58 -- unfold the state, hand back its existentials, cancel.  The right
   rules only need Exists; the left rules must Intros first, and finish with
   the sepcon-adjoint step because the erased conjunct leaves an emp on one
   side. *)

Lemma CDCL_qcp_strategy59_correctness : CDCL_qcp_strategy59.
Proof.
  pre_process_default.
  unfold solver_after_bcp_state.
  Exists pre_snap pre_ranks last.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy60_correctness : CDCL_qcp_strategy60.
Proof.
  pre_process_default.
  unfold solver_after_bcp_state.
  Intros pre_snap pre_ranks last.
  Exists pre_snap pre_ranks last.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy61_correctness : CDCL_qcp_strategy61.
Proof.
  pre_process_default.
  unfold solver_learning_state.
  Exists pre_snap pre_ranks last.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy62_correctness : CDCL_qcp_strategy62.
Proof.
  pre_process_default.
  unfold solver_learning_state.
  Intros pre_snap pre_ranks last.
  Exists pre_snap pre_ranks last.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy63_correctness : CDCL_qcp_strategy63.
Proof.
  pre_process_default.
  unfold solver_install_slot_state.
  Exists pre_snap pre_ranks last.
  Exists old_state old_true_count old_unassigned v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy64_correctness : CDCL_qcp_strategy64.
Proof.
  pre_process_default.
  (* The slot cells are element-store definitions whose bodies use sizeof(INT)
     and ptr_size_Z, while the rule emits the raw 4 / Arch32.ptr_size_Z forms.
     They are convertible; [fold_arch] normalises them, exactly as rules 31/32
     already do for StorePtrAsElement.storeA. *)
  unfold solver_install_slot_state, StoreIntAsElement.storeA,
         StorePtrAsElement.undefstoreA.
  fold_arch.
  change (sizeof_front_end_type FET_int) with 4.
  Intros pre_snap pre_ranks last.
  Intros old_state old_true_count old_unassigned v_data cl_data.
  Exists pre_snap pre_ranks last.
  Exists old_state old_true_count old_unassigned v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy65_correctness : CDCL_qcp_strategy65.
Proof.
  pre_process_default.
  unfold solver_installed_row_state.
  Exists pre_snap installed_snap pre_ranks last.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy66_correctness : CDCL_qcp_strategy66.
Proof.
  pre_process_default.
  unfold solver_installed_row_state, StorePtrAsElement.storeA.
  fold_arch.
  Intros pre_snap installed_snap pre_ranks last.
  Intros v_data cl_data.
  Exists pre_snap installed_snap pre_ranks last.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

(* learning_focus_state.  Same shape as 51/52 (learning_state) plus a pure
   gate, which the tactic does not have to touch -- compare 41/42, where
   solver_input_core's gate is also discharged by entailer!.  The two EX
   binders are the struct-pointer intermediates, as everywhere in this family. *)

Lemma CDCL_qcp_strategy69_correctness : CDCL_qcp_strategy69.
Proof.
  pre_process_default.
  unfold learning_focus_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy70_correctness : CDCL_qcp_strategy70.
Proof.
  pre_process_default.
  unfold learning_focus_state.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy71_correctness : CDCL_qcp_strategy71.
Proof.
  pre_process_default.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy72_correctness : CDCL_qcp_strategy72.
Proof.
  pre_process_default.
  unfold solver_explicit_state.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma CDCL_qcp_strategy75_correctness : CDCL_qcp_strategy75.
Proof.
  pre_process_default.
  unfold backtrack_inner_state.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy76_correctness : CDCL_qcp_strategy76.
Proof.
  pre_process_default.
  unfold backtrack_inner_state.
  entailer!.
Qed.

(* Rules 73/74: the Wave-2 focused-row head H1.  Same shape as 49/50 --
   unfold the head, hand back v_data/cl_data, cancel; the left rule ends
   with the sepcon-adjoint step because the erased conjunct leaves an emp
   on one side. *)

Lemma CDCL_qcp_strategy73_correctness : CDCL_qcp_strategy73.
Proof.
  pre_process_default.
  unfold solver_row_focus_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy74_correctness : CDCL_qcp_strategy74.
Proof.
  pre_process_default.
  unfold solver_row_focus_state.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.

(* Rules 77/78: backtrack's focused-row wrapper.  The wrapper binds no
   existentials of its own -- v_data/cl_data live inside the H1 instance,
   which stays folded on BOTH sides -- so each proof is one unfold and one
   entailer!.  entailer! splits the definition's pure conjunction against
   the individually emitted facts, exactly as it does for rules 63/64.  No
   sepcon-adjoint tail on 78: the folded H1 atom survives on the right, so
   the erased conjunct leaves no emp-only side, and the file's no-[try]
   hygiene makes a superfluous tail fail loudly with "No such goal". *)

Lemma CDCL_qcp_strategy77_correctness : CDCL_qcp_strategy77.
Proof.
  pre_process_default.
  unfold backtrack_row_focus_state.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy78_correctness : CDCL_qcp_strategy78.
Proof.
  pre_process_default.
  unfold backtrack_row_focus_state.
  entailer!.
Qed.

(* Rules 79/80: bcp's clause-update head (design ruling A9).  Same shape as
   63/64: the definition carries an element-store cell
   (StoreIntAsElement.storeA) whose body uses sizeof(INT) while the rule
   emits the raw data_at form, so the unfold direction normalises it with
   fold_arch + the sizeof(FET_int) change exactly as rule 64 does; the fold
   direction needs no normalisation (compare 63/65, whose definitions also
   carry storeA cells).  The two EX binders are the struct-pointer
   intermediates, as everywhere in this family. *)

Lemma CDCL_qcp_strategy79_correctness : CDCL_qcp_strategy79.
Proof.
  pre_process_default.
  unfold bcp_clause_update_state.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma CDCL_qcp_strategy80_correctness : CDCL_qcp_strategy80.
Proof.
  pre_process_default.
  unfold bcp_clause_update_state, StoreIntAsElement.storeA.
  fold_arch.
  change (sizeof_front_end_type FET_int) with 4.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
  apply_sepcon_adjoint. elim_emp. cancel.
Qed.
