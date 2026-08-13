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
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_lib.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_common.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_bcp_entail_wit_10_14 : bcp_entail_wit_10_14.
Proof.
  aggressive_pre_process.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 = 1) as Hval_read.
  bind_fact (Znth bcpvar (Znth i_2 (snap_rows snap) (@nil Z)) 0 = 1) as Hrow_cell.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot n snap ranks logical_dl)) as Hready.
  bind_fact (i_2 <> unitcl) as Hi_ne_unit.
  bind_fact (current_state = Znth i_2 cur_states_2 0) as Hcur_state.
  bind_fact (Znth i_2 (replace_Znth i_2 current_state cur_states_2) 0 <> 0)
    as Hstate_nz.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ | exfalso; lia ].
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  assert (Hb : b_2 = true).
  {
    eapply assigns_one_replaced_one_true__bcp_assignment_summary_d;
      try eassumption; try (split; lia).
    rewrite Hvc in Hvalues_upd; exact Hvalues_upd.
  }
  subst b_2.
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hs as [Hassign [Hexempt Hmix]]
  end.
  assert (Hold_true_zero : Znth i_2 cur_true_2 0 = 0).
  { pose proof (mixed_clause_summaries_old_at_processed__bcp_assignment_summary_a
      _ _ _ _ _ _ _ _ _ _ Hmix ltac:(lia) Hi_ne_unit) as Hold_summary.
    unfold summary_at, clause_summary_ok in Hold_summary.
    destruct Hold_summary as [Htrue0 [_ Hstate0]].
    rewrite <- Hcur_state in Hstate0.
    unfold expected_clause_state in Hstate0.
    pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Znth i_2
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal))) as Hnn0.
    rewrite Htrue0.
    destruct ((0 <? clause_true_count
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Znth i_2
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal)))%Z) eqn:Hpos0.
    - exfalso; apply Hstate_nz; exact Hstate0.
    - apply Z.ltb_ge in Hpos0; lia. }
  pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
    F n live original_count snap i_2 Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (dense_decode_counts_pos__bcp_assignment_summary_a
    n (Znth i_2 (snap_rows snap) (@nil Z)) bcpvar true Hrow_wf
    ltac:(split; lia) Hrow_cell) as [Hvar_d Htrue_d].
  pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
    F n live original_count snap ranks logical_dl
    (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
    bcpvar true logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
    cap i_2 unitcl 1
    Hcoh Hassign Hready Hmix
    ltac:(split; lia) Hexempt ltac:(split; lia) Hi_ne_unit
    Hunit_cell Hvar_d Htrue_d ltac:(left; reflexivity)) as [Hmix_next Hnext].
  rewrite bcp_replace_Znth_collapse.
  replace (replace_Znth i_2 1 cur_true_2)
    with (replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2)
    by (rewrite Hold_true_zero; reflexivity).
  Right.
  Exists (replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2)
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 true new_snap_2 ranks1_2
    (replace_Znth i_2 0 cur_states_2) (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  cdcl_split_pure_spatial.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - pose proof Hmix as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    split.
    + intro Hconflict.
      pose proof (Hconf_found Hconflict) as [Hc0 [Hci Hcell]].
      split; [lia | split; [lia |]].
      rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
      exact Hcell.
    + intros Hconflict k Hk.
      destruct (Z.eq_dec k i_2) as [->|Hki].
      * rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia); lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
        apply (Hconf_clear Hconflict k); lia.
  - split; [exact Hassign | split; [exact Hexempt | exact Hmix_next]].
Qed.

Lemma proof_of_bcp_entail_wit_10_15 : bcp_entail_wit_10_15.
Proof.
  aggressive_pre_process.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 = 0) as Hval_read.
  bind_fact (Znth bcpvar (Znth i_2 (snap_rows snap) (@nil Z)) 0 = (-1)) as Hrow_cell.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot n snap ranks logical_dl)) as Hready.
  bind_fact (i_2 <> unitcl) as Hi_ne_unit.
  bind_fact (current_state = Znth i_2 cur_states_2 0) as Hcur_state.
  bind_fact (Znth i_2 (replace_Znth i_2 current_state cur_states_2) 0 <> 0)
    as Hstate_nz.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ exfalso; lia | ].
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  assert (Hb : b_2 = false).
  {
    eapply assigns_one_replaced_zero_false__bcp_assignment_summary_d;
      try eassumption; try (split; lia).
    rewrite Hvc in Hvalues_upd; exact Hvalues_upd.
  }
  subst b_2.
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hs as [Hassign [Hexempt Hmix]]
  end.
  assert (Hold_true_zero : Znth i_2 cur_true_2 0 = 0).
  { pose proof (mixed_clause_summaries_old_at_processed__bcp_assignment_summary_a
      _ _ _ _ _ _ _ _ _ _ Hmix ltac:(lia) Hi_ne_unit) as Hold_summary.
    unfold summary_at, clause_summary_ok in Hold_summary.
    destruct Hold_summary as [Htrue0 [_ Hstate0]].
    rewrite <- Hcur_state in Hstate0.
    unfold expected_clause_state in Hstate0.
    pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Znth i_2
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal))) as Hnn0.
    rewrite Htrue0.
    destruct ((0 <? clause_true_count
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Znth i_2
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal)))%Z) eqn:Hpos0.
    - exfalso; apply Hstate_nz; exact Hstate0.
    - apply Z.ltb_ge in Hpos0; lia. }
  pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
    F n live original_count snap i_2 Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (dense_decode_counts_neg__bcp_assignment_summary_a
    n (Znth i_2 (snap_rows snap) (@nil Z)) bcpvar false Hrow_wf
    ltac:(split; lia) Hrow_cell) as [Hvar_d Htrue_d].
  pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
    F n live original_count snap ranks logical_dl
    (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
    bcpvar false logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
    cap i_2 unitcl 1
    Hcoh Hassign Hready Hmix
    ltac:(split; lia) Hexempt ltac:(split; lia) Hi_ne_unit
    Hunit_cell Hvar_d Htrue_d ltac:(left; reflexivity)) as [Hmix_next Hnext].
  rewrite bcp_replace_Znth_collapse.
  replace (replace_Znth i_2 1 cur_true_2)
    with (replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2)
    by (rewrite Hold_true_zero; reflexivity).
  Right.
  Exists (replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2)
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 false new_snap_2 ranks1_2
    (replace_Znth i_2 0 cur_states_2) (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  cdcl_split_pure_spatial.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - pose proof Hmix as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    split.
    + intro Hconflict.
      pose proof (Hconf_found Hconflict) as [Hc0 [Hci Hcell]].
      split; [lia | split; [lia |]].
      rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
      exact Hcell.
    + intros Hconflict k Hk.
      destruct (Z.eq_dec k i_2) as [->|Hki].
      * rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia); lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
        apply (Hconf_clear Hconflict k); lia.
  - split; [exact Hassign | split; [exact Hexempt | exact Hmix_next]].
Qed.

Lemma proof_of_bcp_entail_wit_10_16 : bcp_entail_wit_10_16.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmix_pre Hcs_pre.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 0) as Hval_read.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ | exfalso; lia ].
  rewrite ?bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 b_2 new_snap_2 ranks1_2
    (replace_Znth i_2 2 cur_states_2) (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  cdcl_split_pure_spatial.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - cdcl_solve_bcp_prefix_advance.
  - derive_bcp_advance_false true 2 b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    exact Hnext.
  - derive_bcp_advance_false true 2 b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    cdcl_pack_bcp_advance.
Qed.

Lemma proof_of_bcp_entail_wit_10_17 : bcp_entail_wit_10_17.
Proof.
 unfold variable_arrays_rep.
 solve_bcp_cell_domain_absurd F n live original_count snap i_2 bcpvar.
Qed.

Lemma proof_of_bcp_entail_wit_10_18 : bcp_entail_wit_10_18.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmix_pre Hcs_pre.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 1) as Hval_read.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ exfalso; lia | ].
  rewrite ?bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 b_2 new_snap_2 ranks1_2
    (replace_Znth i_2 2 cur_states_2) (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  cdcl_split_pure_spatial.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - cdcl_solve_bcp_prefix_advance.
  - derive_bcp_advance_false false 2 b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    exact Hnext.
  - derive_bcp_advance_false false 2 b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    cdcl_pack_bcp_advance.
Qed.

Lemma proof_of_bcp_entail_wit_10_19 : bcp_entail_wit_10_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmix_pre Hcs_pre.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 0) as Hval_read.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ | exfalso; lia ].
  rewrite ?bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 b_2 new_snap_2 ranks1_2
    (replace_Znth i_2 (current_state + 1) cur_states_2) (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel; try simpl_entail.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - derive_bcp_advance_false true uconstr:(current_state + 1) b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    split_pures; try dump_pre_spatial;
      try cdcl_solve_bcp_prefix_advance;
      try cdcl_pack_bcp_advance;
      try exact Hnext;
      try exact Hadvance;
      try assumption;
      try reflexivity;
      try lia.
  - derive_bcp_advance_false true uconstr:(current_state + 1) b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    exact Hnext.
  - derive_bcp_advance_false true uconstr:(current_state + 1) b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    cdcl_solve_bcp_prefix_advance.
Qed.

Lemma proof_of_bcp_entail_wit_10_20 : bcp_entail_wit_10_20.
Proof.
 unfold variable_arrays_rep.
 solve_bcp_cell_domain_absurd F n live original_count snap i_2 bcpvar.
Qed.

Lemma proof_of_bcp_entail_wit_10_21 : bcp_entail_wit_10_21.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmix_pre Hcs_pre.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 1) as Hval_read.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ exfalso; lia | ].
  rewrite ?bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 b_2 new_snap_2 ranks1_2
    (replace_Znth i_2 (current_state + 1) cur_states_2) (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel; try simpl_entail.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - derive_bcp_advance_false false uconstr:(current_state + 1) b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    split_pures; try dump_pre_spatial;
      try cdcl_solve_bcp_prefix_advance;
      try cdcl_pack_bcp_advance;
      try exact Hnext;
      try exact Hadvance;
      try assumption;
      try reflexivity;
      try lia.
  - derive_bcp_advance_false false uconstr:(current_state + 1) b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    exact Hnext.
  - derive_bcp_advance_false false uconstr:(current_state + 1) b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 current_state cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
    cdcl_solve_bcp_prefix_advance.
Qed.

Lemma proof_of_bcp_entail_wit_10_22 : bcp_entail_wit_10_22.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmix_pre Hcs_pre.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hmix_pre as Hlens_pre.
  unfold mixed_clause_summaries in Hlens_pre.
  destruct Hlens_pre as [_ [Hstates_pre _]].
  match goal with
  | Hcur : current_state = Znth i_2 cur_states_2 0 |- _ => rewrite Hcur
  end.
  rewrite replace_Znth_Znth by (rewrite Hstates_pre; lia).
  Right.
  Exists cur_true_2 cur_unassigned_2 value_cell_2 b_2 new_snap_2 ranks1_2
    cur_states_2 (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  cdcl_split_pure_spatial.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - split.
    + intro Hconflict.
      pose proof (Hconf_found Hconflict) as [Hc0 [Hci Hcell]].
      split; [lia | split; [lia | exact Hcell]].
    + intros Hconflict k Hk.
      destruct (Z.eq_dec k i_2) as [->|Hki].
      * match goal with
        | Hcur : current_state = Znth i_2 cur_states_2 0 |- _ =>
            rewrite <- Hcur
        end.
        match goal with
        | Hne1 : current_state <> 1 |- _ => exact Hne1
        end.
      * apply (Hconf_clear Hconflict k); lia.
  - destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ derive_bcp_advance_same true b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; exact Hnext
    | derive_bcp_advance_same false b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; exact Hnext ].
  - destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]].
    + derive_bcp_advance_same true b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
      split; [exact Hassigns_one|].
      split; [split; [exact PreH9 | exact PreH10] | exact Hadvance].
    + derive_bcp_advance_same false b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap.
      split; [exact Hassigns_one|].
      split; [split; [exact PreH9 | exact PreH10] | exact Hadvance].
Qed.

Lemma proof_of_bcp_entail_wit_10_23 : bcp_entail_wit_10_23.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmix_pre Hcs_pre.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hmix_pre as Hlens_pre.
  unfold mixed_clause_summaries in Hlens_pre.
  destruct Hlens_pre as [_ [Hstates_pre _]].
  match goal with
  | Hcur : current_state = Znth i_2 cur_states_2 0 |- _ => rewrite Hcur
  end.
  rewrite replace_Znth_Znth by (rewrite Hstates_pre; lia).
  Right.
  Exists cur_true_2 cur_unassigned_2 value_cell_2 b_2 new_snap_2 ranks1_2
    cur_states_2 (i_2 + 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel; try simpl_entail.
  - pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ derive_bcp_advance_same true b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; assumption
    | derive_bcp_advance_same false b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; assumption ].
  - destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ derive_bcp_advance_same true b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; exact Hnext
    | derive_bcp_advance_same false b_2 value_cell_2 new_snap_2 snap bcpvar logical_dl unitcl i_2 cur_states_2 F n live original_count ranks ranks1_2 cur_true_2 cur_unassigned_2 cap; exact Hnext ].
  - split.
    + intro Hconflict.
      pose proof (Hconf_found Hconflict) as [Hc0 [Hci Hcell]].
      split; [lia | split; [lia | exact Hcell]].
    + intros Hconflict k Hk.
      destruct (Z.eq_dec k i_2) as [->|Hki].
      * match goal with
        | Hcur : current_state = Znth i_2 cur_states_2 0 |- _ =>
            rewrite <- Hcur
        end.
        match goal with
        | Hne1 : current_state <> 1 |- _ => exact Hne1
        end.
      * apply (Hconf_clear Hconflict k); lia.
Qed.

Lemma proof_of_bcp_entail_wit_11_2 : bcp_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  bind_fact (conflict <> (-1)) as Hconflict_ne.
  bind_fact (bcp_conflict_prefix conflict i cur_states) as Hprefix.
  bind_fact (0 <= unitcl) as Hunitcl_lo.
  bind_fact (unitcl < live) as Hunitcl_hi.
  bind_fact (0 <= bcpvar) as Hbcpvar_lo.
  bind_fact (bcpvar < n) as Hbcpvar_hi.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (stable_search_facts n new_snap ranks1 logical_dl) as Hstable_new.
  bind_fact (bcp_assignment_delta n snap new_snap ranks ranks1 bcpvar value_cell unitcl logical_dl b) as Hdelta.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  unfold bcp_conflict_prefix in Hprefix.
  destruct Hprefix as [Hconflict_hit _].
  unfold bcp_assignment_delta in Hdelta.
  destruct Hdelta as [Hrows_eq [Hpol [Hvalues_eq [Hreasons_eq [Hlevels_eq Hassign]]]]].
  assert (Hvc01 : value_cell = 0 \/ value_cell = 1)
    by (destruct Hpol as [[_ Hv]|[_ Hv]]; [right|left]; exact Hv).
  unfold solver_arrays_rep, variable_arrays_rep.
  unfold bcp_clause_scan, bcp_ready.
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end.
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hs as [_ [_ Hmixed]]
  end.
  pose proof (bcp_exit_snapshot_ready__bcp_exit_results
    F n live original_count cap snap new_snap ranks1 logical_dl
    bcpvar unitcl value_cell cur_states cur_true cur_unassigned i
    (conj Hbcpvar_lo Hbcpvar_hi) (conj Hunitcl_lo Hunitcl_hi) Hvc01
    Hcoh Hstable_new Hrows_eq Hvalues_eq Hreasons_eq Hlevels_eq Hmixed ltac:(lia))
    as [Hcoherent_final Hstable_final].
  pose proof (Hconflict_hit Hconflict_ne) as [Hconflict_lo [Hconflict_hi Hconflict_state]].
  assert (Hconflict_bounds : 0 <= conflict < live) by lia.
  assert (Hdense_new :
    dense_conflict_batch
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n new_snap ranks1 logical_dl)
      bcpvar).
  {
    eapply assigns_one_dense_conflict__bcp_exit_results.
    - exact Hready.
    - exact Hassign.
    - reflexivity.
  }
  assert (Hdense_final :
    dense_conflict_batch
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n
        (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
        ranks1 logical_dl)
      bcpvar).
  {
    rewrite (bcp_exit_view_eq__bcp_exit_results
      n snap new_snap ranks1 logical_dl
      cur_states cur_true cur_unassigned Hrows_eq).
    exact Hdense_new.
  }
  assert (Hlearning_final :
    exists c,
      nth_error
        (installed_clauses
          (cdcl_view_of_snapshot n
            (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
            ranks1 logical_dl))
        (Z.to_nat conflict) = Some c /\
      clause_false
        (assignment
          (cdcl_view_of_snapshot n
            (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
            ranks1 logical_dl)) c).
  {
    eapply coherent_state_one_conflict__bcp_exit_results.
    - exact Hcoherent_final.
    - exact Hconflict_bounds.
    - cbn.
      exact Hconflict_state.
  }
  Exists ranks1
    (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned).
  unfold learning_ready_conflict, bcp_ready.
  cbn.
  sep_apply (IntArray.full_to_seg states live cur_states).
  sep_apply (IntArray.full_to_seg true_counts live cur_true).
  sep_apply (IntArray.full_to_seg unassigned live cur_unassigned).
  unfold IntArray.seg.
  change (sizeof (INT)) with 4.
  entailer!.
Qed.

Lemma proof_of_bcp_entail_wit_11_1 : bcp_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  bind_fact (conflict <> (-1)) as Hconflict_ne.
  bind_fact (bcp_conflict_prefix conflict live cur_states) as Hprefix.
  bind_fact (0 <= unitcl) as Hunitcl_lo.
  bind_fact (unitcl < live) as Hunitcl_hi.
  bind_fact (0 <= bcpvar) as Hbcpvar_lo.
  bind_fact (bcpvar < n) as Hbcpvar_hi.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (stable_search_facts n new_snap ranks1 logical_dl) as Hstable_new.
  bind_fact (bcp_assignment_delta n snap new_snap ranks ranks1 bcpvar value_cell unitcl logical_dl b) as Hdelta.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  unfold bcp_conflict_prefix in Hprefix.
  destruct Hprefix as [Hconflict_hit _].
  unfold bcp_assignment_delta in Hdelta.
  destruct Hdelta as [Hrows_eq [Hpol [Hvalues_eq [Hreasons_eq [Hlevels_eq Hassign]]]]].
  assert (Hvc01 : value_cell = 0 \/ value_cell = 1)
    by (destruct Hpol as [[_ Hv]|[_ Hv]]; [right|left]; exact Hv).
  unfold solver_arrays_rep, variable_arrays_rep.
  unfold bcp_clause_scan, bcp_ready.
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end.
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hs as [_ [_ Hmixed]]
  end.
  pose proof (bcp_exit_snapshot_ready__bcp_exit_results
    F n live original_count cap snap new_snap ranks1 logical_dl
    bcpvar unitcl value_cell cur_states cur_true cur_unassigned live
    (conj Hbcpvar_lo Hbcpvar_hi) (conj Hunitcl_lo Hunitcl_hi) Hvc01
    Hcoh Hstable_new Hrows_eq Hvalues_eq Hreasons_eq Hlevels_eq Hmixed ltac:(lia))
    as [Hcoherent_final Hstable_final].
  pose proof (Hconflict_hit Hconflict_ne) as [Hconflict_lo [Hconflict_hi Hconflict_state]].
  assert (Hconflict_bounds : 0 <= conflict < live) by lia.
  assert (Hdense_new :
    dense_conflict_batch
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n new_snap ranks1 logical_dl)
      bcpvar).
  {
    eapply assigns_one_dense_conflict__bcp_exit_results.
    - exact Hready.
    - exact Hassign.
    - reflexivity.
  }
  assert (Hdense_final :
    dense_conflict_batch
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n
        (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
        ranks1 logical_dl)
      bcpvar).
  {
    rewrite (bcp_exit_view_eq__bcp_exit_results
      n snap new_snap ranks1 logical_dl
      cur_states cur_true cur_unassigned Hrows_eq).
    exact Hdense_new.
  }
  assert (Hlearning_final :
    exists c,
      nth_error
        (installed_clauses
          (cdcl_view_of_snapshot n
            (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
            ranks1 logical_dl))
        (Z.to_nat conflict) = Some c /\
      clause_false
        (assignment
          (cdcl_view_of_snapshot n
            (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
            ranks1 logical_dl)) c).
  {
    eapply coherent_state_one_conflict__bcp_exit_results.
    - exact Hcoherent_final.
    - exact Hconflict_bounds.
    - cbn.
      exact Hconflict_state.
  }
  Exists ranks1
    (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned).
  unfold learning_ready_conflict, bcp_ready.
  cbn.
  sep_apply (IntArray.full_to_seg states live cur_states).
  sep_apply (IntArray.full_to_seg true_counts live cur_true).
  sep_apply (IntArray.full_to_seg unassigned live cur_unassigned).
  unfold IntArray.seg.
  change (sizeof (INT)) with 4.
  entailer!.
Qed.

Lemma proof_of_bcp_entail_wit_12_2 : bcp_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  bind_fact (conflict = (-1)) as Hconflict_eq.
  bind_fact (bcp_conflict_prefix conflict i cur_states) as Hprefix.
  bind_fact (0 <= unitcl) as Hunitcl_lo.
  bind_fact (unitcl < live) as Hunitcl_hi.
  bind_fact (0 <= bcpvar) as Hbcpvar_lo.
  bind_fact (bcpvar < n) as Hbcpvar_hi.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (stable_search_facts n new_snap ranks1 logical_dl) as Hstable_new.
  bind_fact (bcp_assignment_delta n snap new_snap ranks ranks1 bcpvar value_cell unitcl logical_dl b) as Hdelta.
  unfold bcp_conflict_prefix in Hprefix.
  destruct Hprefix as [_ Hconflict_miss].
  unfold bcp_assignment_delta in Hdelta.
  destruct Hdelta as [Hrows_eq [Hpol [Hvalues_eq [Hreasons_eq [Hlevels_eq Hassign]]]]].
  assert (Hvc01 : value_cell = 0 \/ value_cell = 1)
    by (destruct Hpol as [[_ Hv]|[_ Hv]]; [right|left]; exact Hv).
  unfold solver_arrays_rep, variable_arrays_rep.
  unfold bcp_clause_scan, bcp_ready.
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end.
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hs as [_ [_ Hmixed]]
  end.
  pose proof (bcp_exit_snapshot_ready__bcp_exit_results
    F n live original_count cap snap new_snap ranks1 logical_dl
    bcpvar unitcl value_cell cur_states cur_true cur_unassigned i
    (conj Hbcpvar_lo Hbcpvar_hi) (conj Hunitcl_lo Hunitcl_hi) Hvc01
    Hcoh Hstable_new Hrows_eq Hvalues_eq Hreasons_eq Hlevels_eq Hmixed ltac:(lia))
    as [Hcoherent_final Hstable_final].
  assert (Hno_conflict_final :
    no_conflict
      (cdcl_view_of_snapshot n
        (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
        ranks1 logical_dl)).
  {
    eapply coherent_states_no_conflict__bcp_exit_results.
    - exact Hcoherent_final.
    - intros k Hk.
      cbn.
      apply (Hconflict_miss Hconflict_eq k).
      lia.
  }
  Exists ranks1
    (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned).
  cbn.
  sep_apply (IntArray.full_to_seg states live cur_states).
  sep_apply (IntArray.full_to_seg true_counts live cur_true).
  sep_apply (IntArray.full_to_seg unassigned live cur_unassigned).
  unfold IntArray.seg.
  change (sizeof (INT)) with 4.
  entailer!.
Qed.

Lemma proof_of_bcp_entail_wit_12_1 : bcp_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  bind_fact (conflict = (-1)) as Hconflict_eq.
  bind_fact (bcp_conflict_prefix conflict live cur_states) as Hprefix.
  bind_fact (0 <= unitcl) as Hunitcl_lo.
  bind_fact (unitcl < live) as Hunitcl_hi.
  bind_fact (0 <= bcpvar) as Hbcpvar_lo.
  bind_fact (bcpvar < n) as Hbcpvar_hi.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (stable_search_facts n new_snap ranks1 logical_dl) as Hstable_new.
  bind_fact (bcp_assignment_delta n snap new_snap ranks ranks1 bcpvar value_cell unitcl logical_dl b) as Hdelta.
  unfold bcp_conflict_prefix in Hprefix.
  destruct Hprefix as [_ Hconflict_miss].
  unfold bcp_assignment_delta in Hdelta.
  destruct Hdelta as [Hrows_eq [Hpol [Hvalues_eq [Hreasons_eq [Hlevels_eq Hassign]]]]].
  assert (Hvc01 : value_cell = 0 \/ value_cell = 1)
    by (destruct Hpol as [[_ Hv]|[_ Hv]]; [right|left]; exact Hv).
  unfold solver_arrays_rep, variable_arrays_rep.
  unfold bcp_clause_scan, bcp_ready.
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end.
  match goal with
  | Hs : _ /\ _ /\ mixed_clause_summaries _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hs as [_ [_ Hmixed]]
  end.
  pose proof (bcp_exit_snapshot_ready__bcp_exit_results
    F n live original_count cap snap new_snap ranks1 logical_dl
    bcpvar unitcl value_cell cur_states cur_true cur_unassigned live
    (conj Hbcpvar_lo Hbcpvar_hi) (conj Hunitcl_lo Hunitcl_hi) Hvc01
    Hcoh Hstable_new Hrows_eq Hvalues_eq Hreasons_eq Hlevels_eq Hmixed ltac:(lia))
    as [Hcoherent_final Hstable_final].
  assert (Hno_conflict_final :
    no_conflict
      (cdcl_view_of_snapshot n
        (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned)
        ranks1 logical_dl)).
  {
    eapply coherent_states_no_conflict__bcp_exit_results.
    - exact Hcoherent_final.
    - intros k Hk.
      cbn.
      apply (Hconflict_miss Hconflict_eq k).
      lia.
  }
  Exists ranks1
    (snapshot_after_scan new_snap snap cur_states cur_true cur_unassigned).
  cbn.
  sep_apply (IntArray.full_to_seg states live cur_states).
  sep_apply (IntArray.full_to_seg true_counts live cur_true).
  sep_apply (IntArray.full_to_seg unassigned live cur_unassigned).
  unfold IntArray.seg.
  change (sizeof (INT)) with 4.
  entailer!.
Qed.

