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

Lemma proof_of_bcp_entail_wit_10_1 : bcp_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 = 1) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = 1) as Hcell_i2.
  bind_fact (i_2 <> unitcl) as Hne_i2.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconflict_wit & Hno_conflict).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hcell_unit Hvalue_cell] | [Hcell_unit Hvalue_cell]];
    [ | exfalso; lia ].
  assert (Hb : b_2 = true).
  {
    eapply assigns_one_replaced_one_true__bcp_assignment_summary_d;
      try eassumption; try (split; lia).
    rewrite Hvalue_cell in Hvalues_upd; exact Hvalues_upd.
  }
  subst b_2.
  pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
    F n live original_count snap i_2 Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (dense_decode_counts_pos__bcp_assignment_summary_a
    n (Znth i_2 (snap_rows snap) (@nil Z)) bcpvar true Hrow_wf
    ltac:(split; lia) Hcell_i2) as [Hvar_d Htrue_d].
  simpl in Htrue_d.
  rewrite Hcs.
  Right.
  set (next_true :=
    replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2).
  set (next_unassigned :=
    replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2).
  set (next_states := replace_Znth i_2 0 cur_states_2).
  Exists next_true next_unassigned value_cell_2 true new_snap_2 ranks1_2
    next_states (i_2 + 1).
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
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar true logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 1
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_i2
      Hcell_unit Hvar_d Htrue_d ltac:(left; reflexivity))
      as [Hadvance _].
    exact Hadvance.
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar true logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 1
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_i2
      Hcell_unit Hvar_d Htrue_d ltac:(left; reflexivity))
      as [_ Hnext].
    exact Hnext.
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar true logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 1
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_i2
      Hcell_unit Hvar_d Htrue_d ltac:(left; reflexivity))
      as [Hadvance _].
    pose proof Hmixed as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    subst next_states.
    split.
    + intro Hconflict.
      pose proof (Hconflict_wit Hconflict) as [Hc0 [Hci Hcell]].
      split; [lia | split; [lia |]].
      rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
      exact Hcell.
    + intros Hconflict k Hk.
      destruct (Z.eq_dec k i_2) as [->|Hki].
      * rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia); lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
        apply (Hno_conflict Hconflict k); lia.
Qed.

Lemma proof_of_bcp_entail_wit_10_2 : bcp_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 = 0) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = (-1)) as Hcell_i2.
  bind_fact (i_2 <> unitcl) as Hne_i2.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconflict_wit & Hno_conflict).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hcell_unit Hvalue_cell] | [Hcell_unit Hvalue_cell]];
    [ exfalso; lia | ].
  assert (Hb : b_2 = false).
  {
    eapply assigns_one_replaced_zero_false__bcp_assignment_summary_d;
      try eassumption; try (split; lia).
    rewrite Hvalue_cell in Hvalues_upd; exact Hvalues_upd.
  }
  subst b_2.
  pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
    F n live original_count snap i_2 Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (dense_decode_counts_neg__bcp_assignment_summary_a
    n (Znth i_2 (snap_rows snap) (@nil Z)) bcpvar false Hrow_wf
    ltac:(split; lia) Hcell_i2) as [Hvar_d Htrue_d].
  simpl in Htrue_d.
  rewrite Hcs.
  Right.
  set (next_true :=
    replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2).
  set (next_unassigned :=
    replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2).
  set (next_states := replace_Znth i_2 0 cur_states_2).
  Exists next_true next_unassigned value_cell_2 false new_snap_2 ranks1_2
    next_states (i_2 + 1).
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
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar false logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 1
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_i2
      Hcell_unit Hvar_d Htrue_d ltac:(left; reflexivity))
      as [Hadvance _].
    exact Hadvance.
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar false logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 1
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_i2
      Hcell_unit Hvar_d Htrue_d ltac:(left; reflexivity))
      as [_ Hnext].
    exact Hnext.
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar false logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 1
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_i2
      Hcell_unit Hvar_d Htrue_d ltac:(left; reflexivity))
      as [Hadvance _].
    pose proof Hmixed as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    subst next_states.
    split.
    + intro Hconflict.
      pose proof (Hconflict_wit Hconflict) as [Hc0 [Hci Hcell]].
      split; [lia | split; [lia |]].
      rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
      exact Hcell.
    + intros Hconflict k Hk.
      destruct (Z.eq_dec k i_2) as [->|Hki].
      * rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia); lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
        apply (Hno_conflict Hconflict k); lia.
Qed.

Lemma proof_of_bcp_entail_wit_10_3 : bcp_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 0) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = (-1)) as Hrow_cell.
  bind_fact (i_2 <> unitcl) as Hne_unit.
  bind_fact (current_state = (Znth (i_2) (cur_states_2) (0))) as Hstate_old.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
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
  assert (Hb : b_2 = true).
  {
    eapply assigns_one_replaced_one_true__bcp_assignment_summary_d;
      try eassumption; try (split; lia).
    rewrite Hvc in Hvalues_upd; exact Hvalues_upd.
  }
  subst b_2.
  pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
    F n live original_count snap i_2 Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (dense_decode_counts_neg__bcp_assignment_summary_a
    n (Znth i_2 (snap_rows snap) (@nil Z)) bcpvar true Hrow_wf
    ltac:(split; lia) Hrow_cell) as [Hvar_d Htrue_d].
  simpl in Htrue_d.
  rewrite Hcs.
  Right.
  Exists cur_true_2
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
  - pose proof Hmixed as Hlens.
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
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar true logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 0
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_unit
      Hunit_cell Hvar_d Htrue_d
      ltac:(right; split; [reflexivity | rewrite <- Hstate_old; exact Hcs]))
      as [_ Hnext].
    exact Hnext.
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar true logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 0
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_unit
      Hunit_cell Hvar_d Htrue_d
      ltac:(right; split; [reflexivity | rewrite <- Hstate_old; exact Hcs]))
      as [Hadvance _].
    pose proof Hmixed as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [_ [Htrue0 _]]].
    replace (Znth i_2 cur_true_2 0 + 0) with (Znth i_2 cur_true_2 0)
      in Hadvance by lia.
    rewrite replace_Znth_Znth in Hadvance by (rewrite Htrue0; lia).
    split; [exact Hassigns_one | split; [lia | exact Hadvance]].
Qed.

Lemma proof_of_bcp_entail_wit_10_4 : bcp_entail_wit_10_4.
Proof.
 unfold variable_arrays_rep.
 solve_bcp_row_domain_absurd F n live original_count snap i_2 bcpvar Hrow_wf.
Qed.

Lemma proof_of_bcp_entail_wit_10_5 : bcp_entail_wit_10_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 1) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = 1) as Hrow_cell.
  bind_fact (i_2 <> unitcl) as Hne_unit.
  bind_fact (current_state = (Znth (i_2) (cur_states_2) (0))) as Hstate_old.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
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
  assert (Hb : b_2 = false).
  {
    eapply assigns_one_replaced_zero_false__bcp_assignment_summary_d;
      try eassumption; try (split; lia).
    rewrite Hvc in Hvalues_upd; exact Hvalues_upd.
  }
  subst b_2.
  pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
    F n live original_count snap i_2 Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (dense_decode_counts_pos__bcp_assignment_summary_a
    n (Znth i_2 (snap_rows snap) (@nil Z)) bcpvar false Hrow_wf
    ltac:(split; lia) Hrow_cell) as [Hvar_d Htrue_d].
  simpl in Htrue_d.
  rewrite Hcs.
  Right.
  Exists cur_true_2
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
  - pose proof Hmixed as Hlens.
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
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar false logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 0
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_unit
      Hunit_cell Hvar_d Htrue_d
      ltac:(right; split; [reflexivity | rewrite <- Hstate_old; exact Hcs]))
      as [_ Hnext].
    exact Hnext.
  - pose proof (bcp_advance_satisfied_dense__bcp_scan_invariant
      F n live original_count snap ranks logical_dl
      (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl)
      bcpvar false logical_dl unitcl cur_states_2 cur_true_2 cur_unassigned_2
      cap i_2 unitcl 0
      Hcoh Hassigns_one Hready Hmixed
      ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) Hne_unit
      Hunit_cell Hvar_d Htrue_d
      ltac:(right; split; [reflexivity | rewrite <- Hstate_old; exact Hcs]))
      as [Hadvance _].
    pose proof Hmixed as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [_ [Htrue0 _]]].
    replace (Znth i_2 cur_true_2 0 + 0) with (Znth i_2 cur_true_2 0)
      in Hadvance by lia.
    rewrite replace_Znth_Znth in Hadvance by (rewrite Htrue0; lia).
    split; [exact Hassigns_one | split; [lia | exact Hadvance]].
Qed.

Lemma proof_of_bcp_entail_wit_10_6 : bcp_entail_wit_10_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 = 1) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = 1) as Hrow_cell.
  bind_fact (i_2 <> unitcl) as Hne_unit.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
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
  assert (Hmix_next :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i_2 0 cur_states_2)
      (replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2)
      (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1)
        cur_unassigned_2)
      live cap (i_2 + 1) (Some unitcl)).
  {
    eapply bcp_summary_assign_satisfied_step__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix.
    - lia.
    - lia.
    - lia.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + lia.
      + lia.
      + exact Hrow_cell.
  }
  assert (Hnext :
    Znth (i_2 + 1) (replace_Znth i_2 0 cur_states_2) 0 <> 1).
  {
    eapply bcp_next_state_not_conflict__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix_next.
    - exact Hready.
    - lia.
    - exact Hexempt.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + exact Hexempt.
      + lia.
      + exact Hunit_cell.
  }
  rewrite bcp_replace_Znth_collapse.
  Right.
  set (next_true :=
    replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2).
  set (next_unassigned :=
    replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2).
  set (next_states := replace_Znth i_2 0 cur_states_2).
  Exists next_true next_unassigned value_cell_2 true new_snap_2 ranks1_2
    next_states (i_2 + 1).
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
  - pose proof Hmixed as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    subst next_states.
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

Lemma proof_of_bcp_entail_wit_10_7 : bcp_entail_wit_10_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 = 0) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = (-1)) as Hrow_cell.
  bind_fact (i_2 <> unitcl) as Hne_unit.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
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
  assert (Hmix_next :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i_2 0 cur_states_2)
      (replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2)
      (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1)
        cur_unassigned_2)
      live cap (i_2 + 1) (Some unitcl)).
  {
    eapply bcp_summary_assign_satisfied_step__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix.
    - lia.
    - lia.
    - lia.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + lia.
      + lia.
      + exact Hrow_cell.
  }
  assert (Hnext :
    Znth (i_2 + 1) (replace_Znth i_2 0 cur_states_2) 0 <> 1).
  {
    eapply bcp_next_state_not_conflict__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix_next.
    - exact Hready.
    - lia.
    - exact Hexempt.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + exact Hexempt.
      + lia.
      + exact Hunit_cell.
  }
  rewrite bcp_replace_Znth_collapse.
  Right.
  set (next_true :=
    replace_Znth i_2 (Znth i_2 cur_true_2 0 + 1) cur_true_2).
  set (next_unassigned :=
    replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2).
  set (next_states := replace_Znth i_2 0 cur_states_2).
  Exists next_true next_unassigned value_cell_2 false new_snap_2 ranks1_2
    next_states (i_2 + 1).
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
  - pose proof Hmixed as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    subst next_states.
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

Lemma proof_of_bcp_entail_wit_10_8 : bcp_entail_wit_10_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 0) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i) ((snap_rows (snap))) ((@nil Z))) 0 = (-1)) as Hrow_cell.
  bind_fact (i <> unitcl) as Hne_unit.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ | exfalso; lia ].
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
  assert (Hmix_next :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i 1 cur_states_2) cur_true_2
      (replace_Znth i (Znth i cur_unassigned_2 0 - 1) cur_unassigned_2)
      live cap (i + 1) (Some unitcl)).
  {
    eapply bcp_summary_assign_falsified_step__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix.
    - lia.
    - lia.
    - lia.
    - eapply coherent_snapshot_dense_falsified_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + lia.
      + lia.
      + exact Hrow_cell.
  }
  assert (Hnext :
    Znth (i + 1) (replace_Znth i 1 cur_states_2) 0 <> 1).
  {
    eapply bcp_next_state_not_conflict__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix_next.
    - exact Hready.
    - lia.
    - exact Hexempt.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + exact Hexempt.
      + lia.
      + exact Hunit_cell.
  }
  rewrite bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i (Znth i cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 true new_snap_2 ranks1_2
    (replace_Znth i 1 cur_states_2) (i + 1).
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
      row_table live i row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
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
    + intro Hne_minus.
      split; [lia | split; [lia |]].
      rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia).
      reflexivity.
    + intro Hminus.
      lia.
  - split; [exact Hassign | split; [exact Hexempt | exact Hmix_next]].
Qed.

Lemma proof_of_bcp_entail_wit_10_9 : bcp_entail_wit_10_9.
Proof.
 unfold variable_arrays_rep.
 solve_bcp_cell_domain_absurd F n live original_count snap i bcpvar.
Qed.

Lemma proof_of_bcp_entail_wit_10_10 : bcp_entail_wit_10_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 1) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i) ((snap_rows (snap))) ((@nil Z))) 0 = 1) as Hrow_cell.
  bind_fact (i <> unitcl) as Hne_unit.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ exfalso; lia | ].
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
  assert (Hmix_next :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i 1 cur_states_2) cur_true_2
      (replace_Znth i (Znth i cur_unassigned_2 0 - 1) cur_unassigned_2)
      live cap (i + 1) (Some unitcl)).
  {
    eapply bcp_summary_assign_falsified_step__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix.
    - lia.
    - lia.
    - lia.
    - eapply coherent_snapshot_dense_falsified_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + lia.
      + lia.
      + exact Hrow_cell.
  }
  assert (Hnext :
    Znth (i + 1) (replace_Znth i 1 cur_states_2) 0 <> 1).
  {
    eapply bcp_next_state_not_conflict__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix_next.
    - exact Hready.
    - lia.
    - exact Hexempt.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + exact Hexempt.
      + lia.
      + exact Hunit_cell.
  }
  rewrite bcp_replace_Znth_collapse.
  Right.
  set (next_unassigned :=
    replace_Znth i (Znth i cur_unassigned_2 0 - 1) cur_unassigned_2).
  set (next_states := replace_Znth i 1 cur_states_2).
  Exists cur_true_2 next_unassigned value_cell_2 false new_snap_2 ranks1_2
    next_states (i + 1).
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
      row_table live i row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr.
    fold_arch.
    sep_apply Hmerge.
    cancel.
  - pose proof Hmix as Hlens.
    unfold mixed_clause_summaries in Hlens.
    destruct Hlens as [_ [Hstates _]].
    subst next_states.
    split.
    + intro Hne_minus.
      split; [lia | split; [lia |]].
      rewrite Znth_replace_Znth_Same by (rewrite Hstates; lia).
      reflexivity.
    + intro Hminus.
      lia.
  - split; [exact Hassign | split; [exact Hexempt | exact Hmix_next]].
Qed.

Lemma proof_of_bcp_entail_wit_10_11 : bcp_entail_wit_10_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 0) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = (-1)) as Hrow_cell.
  bind_fact (i_2 <> unitcl) as Hne_unit.
  bind_fact (conflict <> (-1)) as Hconf_ne.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ | exfalso; lia ].
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
  assert (Hmix_next :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i_2 1 cur_states_2) cur_true_2
      (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
      live cap (i_2 + 1) (Some unitcl)).
  {
    eapply bcp_summary_assign_falsified_step__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix.
    - lia.
    - lia.
    - lia.
    - eapply coherent_snapshot_dense_falsified_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + lia.
      + lia.
      + exact Hrow_cell.
  }
  assert (Hnext :
    Znth (i_2 + 1) (replace_Znth i_2 1 cur_states_2) 0 <> 1).
  {
    eapply bcp_next_state_not_conflict__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix_next.
    - exact Hready.
    - lia.
    - exact Hexempt.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + exact Hexempt.
      + lia.
      + exact Hunit_cell.
  }
  rewrite bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 true new_snap_2 ranks1_2
    (replace_Znth i_2 1 cur_states_2) (i_2 + 1).
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
    + intro Habs.
      contradiction.
  - split; [exact Hassign | split; [exact Hexempt | exact Hmix_next]].
Qed.

Lemma proof_of_bcp_entail_wit_10_12 : bcp_entail_wit_10_12.
Proof.
 unfold variable_arrays_rep.
 solve_bcp_cell_domain_absurd F n live original_count snap i_2 bcpvar.
Qed.

Lemma proof_of_bcp_entail_wit_10_13 : bcp_entail_wit_10_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold variable_arrays_rep.
  bcp_scan_prelude current_state Hmixed Hcs.
  bind_fact (Znth bcpvar (snap_values (new_snap_2)) 0 <> 1) as Hval_read.
  bind_fact (Znth bcpvar (Znth (i_2) ((snap_rows (snap))) ((@nil Z))) 0 = 1) as Hrow_cell.
  bind_fact (i_2 <> unitcl) as Hne_unit.
  bind_fact (conflict <> (-1)) as Hconf_ne.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  match goal with
  | Hd : bcp_assignment_delta _ _ _ _ _ _ _ _ _ _ |- _ => rename Hd into Hdelta
  end.
  match goal with
  | Hp : bcp_conflict_prefix _ _ _ |- _ => rename Hp into Hprefix
  end.
  pose proof Hprefix as (Hconf_found & Hconf_clear).
  pose proof Hdelta as
    (Hrows_eq & Hpol & Hvalues_upd & Hreasons_upd & Hlevels_upd & Hassigns_one).
  pose proof Hcoh as Hcoh_len.
  unfold coherent_snapshot in Hcoh_len.
  destruct Hcoh_len as (_ & _ & Hlengths & _ & _ & _).
  destruct Hlengths as (Hvalues_length & _).
  rewrite Hvalues_upd in Hval_read.
  rewrite Znth_replace_Znth_Same in Hval_read
    by (rewrite Hvalues_length; lia).
  destruct Hpol as [[Hunit_cell Hvc] | [Hunit_cell Hvc]];
    [ exfalso; lia | ].
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
  assert (Hmix_next :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap_2 ranks1_2 logical_dl))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i_2 1 cur_states_2) cur_true_2
      (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
      live cap (i_2 + 1) (Some unitcl)).
  {
    eapply bcp_summary_assign_falsified_step__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix.
    - lia.
    - lia.
    - lia.
    - eapply coherent_snapshot_dense_falsified_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + lia.
      + lia.
      + exact Hrow_cell.
  }
  assert (Hnext :
    Znth (i_2 + 1) (replace_Znth i_2 1 cur_states_2) 0 <> 1).
  {
    eapply bcp_next_state_not_conflict__bcp_assignment_summary_b.
    - exact Hassign.
    - exact Hmix_next.
    - exact Hready.
    - lia.
    - exact Hexempt.
    - eapply coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b.
      + exact Hcoh.
      + exact Hexempt.
      + lia.
      + exact Hunit_cell.
  }
  rewrite bcp_replace_Znth_collapse.
  Right.
  Exists cur_true_2
    (replace_Znth i_2 (Znth i_2 cur_unassigned_2 0 - 1) cur_unassigned_2)
    value_cell_2 false new_snap_2 ranks1_2
    (replace_Znth i_2 1 cur_states_2) (i_2 + 1).
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
    + intro Habs.
      contradiction.
  - split; [exact Hassign | split; [exact Hexempt | exact Hmix_next]].
Qed.
