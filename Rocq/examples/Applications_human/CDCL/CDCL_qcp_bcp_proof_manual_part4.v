From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_bcp_goal.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_bcp_proof_auto.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_lib.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_common.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_tactics.
Import naive_C_Rules.
Local Open Scope sac.

Ltac poly_store_unfold := cbn [poly_store poly_undef_store].

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
  unfold bcp_clause_scan, bcp_ready.
  try poly_store_unfold.
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel; try simpl_entail.
  - unfold solver_explicit_state.
    Exists v_data cl_data.
    unfold sat_header_rep, var_header_rep, clause_header_rep,
      clause_arrays_explicit_rep, clause_summaries_explicit_rep,
      installed_rows_capacity_rep.
    try poly_store_unfold.
    pose proof (installed_row_focus_merge
      row_table live i_2 row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep in Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
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
  cdcl_entailer.
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
  cdcl_entailer.
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
  cdcl_entailer.
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
  cdcl_entailer.
Qed.



Lemma proof_of_bcp_return_wit_1 : bcp_return_wit_1.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists ranks1_2 snap1_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.


Lemma proof_of_bcp_return_wit_2 : bcp_return_wit_2.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists ranks1_2 snap1_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.


Lemma proof_of_bcp_return_wit_3 : bcp_return_wit_3.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists final_ranks final_snap.
  split_pure_spatial.
  - unfold propagation_result.
    Exists snap ranks bcpvar.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed.


Lemma proof_of_bcp_return_wit_4 : bcp_return_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (unit_scan (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) live i) as Hunit_scan.
  bind_fact (bcp_ready (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl))) as Hready.
  assert (Hno_unit :
    no_unit (cdcl_view_of_snapshot n snap ranks logical_dl)).
  {
    eapply (complete_unit_scan_no_unit__bcp_exit_results
      F n live original_count snap ranks logical_dl i).
    - exact Hcoh.
    - lia.
    - destruct Hunit_scan as [_ Hscan].
      exact Hscan.
  }
  assert (Hquiet :
    propagation_quiescent (cdcl_view_of_snapshot n snap ranks logical_dl)).
  {
    unfold propagation_quiescent, bcp_ready in *.
    split; [exact Hready | exact Hno_unit].
  }
  Exists ranks.
  split_pure_spatial.
  - cancel emp.
  - split_pures;
      dump_pre_spatial;
      try reflexivity;
      assumption.
Qed.



Lemma proof_of_bcp_entail_wit_9 : bcp_entail_wit_9.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  assert (Hrow_bound : 0 <= i < Zlength (snap_rows snap)).
  { pose proof Hcoh as Hcoherent.
    unfold coherent_snapshot in Hcoherent.
    destruct Hcoherent as (_ & _ & Hlengths & _ & _ & _).
    destruct Hlengths as (_ & _ & _ & Hrows_length & _ & _ & _).
    lia. }
  assert (Hrow_length : Zlength (Znth i (snap_rows snap) (@nil Z)) = n).
  { pose proof Hcoh as Hcoherent.
    unfold coherent_snapshot in Hcoherent.
    destruct Hcoherent as (_ & _ & _ & Hcells & _ & _).
    destruct Hcells as (_ & Hrows_wf).
    rewrite Forall_forall in Hrows_wf.
    apply Hrows_wf.
    unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrow_bound.
    lia. }
  Exists value_cell_2 b_2 new_snap_2 ranks1_2 cur_states_2.
  unfold bcp_clause_scan, bcp_ready.
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end.
  cdcl_entailer.
  rewrite (Znth_indep (snap_rows snap) i __default__List_Z (@nil Z))
    by exact Hrow_bound.
  cdcl_entailer.
Qed.

