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

Lemma proof_of_bcp_return_wit_1 : bcp_return_wit_1.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists ranks1_2 snap1_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_bcp_return_wit_2 : bcp_return_wit_2.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists ranks1_2 snap1_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
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
    + split_pures; dump_pre_spatial; try assumption; try lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
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
      try assumption.
Qed.


(* ===== backtrack entail wits (29 proofs) ===== *)
Lemma proof_of_backtrack_entail_wit_1 : backtrack_entail_wit_1.
Proof.
  unfold backtrack_entail_wit_1.
  left.
  intros.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  (* [backtrack]'s precondition is folded into [backjump_state] and its exit
     into [solver_state]; the two differ only by the promise and by the
     [variable_arrays_rep]/[unconstrained_Assignment] spelling, so the whole
     entailment is one head cancellation at [current_snap := snap]. *)
  Exists ranks snap.
  unfold backtrack_outer.
  entailer!.
  - unfold backjump_state, solver_state, unconstrained_Assignment.
    Intros s_pre_v_data s_pre_cl_data.
    Exists s_pre_v_data s_pre_cl_data.
    entailer!.
  - apply prefix_restriction_zero_same_snapshot__backtrack_entry_clear_a.
    lia.
  - cbn [cdcl_view_of_snapshot].
    apply coherent_snapshot_mixed_same__backtrack_entry_clear_a with
      (F := F) (original_count := original_count); assumption.
  - unfold coherent_snapshot in Hcoh.
    tauto.
  - unfold coherent_snapshot in Hcoh.
    tauto.
Qed.
Lemma proof_of_backtrack_entail_wit_2 : backtrack_entail_wit_2.
Proof.
  unfold backtrack_entail_wit_2.
  left.
  intros.
  LLM_pre_process ltac:(int_auto).
  bind_fact (Znth i (snap_levels current_snap_2) 0 > back_dl_pre) as Hlevel_pre.
  bind_fact (Znth i (snap_values current_snap_2) 0 <> (-1)) as Hvalue_pre.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_cur.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_cur.
  bind_fact (backtrack_outer
      (cdcl_view_of_snapshot n snap ranks conflict_dl)
      (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
      n back_dl_pre i live cap
      (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
      (snap_states current_snap_2) (snap_true_counts current_snap_2)
      (snap_unassigned current_snap_2)) as Houter.
  assert (Hvalues_length : Zlength (snap_values current_snap_2) = n).
  { unfold snapshot_lengths in Hlen_cur. tauto. }
  assert (Hlevels_length : Zlength (snap_levels current_snap_2) = n).
  { unfold snapshot_lengths in Hlen_cur. tauto. }
  assert (Hvalue_default :
      Znth i (snap_values current_snap_2) (-1) =
      Znth i (snap_values current_snap_2) 0).
  { apply Znth_indep. lia. }
  assert (Hlevel_default :
      Znth i (snap_levels current_snap_2) (-1) =
      Znth i (snap_levels current_snap_2) 0).
  { apply Znth_indep. lia. }
  assert (Hvalue_assigned :
      Znth i (snap_values current_snap_2) (-1) <> -1).
  { rewrite Hvalue_default. exact Hvalue_pre. }
  assert (Hlevel_above :
      Znth i (snap_levels current_snap_2) (-1) > back_dl_pre).
  { rewrite Hlevel_default. exact Hlevel_pre. }
  set (after_snap :=
    {| snap_values := replace_Znth i (-1) (snap_values current_snap_2);
       snap_reasons := replace_Znth i (-1) (snap_reasons current_snap_2);
       snap_levels := replace_Znth i (-1) (snap_levels current_snap_2);
       snap_rows := snap_rows current_snap_2;
       snap_states := snap_states current_snap_2;
       snap_true_counts := snap_true_counts current_snap_2;
       snap_unassigned := snap_unassigned current_snap_2 |}).
  set (after_ranks := fun y =>
    if Z.eq_dec y i then None else current_ranks_2 y).
  pose proof Houter as H.
  unfold backtrack_outer in H.
  Exists current_ranks_2 after_ranks after_snap
    (snap_states current_snap_2) (snap_true_counts current_snap_2)
    (snap_unassigned current_snap_2) current_snap_2.
  unfold backtrack_inner_state, solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep.
  unfold backtrack_inner.
  entailer!.
  (* The precondition spells the clause summaries `seg p 0 live`, the shared
     head spells the same assertion `full p live`; equal by definition, not by
     syntax. *)
  - unfold IntArray.full, IntArray.seg, store_array. entailer!.
  - subst after_snap.
    pose proof (cleared_snapshot_lengths_cells__backtrack_entry_clear_a
      n live current_snap_2 i Hlen_cur Hcells_cur ltac:(split; lia)) as Hafter.
    exact (proj1 Hafter).
  - subst after_snap.
    pose proof (cleared_snapshot_lengths_cells__backtrack_entry_clear_a
      n live current_snap_2 i Hlen_cur Hcells_cur ltac:(split; lia)) as Hafter.
    exact (proj2 Hafter).
  - subst after_snap. subst after_ranks.
    eapply cleared_snapshot_clears_one__backtrack_entry_clear_a
      with (live := live); eauto.
    split; lia.
  - destruct H as [_ [_ Hmix]].
    eapply mixed_clause_summaries_reset_zero__backtrack_entry_clear_a.
    exact Hmix.
Qed.
Lemma proof_of_backtrack_entail_wit_3 : backtrack_entail_wit_3.
Proof.
  unfold backtrack_entail_wit_3.
  left.
  intros.
  LLM_pre_process ltac:(int_auto).
  unfold installed_rows_capacity_rep.
  sep_apply (installed_row_focus_split row_table live j
    (snap_rows current_snap_2) ltac:(lia)).
  Intros row_ptr.
  Exists current_ranks_2 after_ranks_2 after_snap_2 row_ptr
    cur_states_2 cur_true_2 cur_unassigned_2 current_snap_2.
  unfold backtrack_row_focus_state, solver_row_focus_state.
  Exists v_data cl_data.
  unfold installed_row_focus_rep, sat_header_rep, var_header_rep,
    clause_header_rep, clause_summaries_explicit_rep.
  entailer!.
  apply snapshot_row_length__backtrack_entry_clear_a
    with (live := live); try assumption; lia.
Qed.

Lemma proof_of_backtrack_entail_wit_4_1 : backtrack_entail_wit_4_1.
Proof.
  unfold backtrack_entail_wit_4_1. right. intros. LLM_pre_process ltac:(int_auto).
  bind_fact (Znth i (snap_values current_snap_2) 0 = 1) as Hvalue_cell.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hrow_cell.
  bind_fact (Znth j cur_states_2 0 = 0) as Hstate_zero.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  assert (Hassign :
      assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some true).
  { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
      n current_snap_2 i true ltac:(get_values_len current_snap_2) ltac:(lia) Hvalue_cell). }
  assert (Hmap :
      Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (@nil literal)
      = dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
  { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_map; reflexivity. }
  pose proof (dense_decode_pos_counts__backtrack_entry_clear_a
    (Znth j (snap_rows current_snap_2) (@nil Z)) i ltac:(rewrite Hrow_len; lia) Hrow_cell) as [Hvar Hsat].
  rewrite <- Hmap in Hvar, Hsat.
  pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
    (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
    (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
    (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
    cur_states_2 cur_true_2 cur_unassigned_2 live cap j i true 1 0
    Hclear Hmix ltac:(lia) Hassign Hvar Hsat
    ltac:(left; repeat split; lia)) as Hmix_new.
  assert (Hstates_same : replace_Znth j 0 cur_states_2 = cur_states_2).
  { rewrite <- Hstate_zero. apply replace_Znth_Znth. }
  rewrite Hstates_same in Hmix_new.
  backtrack_advance_epilogue current_ranks_2 after_ranks_2 after_snap_2 current_snap_2 row_ptr j row_table live.
Qed.

Lemma proof_of_backtrack_entail_wit_4_2 : backtrack_entail_wit_4_2.
Proof.
  unfold backtrack_entail_wit_4_2. right. intros. LLM_pre_process ltac:(int_auto).
  bind_fact (Znth i (snap_values current_snap_2) 0 = 0) as Hvalue_cell.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = (-1)) as Hrow_cell.
  bind_fact (Znth j cur_states_2 0 = 0) as Hstate_zero.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  assert (Hassign :
      assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some false).
  { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
      n current_snap_2 i false ltac:(get_values_len current_snap_2) ltac:(lia) Hvalue_cell). }
  assert (Hmap :
      Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (@nil literal)
      = dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
  { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_map; reflexivity. }
  pose proof (dense_decode_neg_counts__backtrack_entry_clear_a
    (Znth j (snap_rows current_snap_2) (@nil Z)) i ltac:(rewrite Hrow_len; lia) Hrow_cell) as [Hvar Hsat].
  rewrite <- Hmap in Hvar, Hsat.
  pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
    (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
    (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
    (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
    cur_states_2 cur_true_2 cur_unassigned_2 live cap j i false 1 0
    Hclear Hmix ltac:(lia) Hassign Hvar Hsat
    ltac:(left; repeat split; lia)) as Hmix_new.
  assert (Hstates_same : replace_Znth j 0 cur_states_2 = cur_states_2).
  { rewrite <- Hstate_zero. apply replace_Znth_Znth. }
  rewrite Hstates_same in Hmix_new.
  backtrack_advance_epilogue current_ranks_2 after_ranks_2 after_snap_2 current_snap_2 row_ptr j row_table live.
Qed.

Lemma proof_of_backtrack_entail_wit_4_3 : backtrack_entail_wit_4_3.
Proof.
  unfold backtrack_entail_wit_4_3. right. intros. LLM_pre_process ltac:(int_auto).
  bind_fact (Znth i (snap_values current_snap_2) 0 = 1) as Hvalue_cell.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hrow_cell.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  assert (Hassign :
      assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some true).
  { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
      n current_snap_2 i true ltac:(get_values_len current_snap_2) ltac:(lia) Hvalue_cell). }
  assert (Hmap :
      Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (@nil literal)
      = dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
  { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_map; reflexivity. }
  pose proof (dense_decode_pos_counts__backtrack_entry_clear_a
    (Znth j (snap_rows current_snap_2) (@nil Z)) i ltac:(rewrite Hrow_len; lia) Hrow_cell) as [Hvar Hsat].
  rewrite <- Hmap in Hvar, Hsat.
  pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
    (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
    (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
    (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
    cur_states_2 cur_true_2 cur_unassigned_2 live cap j i true 1 (- Znth j cur_unassigned_2 0 - 1)
    Hclear Hmix ltac:(lia) Hassign Hvar Hsat
    ltac:(right; left; repeat split; lia)) as Hmix_new.
  backtrack_advance_epilogue current_ranks_2 after_ranks_2 after_snap_2 current_snap_2 row_ptr j row_table live.
Qed.

Lemma proof_of_backtrack_entail_wit_4_4 : backtrack_entail_wit_4_4.
Proof.
  unfold backtrack_entail_wit_4_4. right. intros. LLM_pre_process ltac:(int_auto).
  bind_fact (Znth i (snap_values current_snap_2) 0 = 0) as Hvalue_cell.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = (-1)) as Hrow_cell.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  assert (Hassign :
      assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some false).
  { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
      n current_snap_2 i false ltac:(get_values_len current_snap_2) ltac:(lia) Hvalue_cell). }
  assert (Hmap :
      Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (@nil literal)
      = dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
  { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_map; reflexivity. }
  pose proof (dense_decode_neg_counts__backtrack_entry_clear_a
    (Znth j (snap_rows current_snap_2) (@nil Z)) i ltac:(rewrite Hrow_len; lia) Hrow_cell) as [Hvar Hsat].
  rewrite <- Hmap in Hvar, Hsat.
  pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
    (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
    (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
    (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
    cur_states_2 cur_true_2 cur_unassigned_2 live cap j i false 1 (- Znth j cur_unassigned_2 0 - 1)
    Hclear Hmix ltac:(lia) Hassign Hvar Hsat
    ltac:(right; left; repeat split; lia)) as Hmix_new.
  backtrack_advance_epilogue current_ranks_2 after_ranks_2 after_snap_2 current_snap_2 row_ptr j row_table live.
Qed.

Lemma proof_of_backtrack_entail_wit_4_5 : backtrack_entail_wit_4_5.
Proof.
  unfold backtrack_entail_wit_4_5. right. intros. LLM_pre_process ltac:(int_auto).
  bind_fact (Znth i (snap_values current_snap_2) 0 = 1) as Hvalue_cell.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hrow_cell.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  assert (Hassign :
      assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some true).
  { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
      n current_snap_2 i true ltac:(get_values_len current_snap_2) ltac:(lia) Hvalue_cell). }
  assert (Hmap :
      Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (@nil literal)
      = dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
  { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_map; reflexivity. }
  pose proof (dense_decode_pos_counts__backtrack_entry_clear_a
    (Znth j (snap_rows current_snap_2) (@nil Z)) i ltac:(rewrite Hrow_len; lia) Hrow_cell) as [Hvar Hsat].
  rewrite <- Hmap in Hvar, Hsat.
  pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
    (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
    (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
    (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
    cur_states_2 cur_true_2 cur_unassigned_2 live cap j i true 1 2
    Hclear Hmix ltac:(lia) Hassign Hvar Hsat
    ltac:(right; right; left; repeat split; lia)) as Hmix_new.
  backtrack_advance_epilogue current_ranks_2 after_ranks_2 after_snap_2 current_snap_2 row_ptr j row_table live.
Qed.

Lemma proof_of_backtrack_entail_wit_4_6 : backtrack_entail_wit_4_6.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (snap_values current_snap_2) 0 = 0) as Hvalue_cell.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = (-1)) as Hrow_cell.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - assert (Hassign :
        assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some false).
    { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
        n current_snap_2 i false ltac:(get_values_len current_snap_2) ltac:(lia) Hvalue_cell). }
    assert (Hclause :
        Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (nil : clause)
        = dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_map; reflexivity. }
    pose proof (literal_counts_dense_decode_true__backtrack_clear_b
      (Znth j (snap_rows current_snap_2) (nil : list Z)) i false
      ltac:(rewrite Hrow_len; lia) (or_intror (conj Hrow_cell eq_refl))) as [Hvar_d Htrue_d].
    rewrite <- Hclause in Hvar_d, Htrue_d.
    exact (backtrack_clear_step_delta__backtrack_entry_clear_a
      (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
      (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
      cur_states_2 cur_true_2 cur_unassigned_2 live cap j i false 1 2
      Hclear Hmix ltac:(lia) Hassign Hvar_d Htrue_d
      ltac:(right; right; left; repeat split; lia)).
Qed.

Lemma proof_of_backtrack_entail_wit_4_7 : backtrack_entail_wit_4_7.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (snap_values current_snap_2) 0 <> 0) as Hvalue_nonzero.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = (-1)) as Hrow_cell.
  bind_fact (Znth j cur_states_2 0 = 0) as Hstate_zero.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_cur.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_cur.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - pose proof Hlen_cur as Hlengths.
    destruct Hlengths as
      [Hvalues [Hreasons [Hlevels [Hrows_current Hlengths_tail]]]].
    pose proof Hcells_cur as Hcellswf.
    destruct Hcellswf as [Hcellswf Hcellswf_rows].
    assert (Hvalue_cell : Znth i (snap_values current_snap_2) (-1) = 1).
    { assert (Hne_v : Znth i (snap_values current_snap_2) (-1) <> 0).
      { rewrite (Znth_indep (snap_values current_snap_2) i (-1) 0) by lia.
        exact Hvalue_nonzero. }
      pose proof (proj1 (Hcellswf i ltac:(unfold var_in_range; lia))) as Hdom.
      lia. }
    assert (Hassign :
      assignment
        (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
        i = Some true).
    { change (snapshot_assignment n current_snap_2 i = Some true).
      unfold snapshot_assignment.
      assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
      { apply andb_true_iff; split;
          [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      rewrite Hguard.
      unfold decode_value_cell.
      rewrite Hvalue_cell.
      reflexivity. }
    assert (Hclause :
      Znth j
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks conflict_dl))
        (nil : clause) =
      dense_decode
        (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b.
      rewrite <- Hrows_map.
      reflexivity. }
    pose proof
      (literal_counts_dense_decode_false__backtrack_clear_b
        (Znth j (snap_rows current_snap_2) (nil : list Z))
        i true ltac:(rewrite Hrow_len; lia)
        (or_intror (conj Hrow_cell eq_refl))) as [Hvar_dense Htrue_dense].
    eapply backtrack_summary_clear_step_false_unchanged__backtrack_clear_b.
    + exact Hclear.
    + exact Hmix.
    + lia.
    + exact Hassign.
    + rewrite Hclause; exact Hvar_dense.
    + rewrite Hclause; exact Htrue_dense.
    + exact Hstate_zero.
Qed.
Lemma proof_of_backtrack_entail_wit_4_8 : backtrack_entail_wit_4_8.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  backtrack_row_domain_absurd n j current_snap_2 i.
Qed.

Lemma proof_of_backtrack_entail_wit_4_9 : backtrack_entail_wit_4_9.
Proof.
  aggressive_pre_process.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlengths.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcellswf.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hcell_pos.
  bind_fact (Znth j cur_states_2 0 = 0) as Hstate_zero.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_eq.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - destruct Hlengths as
      [Hvalues [Hreasons [Hlevels [Hrows_current Hlengths_tail]]]].
    destruct Hcellswf as [Hcellswf Hcellswf_rows].
    assert (Hvalue_cell : Znth i (snap_values current_snap_2) (-1) = 0).
    { assert (Hne_v : Znth i (snap_values current_snap_2) (-1) <> 1).
      { rewrite (Znth_indep (snap_values current_snap_2) i (-1) 0) by lia.
        assumption. }
      pose proof (proj1 (Hcellswf i ltac:(unfold var_in_range; lia))) as Hdom.
      lia. }
    assert (Hassign :
      assignment
        (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
        i = Some false).
    { change (snapshot_assignment n current_snap_2 i = Some false).
      unfold snapshot_assignment.
      assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
      { apply andb_true_iff; split;
          [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      rewrite Hguard.
      unfold decode_value_cell.
      rewrite Hvalue_cell.
      reflexivity. }
    assert (Hclause :
      Znth j
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks conflict_dl))
        (nil : clause) =
      dense_decode
        (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b.
      rewrite <- Hrows_eq.
      reflexivity. }
    pose proof
      (literal_counts_dense_decode_false__backtrack_clear_b
        (Znth j (snap_rows current_snap_2) (nil : list Z))
        i false ltac:(rewrite Hrow_len; lia)
        (or_introl (conj Hcell_pos eq_refl))) as [Hvar_dense Htrue_dense].
    eapply backtrack_summary_clear_step_false_unchanged__backtrack_clear_b.
    + exact Hclear.
    + exact Hmix.
    + lia.
    + exact Hassign.
    + rewrite Hclause; exact Hvar_dense.
    + rewrite Hclause; exact Htrue_dense.
    + exact Hstate_zero.
Qed.
Lemma proof_of_backtrack_entail_wit_4_10 : backtrack_entail_wit_4_10.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (snap_values current_snap_2) 0 = 0) as Hval_false.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hcell_pos.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_eq.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - assert (Hassign :
        assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some false).
    { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
        n current_snap_2 i false ltac:(get_values_len current_snap_2) ltac:(lia) Hval_false). }
    assert (Hclause :
        Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (nil : clause)
        = dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_eq; reflexivity. }
    pose proof (literal_counts_dense_decode_false__backtrack_clear_b
      (Znth j (snap_rows current_snap_2) (nil : list Z)) i false
      ltac:(rewrite Hrow_len; lia) (or_introl (conj Hcell_pos eq_refl))) as [Hvar_d Htrue_d].
    rewrite <- Hclause in Hvar_d, Htrue_d.
    pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
      (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
      (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
      cur_states_2 cur_true_2 cur_unassigned_2 live cap j i false 0 2
      Hclear Hmix ltac:(lia) Hassign Hvar_d Htrue_d
      ltac:(right; right; right; right; left; repeat split; lia)) as Hmix_new.
    replace (Znth j cur_true_2 0 - 0) with (Znth j cur_true_2 0) in Hmix_new by lia.
    rewrite replace_Znth_Znth in Hmix_new.
    exact Hmix_new.
Qed.

Lemma proof_of_backtrack_entail_wit_4_11 : backtrack_entail_wit_4_11.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (snap_values current_snap_2) 0 = 1) as Hval_true.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = (-1)) as Hcell_neg.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_eq.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - assert (Hassign :
        assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some true).
    { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
        n current_snap_2 i true ltac:(get_values_len current_snap_2) ltac:(lia) Hval_true). }
    assert (Hclause :
        Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (nil : clause)
        = dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_eq; reflexivity. }
    pose proof (literal_counts_dense_decode_false__backtrack_clear_b
      (Znth j (snap_rows current_snap_2) (nil : list Z)) i true
      ltac:(rewrite Hrow_len; lia) (or_intror (conj Hcell_neg eq_refl))) as [Hvar_d Htrue_d].
    rewrite <- Hclause in Hvar_d, Htrue_d.
    pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
      (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
      (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
      cur_states_2 cur_true_2 cur_unassigned_2 live cap j i true 0 2
      Hclear Hmix ltac:(lia) Hassign Hvar_d Htrue_d
      ltac:(right; right; right; right; left; repeat split; lia)) as Hmix_new.
    replace (Znth j cur_true_2 0 - 0) with (Znth j cur_true_2 0) in Hmix_new by lia.
    rewrite replace_Znth_Znth in Hmix_new.
    exact Hmix_new.
Qed.

Lemma proof_of_backtrack_entail_wit_4_12 : backtrack_entail_wit_4_12.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  exfalso.
  backtrack_state_zero_absurd false snapshot_nonzero_assignment_false__backtrack_finish_decide_bounds or_intror Hmix n current_snap_2 current_ranks_2 back_dl_pre i live j snap ranks conflict_dl cur_states_2 cur_true_2 cur_unassigned_2 Hold_summary.
Qed.

Lemma proof_of_backtrack_entail_wit_4_13 : backtrack_entail_wit_4_13.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  backtrack_row_domain_absurd n j current_snap_2 i.
Qed.

Lemma proof_of_backtrack_entail_wit_4_14 : backtrack_entail_wit_4_14.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  exfalso.
  backtrack_state_zero_absurd true snapshot_nonzero_assignment_true__backtrack_finish_decide_bounds or_introl Hmix n current_snap_2 current_ranks_2 back_dl_pre i live j snap ranks conflict_dl cur_states_2 cur_true_2 cur_unassigned_2 Hold_summary.
Qed.

Lemma proof_of_backtrack_entail_wit_4_15 : backtrack_entail_wit_4_15.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (snap_values current_snap_2) 0 = 0) as Hval_false.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hcell_pos.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_eq.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - assert (Hassign :
        assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some false).
    { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
        n current_snap_2 i false ltac:(get_values_len current_snap_2) ltac:(lia) Hval_false). }
    assert (Hclause :
        Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (nil : clause)
        = dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_eq; reflexivity. }
    pose proof (literal_counts_dense_decode_false__backtrack_clear_b
      (Znth j (snap_rows current_snap_2) (nil : list Z)) i false
      ltac:(rewrite Hrow_len; lia) (or_introl (conj Hcell_pos eq_refl))) as [Hvar_d Htrue_d].
    rewrite <- Hclause in Hvar_d, Htrue_d.
    pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
      (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
      (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
      cur_states_2 cur_true_2 cur_unassigned_2 live cap j i false 0 (-2)
      Hclear Hmix ltac:(lia) Hassign Hvar_d Htrue_d
      ltac:(right; right; right; right; right; repeat split; lia)) as Hmix_new.
    replace (Znth j cur_true_2 0 - 0) with (Znth j cur_true_2 0) in Hmix_new by lia.
    rewrite replace_Znth_Znth in Hmix_new.
    exact Hmix_new.
Qed.

Lemma proof_of_backtrack_entail_wit_4_16 : backtrack_entail_wit_4_16.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (snap_values current_snap_2) 0 = 1) as Hval_true.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = (-1)) as Hcell_neg.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_eq.
  bind_fact (Zlength (Znth j (snap_rows current_snap_2) (@nil Z)) = n) as Hrow_len.
  unfold variable_arrays_rep.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  unfold backtrack_inner.
  backtrack_destruct_inner Hinner_copy.
  entailer!.
  - backtrack_row_merge row_table j live row_ptr current_snap_2.
  - assert (Hassign :
        assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre) i = Some true).
    { exact (snapshot_value_cell_assignment__backtrack_entry_clear_a
        n current_snap_2 i true ltac:(get_values_len current_snap_2) ltac:(lia) Hval_true). }
    assert (Hclause :
        Znth j (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl)) (nil : clause)
        = dense_decode (Znth j (snap_rows current_snap_2) (nil : list Z))).
    { rewrite installed_clause_Znth_dense_decode__backtrack_clear_b; rewrite <- Hrows_eq; reflexivity. }
    pose proof (literal_counts_dense_decode_false__backtrack_clear_b
      (Znth j (snap_rows current_snap_2) (nil : list Z)) i true
      ltac:(rewrite Hrow_len; lia) (or_intror (conj Hcell_neg eq_refl))) as [Hvar_d Htrue_d].
    rewrite <- Hclause in Hvar_d, Htrue_d.
    pose proof (backtrack_clear_step_delta__backtrack_entry_clear_a
      (cdcl_view_of_snapshot n current_snap_2 current_ranks_2 back_dl_pre)
      (cdcl_view_of_snapshot n after_snap_2 after_ranks_2 back_dl_pre)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
      cur_states_2 cur_true_2 cur_unassigned_2 live cap j i true 0 (-2)
      Hclear Hmix ltac:(lia) Hassign Hvar_d Htrue_d
      ltac:(right; right; right; right; right; repeat split; lia)) as Hmix_new.
    replace (Znth j cur_true_2 0 - 0) with (Znth j cur_true_2 0) in Hmix_new by lia.
    rewrite replace_Znth_Znth in Hmix_new.
    exact Hmix_new.
Qed.

Lemma proof_of_backtrack_entail_wit_4_17 : backtrack_entail_wit_4_17.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  backtrack_destruct_inner Hinner_copy.
  exfalso.
  backtrack_state_zero_absurd false snapshot_nonzero_assignment_false__backtrack_finish_decide_bounds or_intror Hmix n current_snap_2 current_ranks_2 back_dl_pre i live j snap ranks conflict_dl cur_states_2 cur_true_2 cur_unassigned_2 Hold_summary.
Qed.

Lemma proof_of_backtrack_entail_wit_4_18 : backtrack_entail_wit_4_18.
Proof.
  unfold backtrack_entail_wit_4_18.
  unfold variable_arrays_rep.
  left; intros.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlengths.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcellswf.
  exfalso.
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as (_ & _ & _ & Hrowslen & _).
  unfold snapshot_cells_wf in Hcellswf.
  destruct Hcellswf as [_ Hrows].
  apply Forall_forall with
    (x := Znth j (snap_rows current_snap_2) (@nil Z)) in Hrows.
  2: { unfold Znth; apply nth_In; rewrite Zlength_correct in Hrowslen; lia. }
  unfold row_wf in Hrows.
  destruct Hrows as [_ Hcells].
  assert (Hirow : 0 <= i <
    Zlength (Znth j (snap_rows current_snap_2) (@nil Z))) by lia.
  apply Forall_forall with
    (x := Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0) in Hcells.
  2: {
    change (In (nth (Z.to_nat i)
      (Znth j (snap_rows current_snap_2) (@nil Z)) 0)
      (Znth j (snap_rows current_snap_2) (@nil Z))).
    apply nth_In.
    rewrite Zlength_correct in Hirow; lia.
  }
  destruct Hcells as [Hminus | [Hzero | Hone]]; contradiction.
Qed.

Lemma proof_of_backtrack_entail_wit_4_19 : backtrack_entail_wit_4_19.
Proof.
  unfold backtrack_entail_wit_4_19.
  unfold variable_arrays_rep.
  backtrack_old_clause_state j.
  bind_fact (Znth j cur_states_2 0 = 2) as Hstate_two.
  bind_fact (Znth i (snap_values current_snap_2) 0 <> 0) as Hvalue_nz.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 1) as Hcell_pos.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_current.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_current.
  bind_fact (Znth i (snap_values current_snap_2) (-1) <> (-1)) as Hvalue_nz_default.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  change (Znth j cur_states_2 0 =
    expected_clause_state (snapshot_assignment n current_snap_2)
      (Znth j (List.map dense_decode (snap_rows snap)) (@nil literal)))
    in Hstate.
  rewrite Znth_map_dense_decode__backtrack_finish_decide_bounds in Hstate.
  rewrite Hstate_two in Hstate; symmetry in Hstate.
  pose proof
    (expected_clause_state_two_true_zero__backtrack_finish_decide_bounds
      _ _ Hstate) as Hzero.
  pose proof Hlen_current as Hlen_copy.
  pose proof Hcells_current as Hcells_copy.
  unfold snapshot_lengths in Hlen_copy.
  destruct Hlen_copy as (_ & _ & _ & Hrowslen & _).
  unfold snapshot_cells_wf in Hcells_copy.
  destruct Hcells_copy as [_ Hrows].
  apply Forall_forall with
    (x := Znth j (snap_rows current_snap_2) (@nil Z)) in Hrows.
  2: { unfold Znth; apply nth_In; rewrite Zlength_correct in Hrowslen; lia. }
  assert (Hin : In (Pos i)
    (dense_decode (Znth j (snap_rows current_snap_2) (@nil Z)))).
  { apply (proj1 (dense_decode_pos n _ i Hrows
      ltac:(unfold var_in_range; lia))). exact Hcell_pos. }
  pose proof
    (snapshot_nonzero_assignment_true__backtrack_finish_decide_bounds
      n live current_snap_2 i Hlen_current Hcells_current
      ltac:(lia) Hvalue_nz Hvalue_nz_default) as Hassign.
  assert (Heval : eval_partial_literal (snapshot_assignment n current_snap_2)
      (Pos i) = Some true).
  { unfold eval_partial_literal; cbn [literal_var]; rewrite Hassign; reflexivity. }
  rewrite <- Hrows_map in Hstate, Hzero.
  pose proof (clause_true_count_positive__backtrack_finish_decide_bounds
    _ _ _ Hin Heval) as Hpositive.
  lia.
Qed.
Lemma proof_of_backtrack_entail_wit_4_20 : backtrack_entail_wit_4_20.
Proof.
  unfold backtrack_entail_wit_4_20.
  unfold variable_arrays_rep.
  right; intros.
  match goal with
  | H : backtrack_inner _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hinner
  end.
  bind_fact (Znth j cur_states_2 0 < 0) as Hstate_neg.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 <> 0) as Hcell_nz.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_current.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_current.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  unfold backtrack_inner in *.
  entailer!.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  backtrack_finish_spatial row_table live j row_ptr current_snap_2.
  destruct Hinner as [Htarget [Hirange [Hprefix [Hclear Hmixed]]]].
  rewrite <- (replace_Znth_Znth j cur_true_2 0).
  eapply
    mixed_clause_summaries_advance_replace__backtrack_finish_decide_bounds.
  - exact Hmixed.
  - lia.
  - backtrack_finish_old_summary j Hmixed.
    rewrite !Znth_replace_Znth_Same by lia.
    assert (Hclause :
      Znth j
        (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
        (@nil literal) =
      dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
    { change (Znth j (List.map dense_decode (snap_rows snap)) (@nil literal) =
        dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
      rewrite Znth_map_dense_decode__backtrack_finish_decide_bounds.
      rewrite Hrows_map; reflexivity. }
    rewrite Hclause in Hold |- *.
    pose proof Hlen_current as Hlengths.
    unfold snapshot_lengths in Hlengths.
    destruct Hlengths as (_ & _ & _ & Hrows_length & _).
    pose proof Hcells_current as Hcells.
    unfold snapshot_cells_wf in Hcells.
    destruct Hcells as [_ Hrows].
    apply Forall_forall with
      (x := Znth j (snap_rows current_snap_2) (@nil Z)) in Hrows.
    2: { unfold Znth; apply nth_In.
         rewrite Zlength_correct in Hrows_length; lia. }
    pose proof Hclear as Hclear_copy.
    destruct Hclear_copy as [[b [d [Hassign Hlevel]]] _].
    cbn [cdcl_view_of_snapshot] in Hassign.
    pose proof
      (clears_one_assignment_eq_clear_partial__backtrack_entry_clear_a
        _ _ _ Hclear) as Hclear_assignment.
    cbn [cdcl_view_of_snapshot] in Hclear_assignment.
    eapply
      clause_summary_clear_negative_dense_nonzero__backtrack_finish_decide_bounds
      with (b := b) (x := i).
    + exact Hrows.
    + unfold var_in_range; lia.
    + exact Hcell_nz.
    + exact Hassign.
    + exact Hclear_assignment.
    + exact Hold.
    + exact Hstate_neg.
Qed.
Lemma proof_of_backtrack_entail_wit_4_21 : backtrack_entail_wit_4_21.
Proof.
  unfold backtrack_entail_wit_4_21.
  unfold variable_arrays_rep.
  backtrack_old_clause_state j.
  pose proof (expected_clause_state_domain__backtrack_finish_decide_bounds
    (assignment (cdcl_view_of_snapshot n current_snap_2 current_ranks_2
      back_dl_pre))
    (Znth j (installed_clauses
      (cdcl_view_of_snapshot n snap ranks conflict_dl)) (@nil literal))) as Hdomain.
  destruct Hdomain as [H0 | [H1 | [H2 | Hneg]]]; lia.
Qed.
Lemma proof_of_backtrack_entail_wit_4_22 : backtrack_entail_wit_4_22.
Proof.
  unfold backtrack_entail_wit_4_22.
  unfold variable_arrays_rep.
  right; intros.
  match goal with
  | H : backtrack_inner _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hinner
  end.
  bind_fact (Znth i (Znth j (snap_rows current_snap_2) (@nil Z)) 0 = 0) as Hcell_zero.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_current.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_current.
  bind_fact (snap_rows current_snap_2 = snap_rows snap) as Hrows_map.
  unfold backtrack_inner in *.
  entailer!.
  Exists current_ranks_2 after_ranks_2 after_snap_2 current_snap_2.
  backtrack_finish_spatial row_table live j row_ptr current_snap_2.
  destruct Hinner as [Htarget [Hirange [Hprefix [Hclear Hmixed]]]].
  eapply mixed_clause_summaries_advance_same__backtrack_finish_decide_bounds.
  - exact Hmixed.
  - lia.
  - backtrack_finish_old_summary j Hmixed.
    assert (Hclause :
      Znth j
        (installed_clauses (cdcl_view_of_snapshot n snap ranks conflict_dl))
        (@nil literal) =
      dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
    { change (Znth j (List.map dense_decode (snap_rows snap)) (@nil literal) =
        dense_decode (Znth j (snap_rows current_snap_2) (@nil Z))).
      rewrite Znth_map_dense_decode__backtrack_finish_decide_bounds.
      rewrite Hrows_map; reflexivity. }
    rewrite Hclause in Hold |- *.
    pose proof Hlen_current as Hlengths.
    unfold snapshot_lengths in Hlengths.
    destruct Hlengths as (_ & _ & _ & Hrows_length & _).
    pose proof Hcells_current as Hcells.
    unfold snapshot_cells_wf in Hcells.
    destruct Hcells as [_ Hrows].
    apply Forall_forall with
      (x := Znth j (snap_rows current_snap_2) (@nil Z)) in Hrows.
    2: { unfold Znth; apply nth_In.
         rewrite Zlength_correct in Hrows_length; lia. }
    pose proof Hclear as Hclear_copy.
    destruct Hclear_copy as [[b [d [Hassign Hlevel]]] _].
    pose proof
      (clears_one_assignment_eq_clear_partial__backtrack_entry_clear_a
        _ _ _ Hclear) as Hclear_assignment.
    eapply clause_summary_clear_dense_zero__backtrack_finish_decide_bounds
      with (b := b) (x := i).
    + exact Hrows.
    + unfold var_in_range; lia.
    + exact Hcell_zero.
    + exact Hassign.
    + exact Hclear_assignment.
    + exact Hold.
Qed.
Lemma proof_of_backtrack_entail_wit_5 : backtrack_entail_wit_5.
Proof.
  unfold backtrack_entail_wit_5.
  unfold variable_arrays_rep.
  right; intros.
  match goal with
  | H : backtrack_inner _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hinner
  end.
  assert (j = live) by lia.
  subst j.
  Exists current_ranks_2 after_ranks_2 after_snap_2.
  split_pure_spatial.
  - cancel emp.
  - split_pures;
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    dump_pre_spatial.
    unfold backtrack_inner in Hinner.
    destruct Hinner as
      (Htarget & Hvarrange & Hprefix & Hclear & Hsummary).
    unfold clearing_variable.
    split; [exact Htarget|].
    split; [exact Hvarrange|].
    split; [exact Hprefix|].
    split; [exact Hclear|].
    destruct Hsummary as
      (Hrows & Hstates & Htrue & Hunassigned & Hcap &
       Hprocessed & Hsummary).
    unfold mixed_clause_summaries.
    split; [exact Hrows|].
    split; [exact Hstates|].
    split; [exact Htrue|].
    split; [exact Hunassigned|].
    split; [exact Hcap|].
    split; [lia|].
    intros idx Hidxrange.
    specialize (Hsummary idx Hidxrange).
    destruct Hsummary as [Hnew Hold].
    split.
    + intros _. exact (Hnew (or_introl (proj2 Hidxrange))).
    + intros [Hge _]. lia.
Qed.
Lemma proof_of_backtrack_entail_wit_6_1 : backtrack_entail_wit_6_1.
Proof.
  unfold backtrack_entail_wit_6_1.
  right; intros.
  match goal with
  | H : clearing_variable _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hclearing
  end.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_current.
  bind_fact (snapshot_lengths n live after_snap) as Hlen_after.
  bind_fact (snapshot_cells_wf n live after_snap) as Hcells_after.
  bind_fact (Znth i (snap_values current_snap_2) (-1) <> (-1)) as Hvalue_nz.
  bind_fact (snap_rows after_snap = snap_rows current_snap_2) as Hrows_after.
  unfold clearing_variable, backtrack_outer in *.
  change (sizeof (INT)) with 4.
  unfold solver_arrays_rep, variable_arrays_rep.
  entailer!.
  Exists after_ranks
    ({| snap_values := snap_values after_snap;
        snap_reasons := snap_reasons after_snap;
        snap_levels := snap_levels after_snap;
        snap_rows := snap_rows after_snap;
        snap_states := cur_states;
        snap_true_counts := cur_true;
        snap_unassigned := cur_unassigned |} : dense_snapshot).
  cbn.
  sep_apply (IntArray.full_to_seg states live cur_states).
  sep_apply (IntArray.full_to_seg true_counts live cur_true).
  sep_apply (IntArray.full_to_seg unassigned live cur_unassigned).
  rewrite Hrows_after.
  unfold IntArray.seg.
  change (sizeof (INT)) with 4.
  entailer!.
  - rewrite <- Hrows_after.
    change (prefix_restriction
      (cdcl_view_of_snapshot n snap ranks conflict_dl)
      (cdcl_view_of_snapshot n after_snap after_ranks back_dl_pre)
      n back_dl_pre (i + 1)).
    destruct Hclearing as (_ & _ & Hprefix & Hclear & _).
    pose proof Hprefix as Hprefix_copy.
    destruct Hprefix_copy as [_ [_ Hcells]].
    specialize (Hcells i ltac:(unfold var_in_range; lia)).
    destruct Hcells as [_ Hsame].
    specialize (Hsame ltac:(lia)).
    destruct Hsame as [_ [Hlevel _]].
    pose proof
      (snapshot_level_assigned__backtrack_finish_decide_bounds
        n live current_snap_2 i Hcells_current ltac:(lia) Hvalue_nz)
      as Hcurrent_level.
    change (snapshot_level n current_snap_2 i = snapshot_level n snap i)
      in Hlevel.
    eapply prefix_restriction_advance_clear__backtrack_finish_decide_bounds
      with (current := cdcl_view_of_snapshot n current_snap_2
        current_ranks_2 back_dl_pre)
           (d := Znth i (snap_levels current_snap_2) (-1)).
    + exact Hprefix.
    + exact Hclear.
    + lia.
    + change (snapshot_level n snap i =
        Some (Znth i (snap_levels current_snap_2) (-1))).
      rewrite <- Hlevel. exact Hcurrent_level.
    + lia.
  - rewrite <- Hrows_after.
    unfold snapshot_cells_wf in *; cbn in *.
    exact Hcells_after.
  - rewrite <- Hrows_after.
    unfold snapshot_lengths; cbn.
    pose proof Hlen_after as Hafter_lengths.
    unfold snapshot_lengths in Hafter_lengths.
    destruct Hafter_lengths as
      [Hvalues [Hreasons [Hlevels [Hrows _]]]].
    destruct Hclearing as (_ & _ & _ & _ & Hmixed).
    unfold mixed_clause_summaries in Hmixed.
    destruct Hmixed as [_ [Hstates [Htrue [Hunassigned _]]]].
    repeat split; assumption.
Qed.
Lemma proof_of_backtrack_entail_wit_6_2 : backtrack_entail_wit_6_2.
Proof.
  unfold backtrack_entail_wit_6_2.
  right; intros.
  match goal with
  | H : backtrack_outer _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Houter
  end.
  bind_fact (Znth i (snap_values current_snap_2) 0 = (-1)) as Hvalue_unassigned.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_current.
  unfold backtrack_outer in *.
  unfold solver_arrays_rep, variable_arrays_rep.
  entailer!.
  Exists current_ranks_2.
  entailer!.
  destruct Houter as (_ & Hprefix & _).
  eapply prefix_restriction_advance_unchanged__backtrack_finish_decide_bounds.
  - exact Hprefix.
  - lia.
  - intros d Hold.
    pose proof Hprefix as Hprefix_copy.
    destruct Hprefix_copy as [_ [_ Hcells]].
    specialize (Hcells i ltac:(unfold var_in_range; lia)).
    destruct Hcells as [_ Hsame].
    specialize (Hsame ltac:(lia)).
    destruct Hsame as [_ [Hlevel _]].
    pose proof Hlen_current as Hlengths.
    unfold snapshot_lengths in Hlengths.
    destruct Hlengths as [Hvalues_len _].
    assert (Hvalue_minus :
      Znth i (snap_values current_snap_2) (-1) = -1).
    { rewrite (Znth_indep (snap_values current_snap_2) i (-1) 0) by lia.
      exact Hvalue_unassigned. }
    pose proof
      (snapshot_level_unassigned__backtrack_finish_decide_bounds
        n current_snap_2 i ltac:(lia) Hvalue_minus) as Hnone.
    change (snapshot_level n current_snap_2 i = snapshot_level n snap i)
      in Hlevel.
    change (snapshot_level n snap i = Some d) in Hold.
    congruence.
Qed.
Lemma proof_of_backtrack_entail_wit_6_3 : backtrack_entail_wit_6_3.
Proof.
  unfold backtrack_entail_wit_6_3.
  right; intros.
  match goal with
  | H : backtrack_outer _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Houter
  end.
  bind_fact (Znth i (snap_levels current_snap_2) 0 <= back_dl_pre) as Hlevel_le.
  bind_fact (Znth i (snap_values current_snap_2) 0 <> (-1)) as Hvalue_nz.
  bind_fact (snapshot_lengths n live current_snap_2) as Hlen_current.
  bind_fact (snapshot_cells_wf n live current_snap_2) as Hcells_current.
  unfold backtrack_outer in *.
  unfold solver_arrays_rep, variable_arrays_rep.
  entailer!.
  Exists current_ranks_2.
  entailer!.
  destruct Houter as (_ & Hprefix & _).
  eapply prefix_restriction_advance_unchanged__backtrack_finish_decide_bounds.
  - exact Hprefix.
  - lia.
  - intros d Hold.
    pose proof Hprefix as Hprefix_copy.
    destruct Hprefix_copy as [_ [_ Hcells]].
    specialize (Hcells i ltac:(unfold var_in_range; lia)).
    destruct Hcells as [_ Hsame].
    specialize (Hsame ltac:(lia)).
    destruct Hsame as [_ [Hlevel _]].
    pose proof Hlen_current as Hlengths.
    unfold snapshot_lengths in Hlengths.
    destruct Hlengths as [Hvalues_len [_ [Hlevels_len _]]].
    assert (Hvalue_assigned :
      Znth i (snap_values current_snap_2) (-1) <> -1).
    { rewrite (Znth_indep (snap_values current_snap_2) i (-1) 0) by lia.
      exact Hvalue_nz. }
    assert (Hlevel_bound :
      Znth i (snap_levels current_snap_2) (-1) <= back_dl_pre).
    { rewrite (Znth_indep (snap_levels current_snap_2) i (-1) 0) by lia.
      exact Hlevel_le. }
    pose proof
      (snapshot_level_assigned__backtrack_finish_decide_bounds
        n live current_snap_2 i Hcells_current ltac:(lia) Hvalue_assigned)
      as Hcurrent_level.
    change (snapshot_level n current_snap_2 i = snapshot_level n snap i)
      in Hlevel.
    change (snapshot_level n snap i = Some d) in Hold.
    rewrite Hcurrent_level, Hold in Hlevel.
    inversion Hlevel; subst d; exact Hlevel_bound.
Qed.
(* ===== backtrack return wits (1 proofs) ===== *)
Lemma proof_of_backtrack_return_wit_1 : backtrack_return_wit_1.
Proof.
  unfold backtrack_return_wit_1.
  left; intros.
  match goal with
  | H : backtrack_outer _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Houter
  end.
  bind_fact (stable_search_facts n conflict_snap conflict_ranks conflict_dl)
    as Hstable_conflict.
  assert (i = n) by lia; subst i.
  unfold backtrack_outer, pending_backjump_rep, bcp_ready in *.
  unfold solver_arrays_rep, variable_arrays_rep.
  entailer!.
  destruct Houter as [Htarget [Hprefix Hmixed]].
  match goal with
  | |- context [ emp && (“ ?B ”) ] =>
      prop_apply (derivable1_andp_elim2 emp (“ B ”))
  end.
  Intros_p H0.
  Intros_p Hjunk.
  destruct H0 as
    [Hphysical [Hcurrent [Hassignment [Hlevel [Hreason [Hrank
      [Hclauses [Hbatch [Hprofile Hcert]]]]]]]]].
  pose (final_ranks :=
    fun x : Z =>
      match snapshot_level n snap x with
      | Some d => if Z.leb d back_dl_pre then ranks x else None
      | None => None
      end).
  assert (Hfinal_ranks : forall x,
    final_ranks x =
      match snapshot_level n snap x with
      | Some d => if Z.leb d back_dl_pre then ranks x else None
      | None => None
      end).
  { intro x; reflexivity. }
  pose proof
    (prefix_snapshot_restrict__backtrack_finish_decide_bounds n back_dl_pre snap ranks conflict_dl
      current_snap current_ranks final_ranks Hfinal_ranks Hprefix) as Hrestrict.
  pose proof
    (backjump_no_conflict__backtrack_finish_decide_bounds F
      (cdcl_view_of_snapshot n start_snap start_ranks conflict_dl)
      (cdcl_view_of_snapshot n conflict_snap conflict_ranks conflict_dl)
      (cdcl_view_of_snapshot n snap ranks conflict_dl)
      (cdcl_view_of_snapshot n current_snap final_ranks back_dl_pre)
      back_dl_pre last learned Hassignment Hlevel Hclauses Hbatch Hcert
      Hrestrict) as [Hnot_after Hno_conflict].
  assert (Hbackjump :
    backjump_clears
      (cdcl_view_of_snapshot n snap ranks conflict_dl)
      (cdcl_view_of_snapshot n current_snap final_ranks back_dl_pre)
      back_dl_pre).
  { split; [exact Hrestrict|].
    split; assumption. }
  assert (Hdense :
    dense_summaries_restored n live back_dl_pre snap current_snap).
  { eapply dense_summaries_from_complete__backtrack_finish_decide_bounds with (cap := cap); eauto. }
  assert (Hcoherent : coherent_snapshot F n live original_count current_snap).
  { eapply coherent_snapshot_from_complete__backtrack_finish_decide_bounds with (cap := cap)
      (old_snap := snap); eauto. }
  unfold stable_search_facts in Hstable_conflict.
  assert (Hstable :
    stable_search_facts n current_snap final_ranks back_dl_pre).
  { unfold stable_search_facts.
    eapply stable_after_backjump__backtrack_finish_decide_bounds with
      (F := F)
      (conflict :=
        cdcl_view_of_snapshot n conflict_snap conflict_ranks conflict_dl)
      (old := cdcl_view_of_snapshot n snap ranks conflict_dl)
      (target := back_dl_pre) (learned := learned); eauto. }
  (* The exit is the cut-free seam into [bcp]'s [Require]: the three pure facts
     stay visible and the memory is handed over as [solver_state] at
     [back_dl_pre].  Only the two struct pointers moved inside it, so the
     witness list drops from four to two and reopens the fold to meet the
     cell-level left side. *)
  Exists final_ranks current_snap.
  unfold solver_state, sat_header_rep, var_header_rep, clause_header_rep,
    unconstrained_Assignment, variable_arrays_rep, solver_arrays_rep.
  Exists v_data cl_data.
  entailer!.
Qed.
(* ===== decide entail wits (12 proofs) ===== *)
