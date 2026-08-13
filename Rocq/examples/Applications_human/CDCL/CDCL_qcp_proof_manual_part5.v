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

Lemma proof_of_decide_entail_wit_2 : decide_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (stable_search_facts n snap ranks logical_dl ) as Hstable.
  bind_fact ((Znth i (snap_values (snap)) 0) = (-1)) as Hval_unassigned.
  pose proof Hcoh as Hcoherent.
  unfold coherent_snapshot in Hcoherent.
  destruct Hcoherent as [_ [_ [Hlengths [_ [Hsummaries _]]]]].
  assert (Hi_none : snapshot_assignment n snap i = None).
  {
    unfold snapshot_assignment.
    assert (Hguard : andb ((0 <=? i)%Z) ((i <? n)%Z) = true).
    { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    rewrite Hguard.
    destruct Hlengths as [Hvalues _].
    rewrite (Znth_indep (snap_values snap) i (-1) 0) by
      (rewrite Hvalues; lia).
    rewrite Hval_unassigned. reflexivity.
  }
  pose proof (stable_unassigned_level_lt__decide_commit
    n snap ranks logical_dl i Hstable ltac:(split; lia) Hi_none) as Hdl_lt.
  assert (Hupdate :
    assignment_update_only
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n (snapshot_set_value snap i 1) ranks
        (logical_dl + 1)) i true /\
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment (cdcl_view_of_snapshot n (snapshot_set_value snap i 1)
        ranks (logical_dl + 1)))
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (snap_states snap) (snap_true_counts snap) (snap_unassigned snap)
      live cap 0 None).
  {
    apply conj.
    - apply (snapshot_assignment_set_true_update__decide_commit
        n live snap ranks logical_dl (logical_dl + 1) i).
      + exact Hlengths.
      + split; lia.
      + exact Hi_none.
    - apply mixed_clause_summaries_initial__decide_commit
        with (n := n).
      + exact Hlengths.
      + exact Hsummaries.
      + lia.
  }
  Exists ranks (snap_states snap) (snap_true_counts snap)
    (snap_unassigned snap) (snapshot_set_value snap i 1).
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep.
  entailer!.
  unfold decision_update.
  entailer!.
  unfold IntArray.full, IntArray.seg, store_array; simpl; entailer!.
  all: try (intros m Hemp; change True; exact I).
  all: entailer!.
Qed.

Lemma proof_of_decide_entail_wit_3 : decide_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  unfold installed_rows_capacity_rep.
  prop_apply (IntPtrArray2.full_Zlength row_table live (snap_rows snap)).
  Intros.
  sep_apply_l_atomic
    (IntPtrArray2.full_split_to_missing_i row_table j live (snap_rows snap)).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists final_ranks_2 row_ptr cur_states_2 cur_true_2 cur_unassigned_2
      final_snap_2.
    unfold solver_row_focus_state.
    Exists v_data cl_data.
    unfold sat_header_rep, var_header_rep, clause_header_rep,
      clause_summaries_explicit_rep, installed_row_focus_rep.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth j (snap_rows snap) nil))
      (Znth j (snap_rows snap) nil)) with
      (IntArray.full row_ptr
        (Zlength (Znth j (snap_rows snap) nil))
        (Znth j (snap_rows snap) nil)).
    entailer!.
    unfold coherent_snapshot, snapshot_cells_wf in Hcoh.
    destruct Hcoh as [_ [_ [_ [Hcells _]]]].
    destruct Hcells as [_ Hrows].
    apply Forall_forall with
      (x := Znth j (snap_rows snap) nil) in Hrows.
    2: {
      unfold Znth.
      apply nth_In.
      replace (List.length (snap_rows snap)) with
        (Z.to_nat (Zlength (snap_rows snap))).
      - apply Z2Nat.inj_lt; lia.
      - rewrite Zlength_correct, Nat2Z.id; reflexivity.
    }
    unfold row_wf in Hrows.
    tauto.
Qed.

Lemma proof_of_decide_entail_wit_4_1 : decide_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact ((Znth i (Znth (j) ((snap_rows (snap))) ((@nil Z))) 0) = 1)
    as Hcell_pos.
  bind_fact ((Znth j cur_states_2 0) = 0) as Hstate_zero.
  decide_rows_prelude row_table j live row_ptr snap.
  Exists final_ranks_2 cur_states_2
    (replace_Znth j (Znth j cur_true_2 0 + 1) cur_true_2)
    (replace_Znth j (Znth j cur_unassigned_2 0 - 1) cur_unassigned_2)
    final_snap_2.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  entailer!.
  unfold decision_update in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  pose proof (coherent_snapshot_row_wf__decide_commit
    F n live original_count snap j Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (decision_mixed_dense_positive_step__decide_commit
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (cdcl_view_of_snapshot n final_snap_2 final_ranks_2 (logical_dl + 1))
    (snap_rows snap) cur_states_2 cur_true_2 cur_unassigned_2
    live cap j i n Hassign Hmix ltac:(lia) Hrow_wf
    ltac:(split; lia) Hcell_pos) as Hadvance.
  assert (Hstates_same : replace_Znth j 0 cur_states_2 = cur_states_2).
  { rewrite <- Hstate_zero. apply replace_Znth_Znth. }
  rewrite Hstates_same in Hadvance.
  exact Hadvance.
Qed.

Lemma proof_of_decide_entail_wit_4_2 : decide_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact ((Znth i (Znth (j) ((snap_rows (snap))) ((@nil Z))) 0) = 1)
    as Hcell_pos.
  bind_fact ((Znth j cur_states_2 0) < 0) as Hstate_neg.
  decide_rows_prelude row_table j live row_ptr snap.
  Exists final_ranks_2
    (replace_Znth j 0 cur_states_2)
    (replace_Znth j 1 cur_true_2)
    (replace_Znth j (Znth j cur_unassigned_2 0 - 1) cur_unassigned_2)
    final_snap_2.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  entailer!.
  unfold decision_update in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  pose proof (coherent_snapshot_row_wf__decide_commit
    F n live original_count snap j Hcoh ltac:(lia)) as Hrow_wf.
  pose proof (decision_mixed_dense_positive_step__decide_commit
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (cdcl_view_of_snapshot n final_snap_2 final_ranks_2 (logical_dl + 1))
    (snap_rows snap) cur_states_2 cur_true_2 cur_unassigned_2
    live cap j i n Hassign Hmix ltac:(lia) Hrow_wf
    ltac:(split; lia) Hcell_pos) as Hadvance.
  pose proof (mixed_clause_summaries_old_at__decide_commit
    _ _ _ _ _ _ _ _ _ Hmix ltac:(lia)) as Hold.
  unfold summary_at in Hold.
  pose proof (clause_summary_negative_true_zero__decide_commit
    _ _ _ _ _ Hold Hstate_neg) as Htrue_zero.
  rewrite Htrue_zero in Hadvance.
  replace (0 + 1) with 1 in Hadvance by lia.
  exact Hadvance.
Qed.

Lemma proof_of_decide_entail_wit_4_3 : decide_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact ((Znth j (replace_Znth (j) (((Znth j cur_states_2 0) + 1 ))
    (cur_states_2)) 0) = (-1)) as Hnext_state.
  bind_fact ((Znth j cur_states_2 0) < 0) as Hstate_neg.
  decide_rows_prelude row_table j live row_ptr snap.
  Exists final_ranks_2
    (replace_Znth j 2
      (replace_Znth j (Znth j cur_states_2 0 + 1) cur_states_2))
    cur_true_2
    (replace_Znth j (Znth j cur_unassigned_2 0 - 1) cur_unassigned_2)
    final_snap_2.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  entailer!.
  unfold decision_update in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  pose proof (coherent_snapshot_row_wf__decide_commit
    F n live original_count snap j Hcoh ltac:(lia)) as Hrow_wf.
  assert (Hcell : Znth i (Znth j (snap_rows snap) nil) 0 = -1).
  { pose proof (row_wf_cell_domain n
      (Znth j (snap_rows snap) nil) i Hrow_wf ltac:(split; lia)) as Hcells.
    destruct Hcells as [Hneg | [Hzero | Hpos]]; lia. }
  pose proof (decision_mixed_dense_negative_step__decide_commit
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (cdcl_view_of_snapshot n final_snap_2 final_ranks_2 (logical_dl + 1))
    (snap_rows snap) cur_states_2 cur_true_2 cur_unassigned_2
    live cap j i n Hassign Hmix ltac:(lia) Hrow_wf
    ltac:(split; lia) Hcell Hstate_neg) as Hadvance.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as [_ [Hstates _]].
  assert (Hnext_minus_one : Znth j cur_states_2 0 + 1 = -1).
  { rewrite Znth_replace_Znth_Same in Hnext_state by lia. exact Hnext_state. }
  rewrite Hnext_minus_one in Hadvance.
  cbn in Hadvance.
  rewrite replace_Znth_replace_Znth_Same by lia.
  exact Hadvance.
Qed.

Lemma proof_of_decide_entail_wit_4_4 : decide_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact ((Znth j (replace_Znth (j) (((Znth j cur_states_2 0) + 1 ))
    (cur_states_2)) 0) <> (-1)) as Hnext_state.
  bind_fact ((Znth j cur_states_2 0) < 0) as Hstate_neg.
  decide_rows_prelude row_table j live row_ptr snap.
  Exists final_ranks_2
    (replace_Znth j (Znth j cur_states_2 0 + 1) cur_states_2)
    cur_true_2
    (replace_Znth j (Znth j cur_unassigned_2 0 - 1) cur_unassigned_2)
    final_snap_2.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  entailer!.
  unfold decision_update in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  pose proof (coherent_snapshot_row_wf__decide_commit
    F n live original_count snap j Hcoh ltac:(lia)) as Hrow_wf.
  assert (Hcell : Znth i (Znth j (snap_rows snap) nil) 0 = -1).
  { pose proof (row_wf_cell_domain n
      (Znth j (snap_rows snap) nil) i Hrow_wf ltac:(split; lia)) as Hcells.
    destruct Hcells as [Hneg | [Hzero | Hpos]]; lia. }
  pose proof (decision_mixed_dense_negative_step__decide_commit
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (cdcl_view_of_snapshot n final_snap_2 final_ranks_2 (logical_dl + 1))
    (snap_rows snap) cur_states_2 cur_true_2 cur_unassigned_2
    live cap j i n Hassign Hmix ltac:(lia) Hrow_wf
    ltac:(split; lia) Hcell Hstate_neg) as Hadvance.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as [_ [Hstates _]].
  assert (Hnext_not_minus_one : Znth j cur_states_2 0 + 1 <> -1).
  { intro Heq. apply Hnext_state.
    rewrite Znth_replace_Znth_Same by lia. exact Heq. }
  assert (Hbranch : Z.eqb (Znth j cur_states_2 0 + 1) (-1) = false).
  { apply Z.eqb_neq. exact Hnext_not_minus_one. }
  rewrite Hbranch in Hadvance.
  exact Hadvance.
Qed.

Lemma proof_of_decide_entail_wit_4_5 : decide_entail_wit_4_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact (decision_ready (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) ) as Hdec_ready.
  bind_fact ((Znth j cur_states_2 0) = 1) as Hstate_one.
  unfold decision_update, decision_ready,
    propagation_quiescent in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  destruct Hdec_ready as [Hno_conflict Hno_unit].
  pose proof (mixed_clause_summaries_old_at__decide_commit
    _ _ _ _ _ _ _ _ _ Hmix ltac:(lia)) as Hold.
  unfold summary_at in Hold.
  rewrite Hstate_one in Hold.
  pose proof (clause_summary_one_false__bcp_assignment_summary_d
    _ _ _ _ Hold) as Hfalse.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as [Hrows _].
  specialize (Hno_conflict
    (Znth j
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl)) nil)).
  assert (Hin : In
    (Znth j
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl)) nil)
    (installed_clauses
      (cdcl_view_of_snapshot n snap ranks logical_dl))).
  { apply Znth_In__decide_commit. lia. }
  specialize (Hno_conflict Hin).
  contradiction.
Qed.
Lemma proof_of_decide_entail_wit_4_6 : decide_entail_wit_4_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact (decision_ready (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) ) as Hdec_ready.
  bind_fact ((Znth j cur_states_2 0) = 2) as Hstate_two.
  unfold decision_update, decision_ready,
    propagation_quiescent in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  destruct Hdec_ready as [Hno_conflict Hno_unit].
  pose proof (mixed_clause_summaries_old_at__decide_commit
    _ _ _ _ _ _ _ _ _ Hmix ltac:(lia)) as Hold.
  unfold summary_at in Hold.
  rewrite Hstate_two in Hold.
  pose proof (clause_summary_state_two_unit__decide_commit
    _ _ _ _ Hold) as Hunit.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as [Hrows _].
  specialize (Hno_unit
    (Znth j
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl)) nil)).
  assert (Hin : In
    (Znth j
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl)) nil)
    (installed_clauses
      (cdcl_view_of_snapshot n snap ranks logical_dl))).
  { apply Znth_In__decide_commit. lia. }
  specialize (Hno_unit Hin).
  contradiction.
Qed.
Lemma proof_of_decide_entail_wit_4_7 : decide_entail_wit_4_7.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_decide_entail_wit_4_8 : decide_entail_wit_4_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  bind_fact ((Znth j cur_states_2 0) = 0) as Hstate_zero.
  decide_rows_prelude row_table j live row_ptr snap.
  Exists final_ranks_2 cur_states_2 cur_true_2
    (replace_Znth j (Znth j cur_unassigned_2 0 - 1) cur_unassigned_2)
    final_snap_2.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  entailer!.
  unfold decision_update in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  pose proof (coherent_snapshot_row_wf__decide_commit
    F n live original_count snap j Hcoh ltac:(lia)) as Hrow_wf.
  assert (Hcell : Znth i (Znth j (snap_rows snap) nil) 0 = -1).
  { pose proof (row_wf_cell_domain n
      (Znth j (snap_rows snap) nil) i Hrow_wf ltac:(split; lia)) as Hcells.
    destruct Hcells as [Hneg | [Hzero | Hpos]]; lia. }
  exact (decision_mixed_dense_negative_zero_step__decide_commit
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (cdcl_view_of_snapshot n final_snap_2 final_ranks_2 (logical_dl + 1))
    (snap_rows snap) cur_states_2 cur_true_2 cur_unassigned_2
    live cap j i n Hassign Hmix ltac:(lia) Hrow_wf
    ltac:(split; lia) Hcell Hstate_zero).
Qed.

Lemma proof_of_decide_entail_wit_4_9 : decide_entail_wit_4_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states_2
    cur_true_2 cur_unassigned_2 ) as Hdec_update.
  decide_rows_prelude row_table j live row_ptr snap.
  Exists final_ranks_2 cur_states_2 cur_true_2 cur_unassigned_2 final_snap_2.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  entailer!.
  unfold decision_update in *.
  entailer!.
  destruct Hdec_update as [Hassign Hmix].
  eapply decision_mixed_dense_absent_step__decide_commit;
    try eassumption; try lia.
  - eapply coherent_snapshot_row_wf__decide_commit; eauto; lia.
  - split; lia.
Qed.

Lemma proof_of_decide_entail_wit_1 : decide_entail_wit_1.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
Qed.

(* ===== decide return wits (2 proofs) ===== *)
Lemma proof_of_decide_return_wit_1 : decide_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (forall (x: Z) , (((0 <= x) /\ (x < i)) ->
    ((Znth (x) ((snap_values (snap))) (0)) <> (-1)))) as Hprefix_assigned.
  (* Folded on the RIGHT here, not on the left: the model-ready exit hands back
     [solver_state], whose two [EX] binders are the [forall]-bound cell values
     [v_data] and [cl_data] -- in the definition's order, v_data first. *)
  unfold solver_state, sat_header_rep, var_header_rep, clause_header_rep,
    unconstrained_Assignment, solver_arrays_rep, variable_arrays_rep.
  Exists v_data cl_data.
  unfold model_ready, decision_ready.
  entailer!.
  unfold total_assignment_on, cdcl_view_of_snapshot.
  cbn.
  intros x Hx.
  unfold snapshot_assignment.
  assert (Hguard : andb (Z.leb 0 x) (Z.ltb x n) = true).
  {
    apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt].
    all: unfold var_in_range in Hx; lia.
  }
  rewrite Hguard.
  destruct Hcoh as [_ [_ [Hlengths [Hcells _]]]].
  destruct Hlengths as [Hvalues_length _].
  assert (Hx_length : 0 <= x < Zlength (snap_values snap)) by
    (unfold var_in_range in Hx; lia).
  pose proof (Znth_indep (snap_values snap) x (-1) 0 Hx_length) as Hdefaults.
  assert (Hassigned0 : Znth x (snap_values snap) 0 <> -1).
  {
    apply Hprefix_assigned.
    unfold var_in_range in Hx.
    lia.
  }
  rewrite <- Hdefaults in Hassigned0.
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hcells _].
  specialize (Hcells x Hx).
  cbn in Hcells.
  destruct Hcells as [Hvalue _].
  destruct Hvalue as [Hminus | [Hzero | Hone]].
  + contradiction.
  + exists false. unfold decode_value_cell. rewrite Hzero. reflexivity.
  + exists true. unfold decode_value_cell. rewrite Hone. reflexivity.
Qed.
Lemma proof_of_decide_return_wit_2 : decide_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (decision_ready (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) ) as Hdec_ready.
  bind_fact (decision_update (cdcl_view_of_snapshot (n) (snap) (ranks)
    (logical_dl)) (cdcl_view_of_snapshot (n) (final_snap_2) (final_ranks_2)
    ((logical_dl + 1 ))) i j live cap (installed_clauses
    ((cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)))) cur_states
    cur_true cur_unassigned ) as Hdec_update.
  bind_fact ((snap_values (final_snap_2)) = (replace_Znth (i) (1)
    ((snap_values (snap))))) as Hvalues_eq.
  (* The invariant block is now the folded whole-table head, so its two ghost
     struct pointers arrive as ordinary binders named [v_data] / [cl_data]
     instead of the old [s_v_data] / [s_cl_data]. *)
  - pose proof
      (decision_update_ready_facts__decide_exit_solver_setup
        (cdcl_view_of_snapshot n snap ranks logical_dl)
        (cdcl_view_of_snapshot n final_snap_2 final_ranks_2
          (logical_dl + 1))
        i j live cap
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks logical_dl))
        cur_states cur_true cur_unassigned Hdec_ready Hdec_update) as H.
    destruct H as
      [Hno_conflict_old [Hno_unit_old [Hupdate_old Hmixed_old]]].
    assert (Hj : j = live) by lia.
    subst j.
    destruct
      (decision_commit_bcp_ready__decide_exit_solver_setup
        F n live original_count cap snap ranks logical_dl i
        final_snap_2 final_ranks_2 cur_states cur_true cur_unassigned)
      as [final_snap [final_ranks
        [Hvalues [Hlevels [Hreasons [Hrows
          [Hstates [Htrue [Hunassigned
            [Hcoherent [Hstable [Hno_conflict_final
              [Hupdate_final Hmixed_final]]]]]]]]]]]]].
    + lia.
    + lia.
    + assumption.
    + assumption.
    + exact Hno_conflict_old.
    + exact Hno_unit_old.
    + exact Hvalues_eq.
    + assumption.
    + exact Hupdate_old.
    + exact Hmixed_old.
    + Exists final_ranks final_snap.
      unfold solver_state, sat_header_rep, var_header_rep, clause_header_rep,
        unconstrained_Assignment, variable_arrays_rep, solver_arrays_rep.
      Exists v_data cl_data.
      rewrite Hvalues, Hvalues_eq, Hlevels, Hreasons, Hrows,
        Hstates, Htrue, Hunassigned.
      unfold bcp_ready.
      entailer!.
      (* The folded invariant spells the clause summaries `full p live`; the
         exit's [solver_state] spells the same assertion `seg p 0 live`. *)
      unfold IntArray.full, IntArray.seg, store_array.
      entailer!.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_1 : cdcl_solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (fresh_formula F n original_count
    (cdcl_view_of_snapshot (n) (snap) (ranks) (0))) as Hfresh.
  (* The loop invariant is folded into [solver_loop_state], whose snapshot,
     rank map and level are PARAMETERS, so all four of the goal's existentials
     -- [current_live] and the three ghosts -- are handed over here in one
     [Exists].  Reopening the wrapper then takes two more layers:
     [solver_loop_state] exposes [solver_state], which exposes the three header
     reps and the two array bundles, which have to come apart too because the
     left side still carries the thirteen raw header cells. *)
  Exists live snap ranks 0.
  unfold solver_loop_state.
  unfold solver_state, sat_header_rep, var_header_rep, clause_header_rep,
    unconstrained_Assignment, solver_arrays_rep, variable_arrays_rep.
  Exists v_data cl_data.
  entailer!.
  unfold bcp_ready.
  destruct Hfresh as [Hwf [Hinstalled [_ [_ [Hnone Hnonempty]]]]].
  unfold no_conflict.
  intros c Hc Hfalse.
  rewrite Hinstalled in Hc.
  apply Forall_forall with (x := c) in Hnonempty; [|exact Hc].
  destruct c as [|l c']; [contradiction|].
  destruct Hwf as [_ Hwf].
  apply Forall_forall with (x := l :: c') in Hwf; [|exact Hc].
  inversion Hwf as [|? ? Hl _]; subst.
  unfold literal_wf in Hl.
  destruct (Hnone (literal_var l) Hl) as [Hnone_assignment _].
  specialize (Hfalse l (or_introl eq_refl)).
  unfold eval_partial_literal in Hfalse.
  rewrite Hnone_assignment in Hfalse.
  discriminate.
Qed.
Lemma proof_of_cdcl_solver_entail_wit_4 : cdcl_solver_entail_wit_4.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  (* Expose the three freshly-writable cells at index current_live_2 and the
     spare row-table slot; the RHS wrapper stores them at [slot - 1]. *)
  rewrite (IntArray.seg_shape_unfold states current_live_2 cap) by lia.
  Intros old_state.
  rewrite (IntArray.seg_shape_unfold true_counts current_live_2 cap) by lia.
  Intros old_true_count.
  rewrite (IntArray.seg_shape_unfold unassigned current_live_2 cap) by lia.
  Intros old_unassigned.
  sep_apply (installed_rows_capacity_expose row_table current_live_2 cap
    (snap_rows current_snap_2)); try lia.
  Exists current_live_2 (current_live_2 + 1) learned_row_2
    current_snap_2 bcp_ranks_2 logical_dl_2.
  unfold solver_install_slot_state.
  Exists pre_snap pre_ranks last old_state old_true_count old_unassigned
    v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    variable_arrays_rep, slot_at,
    StoreIntAsElement.storeA, StorePtrAsElement.undefstoreA.
  unfold learning_ready_conflict, installing_clause.
  entailer!.
  replace (current_live_2 + 1 - 1) with current_live_2 by lia.
  entailer!.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_5 : cdcl_solver_entail_wit_5.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  bind_fact (current_learning_exit_cert F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_2) (logical_dl_2))
    (dense_decode (learned_row_2))) as Hexit_cert.
  bind_fact (installing_clause F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_2) (logical_dl_2))
    n cap learned_row_2 (dense_decode (learned_row_2))
    current_live_2 (current_live_2 + 1)) as Hinstall.
  (* [solver_installed_row_state] fixes the header's clause count at
     [current_live + 1], so the loose [slot] the code carries has to be
     identified with it before the header cells will cancel.  [slot_at] is
     opaque to the strategy engine but is a plain equation in Coq. *)
  unfold slot_at in *.
  subst slot.
  (* Five existentials on the outside ([current_live], the learned row and the
     three ghosts, which are parameters of the wrapper), six on the inside. *)
  Exists current_live_2 learned_row_2 current_snap_2 bcp_ranks_2 logical_dl_2.
  unfold solver_installed_row_state.
  (* The installed snapshot is not existential in any useful sense: it is the
     current one with one entry appended to each clause-indexed list, which is
     exactly what [snapshot_installs] demands. *)
  Exists pre_snap
    (Build_dense_snapshot
       (snap_values current_snap_2)
       (snap_reasons current_snap_2)
       (snap_levels current_snap_2)
       (app (snap_rows current_snap_2) (cons learned_row_2 nil))
       (app (snap_states current_snap_2) (cons 1 nil))
       (app (snap_true_counts current_snap_2) (cons 0 nil))
       (app (snap_unassigned current_snap_2) (cons 0 nil)))
    pre_ranks last v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_summaries_explicit_rep, StorePtrAsElement.storeA,
    snapshot_installs.
  cbn [snap_values snap_reasons snap_levels snap_rows snap_states
       snap_true_counts snap_unassigned].
  assert (Hassigned :
    clause_vars_assigned
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_2 logical_dl_2)
      (dense_decode learned_row_2)).
  {
    eapply stable_false_clause_vars_assigned__decide_exit_solver_setup;
      [ assumption | ].
    exact (proj2 (proj1 Hexit_cert)).
  }
  entailer!.
  replace (current_live_2 + 1 - 1) with current_live_2 by lia.
  sep_apply (IntArray.seg_single states current_live_2 1).
  sep_apply
    (IntArray.seg_merge_to_full states 0 current_live_2
      (current_live_2 + 1)); try lia.
  replace (states + 0 * sizeof(INT)) with states by lia.
  replace (current_live_2 + 1 - 0) with (current_live_2 + 1) by lia.
  sep_apply (IntArray.seg_single true_counts current_live_2 0).
  sep_apply
    (IntArray.seg_merge_to_full true_counts 0 current_live_2
      (current_live_2 + 1)); try lia.
  replace (true_counts + 0 * sizeof(INT)) with true_counts by lia.
  replace (current_live_2 + 1 - 0) with (current_live_2 + 1) by lia.
  sep_apply (IntArray.seg_single unassigned current_live_2 0).
  sep_apply
    (IntArray.seg_merge_to_full unassigned 0 current_live_2
      (current_live_2 + 1)); try lia.
  replace (unassigned + 0 * sizeof(INT)) with unassigned by lia.
  replace (current_live_2 + 1 - 0) with (current_live_2 + 1) by lia.
  sep_apply
    (int_ptr_array_full_to_tail_missing__decide_exit_solver_setup
      row_table current_live_2 (snap_rows current_snap_2)
      new_cl learned_row_2); try lia.
  cancel.
  change ptr_size_Z with 4.
  change (sizeof(PTR)) with 4.
  unfold variable_arrays_rep.
  entailer!.
Qed.
Lemma proof_of_cdcl_solver_entail_wit_6_1 : cdcl_solver_entail_wit_6_1.
Proof.
  unfold cdcl_solver_entail_wit_6_1, conflict_levels_rep.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_exact
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_2) (logical_dl_2))
    learned_row_2 n max1 max2) as Htop.
  bind_fact (max1 = (-1)) as Hmax1_neg.
  bind_fact (coherent_snapshot F n current_live_2 original_count
    current_snap_2) as Hcoh.
  bind_fact (current_learning_exit_cert F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    (dense_decode (learned_row_2))) as Hexit_cert.
  bind_fact (snapshot_installs learned_row_2 current_snap_2 installed_snap_2)
    as Hinstalls.
  bind_fact (installing_clause F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    n cap learned_row_2 (dense_decode (learned_row_2))
    current_live_2 (current_live_2 + 1)) as Hinstall.
  assert (Hrow_len : Zlength learned_row_2 = n)
    by exact (proj1 (proj1 (proj2 (proj2 Hinstall)))).
  assert (Htop_minus :
    top_two_levels_exact
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      learned_row_2 n (-1) max2).
  { rewrite <- Hmax1_neg. exact Htop. }
  assert (Hempty : dense_decode learned_row_2 = nil).
  { eapply top_two_max1_minus1_empty_stable__decide_exit_solver_setup; eauto. }
  pose proof Hexit_cert as Hexit.
  unfold current_learning_exit_cert, learned_clause_sound in Hexit.
  destruct Hexit as [[Hentails _] _].
  rewrite Hempty in Hentails.
  assert (Hcnf_wf : cnf_wf n F).
  { eapply coherent_snapshot_cnf_wf__decide_exit_solver_setup. exact Hcoh. }
  assert (Hunsat : cnf_unsat n F).
  { eapply entails_empty_cnf_unsat__decide_exit_solver_setup; eauto. }
  pose proof Hcoh as Hcoherent_old.
  unfold coherent_snapshot in Hcoherent_old.
  destruct Hcoherent_old as [_ [_ [Hlengths_old _]]].
  unfold snapshot_lengths in Hlengths_old.
  destruct Hlengths_old as [_ [_ [_ [Hrows_old [_ [_ _]]]]]].
  assert (Hrows_new :
    Zlength (snap_rows current_snap_2 ++ learned_row_2 :: nil) =
      current_live_2 + 1).
  { rewrite Zlength_app, Hrows_old, Zlength_cons, Zlength_nil. lia. }
  assert (Hrow_lookup :
    Znth current_live_2
      (snap_rows current_snap_2 ++ learned_row_2 :: nil) nil = learned_row_2).
  { rewrite app_Znth2 by lia. rewrite Hrows_old.
    replace (current_live_2 - current_live_2) with 0 by lia.
    rewrite Znth0_cons. reflexivity. }
  pick_disjunct derivable1_orp_intros2.
  Exists retval current_snap_2 bcp_ranks_3 installed_snap_2
    current_live_2 logical_dl_2.
  destruct Hinstalls as [Hiv [Hir [Hil [Hirows [Hists [Hitc Hiua]]]]]].
  destruct installed_snap_2 as [iv ir il irows ists itc iua].
  cbn in Hiv, Hir, Hil, Hirows, Hists, Hitc, Hiua.
  subst iv ir il irows ists itc iua.
  unfold solver_state, unconstrained_Assignment, variable_arrays_rep,
         solver_arrays_rep, installed_rows_capacity_rep,
         sat_header_rep, var_header_rep, clause_header_rep, unsat_terminal.
  Exists v_data cl_data.
  cbn [snap_values snap_reasons snap_levels snap_rows snap_states
       snap_true_counts snap_unassigned].
  sep_apply (int_ptr_array_publish_existing__decide_exit_solver_setup
    row_table current_live_2 (current_live_2 + 1) new_cl
    (snap_rows current_snap_2 ++ learned_row_2 :: nil)
    learned_row_2 n); try lia.
  entailer!.
  - sep_apply (IntArray.full_to_seg states (current_live_2 + 1)
      (snap_states current_snap_2 +:: 1)).
    sep_apply (IntArray.full_to_seg true_counts (current_live_2 + 1)
      (snap_true_counts current_snap_2 +:: 0)).
    sep_apply (IntArray.full_to_seg unassigned (current_live_2 + 1)
      (snap_unassigned current_snap_2 +:: 0)).
    cancel.
  - destruct Hinstall as [_ [_ [Hrow_wf [_ _]]]].
    eapply publish_false_learned_clause_record__decide_exit_solver_setup;
      eauto.
  - exact Hrow_lookup.
Qed.
Lemma proof_of_cdcl_solver_entail_wit_6_2 : cdcl_solver_entail_wit_6_2.
Proof.
  unfold cdcl_solver_entail_wit_6_2, conflict_levels_rep.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_exact
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_2) (logical_dl_2))
    learned_row_2 n max1 max2) as Htop.
  bind_fact (max1 <> (-1)) as Hmax1_ne.
  bind_fact (max2 = (-1)) as Hmax2_neg.
  bind_fact (retval = 0) as Hretval.
  bind_fact (0 < logical_dl_2) as Hdl_pos.
  bind_fact (coherent_snapshot F n current_live_2 original_count
    current_snap_2) as Hcoh.
  bind_fact (stable_search_facts n current_snap_2 bcp_ranks_3
    logical_dl_2) as Hstable_facts.
  bind_fact (current_learning_exit_cert F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    (dense_decode (learned_row_2))) as Hexit_cert.
  bind_fact (clause_vars_assigned
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    (dense_decode (learned_row_2))) as Hassigned.
  bind_fact (dense_conflict_batch
    (cdcl_view_of_snapshot (n) (pre_snap_2) (pre_ranks_2) (logical_dl_2))
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    last_2) as Hbatch.
  bind_fact (snapshot_installs learned_row_2 current_snap_2 installed_snap_2)
    as Hinstalls.
  bind_fact (installing_clause F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    n cap learned_row_2 (dense_decode (learned_row_2))
    current_live_2 (current_live_2 + 1)) as Hinstall.
  assert (Hrow_len : Zlength learned_row_2 = n)
    by exact (proj1 (proj1 (proj2 (proj2 Hinstall)))).
  pose proof
    (installing_clause_rep_row_wf__decide_exit_solver_setup
      F
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      n cap learned_row_2 (dense_decode learned_row_2)
      current_live_2 (current_live_2 + 1) Hinstall)
    as Hrow_learned.
  pose proof Hstable_facts as Hstable.
  unfold stable_search_facts in Hstable.
  destruct Hstable as [_ [Hclosed _]].
  assert (Htop_zero :
    top_two_levels_exact
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      learned_row_2 n max1 (-1)).
  { rewrite <- Hmax2_neg. exact Htop. }
  pose proof
    (top_two_profile_zero__decide_exit_solver_setup
      F n learned_row_2
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      max1 Hrow_learned Hrow_len Hclosed Hdl_pos
      Hassigned Hexit_cert Htop_zero Hmax1_ne)
    as [Hsound [Hnode Hprofile]].
  pose proof
    (backjump_profile_cert__decide_exit_solver_setup
      F n learned_row_2
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      0 Hrow_learned Hclosed Hdl_pos Hsound Hnode Hprofile)
    as Hcert.
  pose proof Hcoh as Hcoherent_old.
  unfold coherent_snapshot in Hcoherent_old.
  destruct Hcoherent_old as [_ [_ [Hlengths_old _]]].
  unfold snapshot_lengths in Hlengths_old.
  destruct Hlengths_old as [_ [_ [_ [Hrows_old [_ [_ _]]]]]].
  assert (Hrows_new :
    Zlength (snap_rows current_snap_2 ++ learned_row_2 :: nil) =
      current_live_2 + 1).
  { rewrite Zlength_app, Hrows_old, Zlength_cons, Zlength_nil. lia. }
  assert (Hrow_lookup :
    Znth current_live_2
      (snap_rows current_snap_2 ++ learned_row_2 :: nil) nil = learned_row_2).
  { rewrite app_Znth2 by lia. rewrite Hrows_old.
    replace (current_live_2 - current_live_2) with 0 by lia.
    rewrite Znth0_cons. reflexivity. }
  pick_disjunct derivable1_orp_intros1.
  Exists pre_snap_2 pre_ranks_2 last_2 learned_row_2 retval
    current_snap_2 bcp_ranks_3 installed_snap_2 current_live_2 logical_dl_2.
  destruct Hinstalls as [Hiv [Hir [Hil [Hirows [Hists [Hitc Hiua]]]]]].
  destruct installed_snap_2 as [iv ir il irows ists itc iua].
  cbn in Hiv, Hir, Hil, Hirows, Hists, Hitc, Hiua.
  subst iv ir il irows ists itc iua.
  unfold backjump_state, variable_arrays_rep, solver_arrays_rep,
         installed_rows_capacity_rep, sat_header_rep, var_header_rep,
         clause_header_rep, pending_backjump_rep, pending_backjump_facts.
  Exists v_data cl_data.
  cbn [snap_values snap_reasons snap_levels snap_rows snap_states
       snap_true_counts snap_unassigned].
  sep_apply (int_ptr_array_publish_existing__decide_exit_solver_setup
    row_table current_live_2 (current_live_2 + 1) new_cl
    (snap_rows current_snap_2 ++ learned_row_2 :: nil)
    learned_row_2 n); try lia.
  entailer!.
  2: { eapply publish_false_learned_clause_record__decide_exit_solver_setup;
       eauto. }
  2: { exact Hrow_lookup. }
  sep_apply (IntArray.full_to_seg states (current_live_2 + 1)
    (snap_states current_snap_2 +:: 1)).
  sep_apply (IntArray.full_to_seg true_counts (current_live_2 + 1)
    (snap_true_counts current_snap_2 +:: 0)).
  sep_apply (IntArray.full_to_seg unassigned (current_live_2 + 1)
    (snap_unassigned current_snap_2 +:: 0)).
  entailer!.
  apply derivable1s_truep_intros; [ cancel | ].
  apply derivable1s_coq_prop_r.
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ apply map_app | ].
  split; [ exact Hbatch | ].
  rewrite Hretval.
  split; [ exact Hprofile | exact Hcert ].
Qed.

Lemma proof_of_cdcl_solver_entail_wit_6_3 : cdcl_solver_entail_wit_6_3.
Proof.
  unfold cdcl_solver_entail_wit_6_3, conflict_levels_rep.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_exact
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_2) (logical_dl_2))
    learned_row_2 n max1 max2) as Htop.
  bind_fact (max1 <> (-1)) as Hmax1_ne.
  bind_fact (max2 <> (-1)) as Hmax2_ne.
  bind_fact (retval = max2) as Hretval.
  bind_fact (0 < logical_dl_2) as Hdl_pos.
  bind_fact (coherent_snapshot F n current_live_2 original_count
    current_snap_2) as Hcoh.
  bind_fact (stable_search_facts n current_snap_2 bcp_ranks_3
    logical_dl_2) as Hstable.
  bind_fact (current_learning_exit_cert F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    (dense_decode (learned_row_2))) as Hexit_cert.
  bind_fact (clause_vars_assigned
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    (dense_decode (learned_row_2))) as Hassigned.
  bind_fact (dense_conflict_batch
    (cdcl_view_of_snapshot (n) (pre_snap_2) (pre_ranks_2) (logical_dl_2))
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    last_2) as Hbatch.
  bind_fact (snapshot_installs learned_row_2 current_snap_2 installed_snap_2)
    as Hinstalls.
  bind_fact (installing_clause F
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_3) (logical_dl_2))
    n cap learned_row_2 (dense_decode (learned_row_2))
    current_live_2 (current_live_2 + 1)) as Hinstall.
  assert (Hrow_wf : row_wf n learned_row_2)
    by exact (proj1 (proj2 (proj2 Hinstall))).
  assert (Hrow_len : Zlength learned_row_2 = n) by exact (proj1 Hrow_wf).
  pose proof Hstable as Hstable_copy.
  unfold stable_search_facts in Hstable_copy.
  destruct Hstable_copy as [_ [Hclosed _]].
  pose proof
    (top_two_profile_nonzero__decide_exit_solver_setup
      F n learned_row_2
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      max1 max2 Hrow_wf Hrow_len Hclosed Hdl_pos
      Hassigned Hexit_cert Htop Hmax1_ne Hmax2_ne)
    as [Hsound [Hnode Hprofile]].
  assert (Htarget_bounds : 0 <= max2 < logical_dl_2).
  {
    pose proof Hprofile as Hprofile_bounds.
    unfold backjump_target_profile in Hprofile_bounds.
    destruct Hprofile_bounds as
      [_ [_ [_ [[Htarget_zero _] | [Htarget_positive _]]]]].
    - rewrite Htarget_zero. lia.
    - exact Htarget_positive.
  }
  pose proof
    (backjump_profile_cert__decide_exit_solver_setup
      F n learned_row_2
      (cdcl_view_of_snapshot n current_snap_2 bcp_ranks_3 logical_dl_2)
      max2 Hrow_wf Hclosed Hdl_pos Hsound Hnode Hprofile)
    as Hcert.
  pose proof Hcoh as Hcoherent_old.
  unfold coherent_snapshot in Hcoherent_old.
  destruct Hcoherent_old as [_ [_ [Hlengths_old _]]].
  unfold snapshot_lengths in Hlengths_old.
  destruct Hlengths_old as [_ [_ [_ [Hrows_old [_ [_ _]]]]]].
  assert (Hrows_new :
    Zlength (snap_rows current_snap_2 ++ learned_row_2 :: nil) =
      current_live_2 + 1).
  { rewrite Zlength_app, Hrows_old, Zlength_cons, Zlength_nil. lia. }
  assert (Hrow_lookup :
    Znth current_live_2
      (snap_rows current_snap_2 ++ learned_row_2 :: nil) nil = learned_row_2).
  { rewrite app_Znth2 by lia. rewrite Hrows_old.
    replace (current_live_2 - current_live_2) with 0 by lia.
    rewrite Znth0_cons. reflexivity. }
  subst retval.
  pick_disjunct derivable1_orp_intros1.
  Exists pre_snap_2 pre_ranks_2 last_2 learned_row_2 max2
    current_snap_2 bcp_ranks_3 installed_snap_2
    current_live_2 logical_dl_2.
  destruct Hinstalls as [Hiv [Hir [Hil [Hirows [Hists [Hitc Hiua]]]]]].
  destruct installed_snap_2 as [iv ir il irows ists itc iua].
  cbn in Hiv, Hir, Hil, Hirows, Hists, Hitc, Hiua.
  subst iv ir il irows ists itc iua.
  unfold backjump_state, pending_backjump_rep, pending_backjump_facts,
         variable_arrays_rep, solver_arrays_rep,
         installed_rows_capacity_rep,
         sat_header_rep, var_header_rep, clause_header_rep.
  Exists v_data cl_data.
  cbn [snap_values snap_reasons snap_levels snap_rows snap_states
       snap_true_counts snap_unassigned].
  sep_apply (int_ptr_array_publish_existing__decide_exit_solver_setup
    row_table current_live_2 (current_live_2 + 1) new_cl
    (snap_rows current_snap_2 ++ learned_row_2 :: nil)
    learned_row_2 n); try lia.
  entailer!.
  - sep_apply (IntArray.full_to_seg states (current_live_2 + 1)
      (snap_states current_snap_2 +:: 1)).
    sep_apply (IntArray.full_to_seg true_counts (current_live_2 + 1)
      (snap_true_counts current_snap_2 +:: 0)).
    sep_apply (IntArray.full_to_seg unassigned (current_live_2 + 1)
      (snap_unassigned current_snap_2 +:: 0)).
    entailer!.
    apply _derivable1_andp_intros; [ cancel | ].
    apply derivable1s_coq_prop_r.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [apply map_app|].
    split; [exact Hbatch|].
    split; [exact Hprofile|].
    exact Hcert.
  - eapply publish_false_learned_clause_record__decide_exit_solver_setup;
      eauto.
  - exact Hrow_lookup.
Qed.
Lemma proof_of_cdcl_solver_entail_wit_8 : cdcl_solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  (* Both sides are folded -- [solver_after_bcp_state] on the left,
     [solver_state] on the right -- and the wrapper takes the snapshot, rank map
     and level as parameters, so [solver_state] is head-identical at identical
     arguments across the seam.  Reopen only the left, and hand the right its
     four existentials from the wrapper's own parameters. *)
  unfold solver_after_bcp_state.
  Intros pre_snap pre_ranks last.
  Exists bcp_ranks current_snap_2 current_live_2 logical_dl_2.
  entailer!.
  (* [decision_ready] is [propagation_quiescent], which is exactly what
     [bcp_outcome]'s quiescent arm carries; [conflict_cl = -1] kills the
     conflict arm. *)
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & Houtcome).
  unfold bcp_outcome in Houtcome.
  destruct Houtcome as [[_ Hquiet] | [Hlow _]].
  - exact Hquiet.
  - lia.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_9 : cdcl_solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  (* Both sides of the loop-back edge are folded: [decide]'s [Ensure] delivers
     [solver_state] on the left and the invariant is [solver_loop_state] on the
     right.  Since the wrapper's snapshot, rank map and level are parameters,
     all four existentials go in at once and [solver_state] is head-identical
     across the seam, with the struct pointers staying inside where both sides
     bind them.  The residual is the single pure fact the wrapper adds over
     [decide]'s post, [logical_dl + 1 <= n]. *)
  Exists current_live_2 final_snap final_ranks (logical_dl_2 + 1).
  unfold solver_loop_state.
  entailer!.
  eapply stable_search_level_bound__solver_analysis_and_returns
    with (F := F) (live := current_live_2)
      (original_count := original_count) (snap := final_snap)
      (ranks := final_ranks).
  - assumption.
  - assumption.
Qed.


(* ===== cdcl_solver slot-index safety wits (4 proofs) =====

   These four moved from the auto class to the manual one when block 4 was
   folded, and the reason is worth recording because it is the whole price of
   that fold.  Each asks for [slot - 1 <= INT_MAX], the index of the clause slot
   being written.  Before the fold the term was [current_live + 1 - 1] and
   [int_auto] bounded it straight from the contract's [current_live < cap].
   Folding replaced it with the opaque [slot], and the same opacity that stops
   the strategy engine from absorbing the four stored values (see
   reports/qcpsat-symexec-segv-upstream-20260731.md section 7a) also stops the
   range solver.

   So the bound has to come from the only other place that knows it: the header
   cell that stores [slot] is an [Int], hence in int range.  That is a stronger
   justification than the one these obligations had before, when they were
   simply admitted. *)
Lemma proof_of_cdcl_solver_safety_wit_14 : cdcl_solver_safety_wit_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold slot_at in *.
  sep_apply (store_int_range (&((s_pre) # "sat_data" ->ₛ "cl_size")) slot).
  Intros. entailer!.
  (* [INT_MAX] is a literal notation from SimpleC.SL.IntLib; the store's range
     fact is stated with CompCert's [Int.max_signed].  [change] checks the two
     are convertible rather than assuming it, so a target whose int is not 32
     bits fails here loudly instead of silently. *)
  change Int.max_signed with INT_MAX in H. lia.
Qed.

Lemma proof_of_cdcl_solver_safety_wit_16 : cdcl_solver_safety_wit_16.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold slot_at in *.
  sep_apply (store_int_range (&((s_pre) # "sat_data" ->ₛ "cl_size")) slot).
  Intros. entailer!.
  change Int.max_signed with INT_MAX in H. lia.
Qed.

Lemma proof_of_cdcl_solver_safety_wit_19 : cdcl_solver_safety_wit_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold slot_at in *.
  sep_apply (store_int_range (&((s_pre) # "sat_data" ->ₛ "cl_size")) slot).
  Intros. entailer!.
  change Int.max_signed with INT_MAX in H. lia.
Qed.

Lemma proof_of_cdcl_solver_safety_wit_22 : cdcl_solver_safety_wit_22.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold slot_at in *.
  sep_apply (store_int_range (&((s_pre) # "sat_data" ->ₛ "cl_size")) slot).
  Intros. entailer!.
  change Int.max_signed with INT_MAX in H. lia.
Qed.


(* ===== cdcl_solver return wits (5 proofs) ===== *)
Lemma proof_of_cdcl_solver_return_wit_1 : cdcl_solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (model_ready n
    (cdcl_view_of_snapshot (n) (current_snap) (decision_ranks) (logical_dl)))
    as Hmodel.
  unfold model_ready, propagation_quiescent in Hmodel.
  destruct Hmodel as [[Hno_conflict Hno_unit] Htotal].
  assert (Hmodels : models (rho_of_values n (snap_values current_snap)) F).
  {
    eapply model_ready_models_original__solver_analysis_and_returns
      with (F := F) (n := n) (live := current_live)
        (original_count := original_count) (snap := current_snap)
        (ranks := decision_ranks) (logical_dl := logical_dl).
    - assumption.
    - exact Hno_conflict.
    - exact Htotal.
  }
  unfold solver_state.
  Intros s_callee_v_data s_callee_cl_data.
  Exists (rho_of_values n (snap_values current_snap)).
  unfold solver_sat_arm_core, store_cnf, store_Assignment,
    unconstrained_Assignment,
    sat_header_rep, var_header_rep, clause_header_rep.
  Exists current_snap logical_dl current_live s_callee_v_data s_callee_cl_data.
  entailer!.
Qed.


(* ===== cdcl_solver partial_solve pure wits (3 proofs) =====

   These three bodies are UNCHANGED.  What moved is the numbering: the whole
   cdcl_solver partial_solve chain shifted up by one because folding the
   contract introduced a new call site, so the statement each body was written
   against is now one index higher.  Verified by byte-comparing the regenerated
   statements against the pre-regeneration ones:

     new wit_3_pure == old wit_2_pure   (auto-owned; proof_auto.v proves it)
     new wit_4_pure == old wit_3_pure   <- body below, was named wit_3_pure
     new wit_5_pure == old wit_4_pure   <- body below, was named wit_4_pure
     new wit_6_pure == old wit_5_pure   <- body below, was named wit_5_pure

   Leaving the old names in place would prove wit_3_pure twice (proof_auto.v
   already does, at its line 2738) and leave wit_6_pure with no proof at all.
   This is the rename-only class that a name-indexed oracle cannot see. *)

Lemma proof_of_cdcl_solver_partial_solve_wit_12_pure_manual_unused : cdcl_solver_partial_solve_wit_12_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_cdcl_solver_partial_solve_wit_4_pure : cdcl_solver_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (bcp_outcome
    (cdcl_view_of_snapshot (n) (current_snap) (bcp_ranks) (logical_dl))
    (cdcl_view_of_snapshot (n) (pre_snap) (pre_ranks) (logical_dl))
    current_live conflict_cl last) as Hbcp.
  bind_fact (conflict_cl <> (-1)) as Hconflict_ne.
  bind_fact (logical_dl <> 0) as Hdl_nz.
  bind_fact (0 <= logical_dl) as Hdl_nonneg.
  unfold bcp_outcome in Hbcp.
  destruct Hbcp as [[Hquiescent _] | [_ [Hlt [_ Hready]]]].
  { congruence. }
  entailer!.
Qed.


(* Renumbered AGAIN by the block-4 fold, and again body-identical: folding that
   Assert into [solver_install_slot_state] shifted the chain by one more, so what
   this body proves is now wit_7_pure.  Regeneration removed wit_6_pure outright,
   so leaving the old name here would leave the proof attached to nothing. *)
Lemma proof_of_cdcl_solver_partial_solve_wit_7_pure : cdcl_solver_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold solver_installed_row_state.
  Intros pre_snap_2 installed_snap_2 pre_ranks_2 last_2 v_data_2 cl_data_2.
  entailer!.
  unfold installing_clause in H.
  tauto.
Qed.


Lemma proof_of_cdcl_solver_entail_wit_2_1 : cdcl_solver_entail_wit_2_1.
Proof.
  (* bcp's conflict exit: [propagation_result] is [dense_conflict_batch] over
     [solver_state], and [solver_after_bcp_state] is the same [solver_state]
     under [bcp_outcome]'s conflict arm.  Both sides are folded, so only the
     two wrappers come apart (trap b): reopen the left one, hand its three
     existentials straight back to the right one. *)
  left.
  LLM_pre_process ltac:(int_auto).
  unfold propagation_result.
  Intros pre_snap pre_ranks last.
  Exists current_live_2 snap1 ranks1 logical_dl_2.
  unfold solver_after_bcp_state.
  Exists pre_snap pre_ranks last.
  entailer!.
  unfold bcp_outcome.
  right.
  repeat split; assumption.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_2_2 : cdcl_solver_entail_wit_2_2.
Proof.
  (* bcp's quiescent exit.  [bcp_outcome]'s first arm mentions no pre-state,
     so the three existentials of [solver_after_bcp_state] are supplied with
     arbitrary values. *)
  left.
  LLM_pre_process ltac:(int_auto).
  Exists current_live_2 snap1 ranks1 logical_dl_2.
  unfold solver_after_bcp_state.
  Exists snap1 ranks1 0.
  entailer!.
  unfold bcp_outcome.
  left.
  split; assumption.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_3 : cdcl_solver_entail_wit_3.
Proof.
  (* clause_learning's return, folded into [solver_learning_state].  The left
     side is [learning_state] (headers + reasons/levels + row table) plus the
     caller's frame; the right side's [solver_state] is headers + all three
     variable arrays + all the clause-summary segments, so both bundles and
     their components have to come apart (trap a).
     [conflict_cl < live], the conflict batch and [learning_ready_conflict] are
     not hypotheses here: they are recovered from [bcp_outcome]'s conflict arm,
     which is the only arm left once [conflict_cl <> -1] (trap e). *)
  left.
  LLM_pre_process ltac:(int_auto).
  bind_fact (conflict_cl <> (-1)) as Hne.
  bind_fact (bcp_outcome
    (cdcl_view_of_snapshot (n) (current_snap_2) (bcp_ranks_2) (logical_dl_2))
    (cdcl_view_of_snapshot (n) (pre_snap) (pre_ranks) (logical_dl_2))
    current_live_2 conflict_cl last) as Houtcome.
  unfold bcp_outcome in Houtcome.
  destruct Houtcome as [[Hquiet _] | (Hlo & Hhi & Hbatch & Hready)];
    [ contradiction | ].
  Exists current_live_2 learned_row_2 current_snap_2 bcp_ranks_2 logical_dl_2.
  unfold solver_learning_state.
  Exists pre_snap pre_ranks last.
  unfold learning_state, solver_state, unconstrained_Assignment,
    variable_arrays_rep, solver_arrays_rep.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_7_1 : cdcl_solver_entail_wit_7_1.
Proof.
  (* Same hand-off as wit_2_1, one iteration later: the loop has re-entered
     [bcp] after installing the learned row and backjumping, so the live count
     is [current_live_2 + 1] and the level is [back_dl].  The block-6 fold
     replaced the longhand size/level ghosts [s_cl_size] and [max2] by those
     two expressions, but the math is unchanged: the size bound comes from
     [current_live_2 < cap] and the level bound from
     [back_dl < logical_dl_2 <= n]. *)
  left.
  LLM_pre_process ltac:(int_auto).
  unfold propagation_result.
  Intros bpre_snap bpre_ranks blast.
  Exists (current_live_2 + 1) snap1 ranks1 back_dl.
  unfold solver_after_bcp_state.
  Exists bpre_snap bpre_ranks blast.
  entailer!.
  unfold bcp_outcome.
  right.
  repeat split; assumption.
Qed.

Lemma proof_of_cdcl_solver_entail_wit_7_2 : cdcl_solver_entail_wit_7_2.
Proof.
  (* Quiescent [bcp] exit one iteration later: the loop has re-entered [bcp]
     after the backjump, so the live count is [current_live_2 + 1] and the
     level is [back_dl].  The RHS spatial atom is [solver_after_bcp_state] at
     exactly the snapshot the LHS [solver_state] already holds, so the whole
     entailment is a re-packaging: pick the pre-batch view to be the post-batch
     view and take [bcp_outcome]'s quiescent arm. *)
  left.
  LLM_pre_process ltac:(int_auto).
  Exists (current_live_2 + 1) snap1 ranks1 back_dl.
  unfold solver_after_bcp_state.
  Exists snap1 ranks1 0.
  entailer!.
  unfold bcp_outcome.
  left.
  split; assumption.
Qed.

(* cdcl_solver_return_wit_3: the block-6 fold shifted the return witnesses down one;
   this is the proof that was written for cdcl_solver_return_wit_4, whose statement
   is now cdcl_solver_return_wit_3's.  Matched on the statement, not the name. *)
Lemma proof_of_cdcl_solver_return_wit_3 : cdcl_solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst current_live.
  unfold solver_capacity_exhausted_arm_core, store_cnf,
    unconstrained_Assignment, solver_arrays_rep, variable_arrays_rep,
    sat_header_rep, var_header_rep, clause_header_rep.
  Exists current_snap logical_dl new_cl learned_row v_data cl_data.
  all: entailer!.
Qed.

(* cdcl_solver_return_wit_4: the block-6 fold shifted the return witnesses down one;
   this is the proof that was written for cdcl_solver_return_wit_5, whose statement
   is now cdcl_solver_return_wit_4's.  Matched on the statement, not the name. *)
Lemma proof_of_cdcl_solver_return_wit_4 : cdcl_solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (bcp_outcome
    (cdcl_view_of_snapshot (n) (current_snap) (bcp_ranks) (logical_dl))
    (cdcl_view_of_snapshot (n) (pre_snap) (pre_ranks) (logical_dl))
    current_live conflict_cl last) as Houtcome.
  bind_fact (conflict_cl <> (-1)) as Hne.
  unfold bcp_outcome in Houtcome.
  destruct Houtcome as [[Hquiet _] | [_ [_ [_ Hconflict]]]].
  { exfalso. apply Hne. exact Hquiet. }
  subst logical_dl.
  unfold learning_ready_conflict in Hconflict.
  destruct Hconflict as [c [Hnth Hfalse]].
  unfold solver_unsat_arm_core, store_cnf, unconstrained_Assignment,
    solver_arrays_rep, variable_arrays_rep,
    sat_header_rep, var_header_rep, clause_header_rep.
  Exists current_snap 0 current_live v_data cl_data.
  entailer!.
  eapply root_conflict_implies_cnf_unsat__solver_analysis_and_returns
    with (F := F) (n := n) (live := current_live)
      (original_count := original_count) (snap := current_snap)
      (ranks := bcp_ranks).
  - assumption.
  - assumption.
  - exists c. split.
    + now apply nth_error_In in Hnth.
    + exact Hfalse.
Qed.

Lemma proof_of_cdcl_solver_return_wit_2 : cdcl_solver_return_wit_2.
Proof.
  unfold cdcl_solver_return_wit_2.
  left. intros.
  (* The UNSAT verdict is DERIVED here, inside the checked class.
     unsat_terminal has two routes; the root-conflict route is vacuous at this
     program point because current_level is logical_dl definitionally and the
     assertion carries 0 < logical_dl. *)
  assert (Hunsat : cnf_unsat n F).
  { match goal with
    | Hterm : unsat_terminal _ _ |- _ => destruct Hterm as [[Hlevel _] | Hentails]
    end.
    - cbn in Hlevel. lia.
    - eapply entails_empty_cnf_unsat__decide_exit_solver_setup; [ | exact Hentails ].
      match goal with
      | Hc : coherent_snapshot _ _ _ _ _ |- _ =>
          eapply coherent_snapshot_cnf_wf__decide_exit_solver_setup; exact Hc
      end. }
  unfold solver_unsat_arm_core, store_cnf, unconstrained_Assignment,
         variable_arrays_rep, solver_arrays_rep, sat_header_rep,
         var_header_rep, clause_header_rep, installed_rows_capacity_rep.
  Exists installed_snap back_dl (current_live + 1) v_data cl_data.
  entailer!.
Qed.

