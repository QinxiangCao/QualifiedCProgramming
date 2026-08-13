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

Lemma proof_of_qcpsat_fill_ints_entail_wit_1 : qcpsat_fill_ints_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  unfold repeat_Z. simpl.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
  cbn.
  entailer!.
Qed.

Lemma proof_of_qcpsat_fill_ints_entail_wit_2 : qcpsat_fill_ints_entail_wit_2.
Proof.
  aggressive_pre_process.
  symmetry.
  apply repeat_Z_tail.
  lia.
Qed.

(* ===== qcpsat_fill_ints return wits (1 proofs) ===== *)
Lemma proof_of_qcpsat_fill_ints_return_wit_1 : qcpsat_fill_ints_return_wit_1.
Proof.
  aggressive_pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  entailer!.
Qed.

(* ===== clause_resolution entail wits (7 proofs) ===== *)
Lemma proof_of_clause_resolution_entail_wit_1 : clause_resolution_entail_wit_1.
Proof.
  aggressive_pre_process.
  bind_fact (row_wf n left) as Hrwl.
  bind_fact (row_wf n right) as Hrwr.
  unfold resolution_prefix.
  destruct Hrwl as [Hll _].
  destruct Hrwr as [Hlr _].
  pose proof (Zlength_repeat_Z__dense_array_prefix_kernels 0 n ltac:(lia)) as Hzr.
  repeat split; try lia.
  intros k Hk.
  unfold repeat_Z.
  apply Znth_repeat.
Qed.
Lemma proof_of_clause_resolution_entail_wit_2_1 : clause_resolution_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  bind_fact ((Znth i left 0) <> 0) as Hnz.
  bind_fact (row_wf n left) as Hrwl.
  bind_fact (resolution_prefix left right out_2 i) as Hpref.
  eapply resolution_prefix_advance__dense_array_prefix_kernels.
  - destruct Hrwl as [Hleft _]. lia.
  - symmetry.
    rewrite <- PreH3.
    apply dense_cancel_cell_left_nonzero; [exact Hnz | intros [[Ha Hb]|[Ha Hb]]; lia].
  - exact Hpref.
Qed.

Lemma proof_of_clause_resolution_entail_wit_2_2 : clause_resolution_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  bind_fact ((Znth i left 0) <> 0) as Hnz.
  bind_fact (row_wf n left) as Hrwl.
  bind_fact (resolution_prefix left right out_2 i) as Hpref.
  eapply resolution_prefix_advance__dense_array_prefix_kernels.
  - destruct Hrwl as [Hleft _]. lia.
  - symmetry.
    rewrite <- PreH4.
    apply dense_cancel_cell_left_nonzero; [exact Hnz | intros [[Ha Hb]|[Ha Hb]]; lia].
  - exact Hpref.
Qed.

Lemma proof_of_clause_resolution_entail_wit_2_3 : clause_resolution_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  bind_fact (row_wf n left) as Hrwl.
  exfalso.
  assert (Hrange : var_in_range n i) by (unfold var_in_range; lia).
  pose proof (row_wf_cell_domain n left i Hrwl Hrange) as Hd.
  destruct Hd as [Hd|[Hd|Hd]]; lia.
Qed.

Lemma proof_of_clause_resolution_entail_wit_2_4 : clause_resolution_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  bind_fact ((Znth i left 0) = 0) as Hz.
  bind_fact (row_wf n left) as Hrwl.
  bind_fact (resolution_prefix left right out_2 i) as Hpref.
  eapply resolution_prefix_advance__dense_array_prefix_kernels.
  - destruct Hrwl as [Hleft _]. lia.
  - symmetry.
    rewrite Hz.
    apply dense_cancel_cell_left_zero.
  - exact Hpref.
Qed.

Lemma proof_of_clause_resolution_entail_wit_2_5 : clause_resolution_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  bind_fact (row_wf n left) as Hrwl.
  bind_fact (resolution_prefix left right out_2 i) as Hpref.
  eapply resolution_prefix_advance__dense_array_prefix_kernels.
  - destruct Hrwl as [Hleft _]. lia.
  - symmetry.
    apply dense_cancel_cell_complementary.
    left; split; assumption.
  - exact Hpref.
Qed.

Lemma proof_of_clause_resolution_entail_wit_2_6 : clause_resolution_entail_wit_2_6.
Proof.
  aggressive_pre_process.
  bind_fact (row_wf n left) as Hrwl.
  bind_fact (resolution_prefix left right out_2 i) as Hpref.
  eapply resolution_prefix_advance__dense_array_prefix_kernels.
  - destruct Hrwl as [Hleft _]. lia.
  - symmetry.
    apply dense_cancel_cell_complementary.
    right; split; assumption.
  - exact Hpref.
Qed.

(* ===== clause_resolution return wits (1 proofs) ===== *)
Lemma proof_of_clause_resolution_return_wit_1 : clause_resolution_return_wit_1.
Proof.
  aggressive_pre_process.
  - apply dense_cancel_union_row_wf__dense_array_prefix_kernels; assumption.
  - bind_fact (resolution_prefix left right out i) as Hpref.
    bind_fact (row_wf n left) as Hrwl.
    pose proof Hpref as HP.
    assert (Hi : i = n) by lia.
    subst i.
    unfold resolution_prefix in HP.
    destruct HP as [Hb [Hlo [Hro [Hpre Htail]]]].
    destruct Hrwl as [Hll _].
    apply list_eq_ext with (d := 0).
    split.
    + rewrite Zlength_dense_cancel_union__dense_array_prefix_kernels by congruence.
      congruence.
    + intros k Hk.
      rewrite Hpre by lia.
      symmetry.
      apply Znth_dense_cancel_union__dense_array_prefix_kernels; [congruence | lia].
Qed.

(* ===== clause_learning entail wits (11 proofs) ===== *)
Lemma proof_of_clause_learning_entail_wit_1 : clause_learning_entail_wit_1.
Proof.
  aggressive_pre_process; try entailer!.
  all: bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  - assert (Hrows : Zlength (snap_rows snap) = live)
      by (unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto).
    rewrite (Znth_indep (snap_rows snap) wi_pre
      __default__List_Z nil) by (rewrite Hrows; lia).
    entailer!.
  - intros. unfold repeat_Z. apply Znth_repeat.
  - pose proof (coherent_snapshot_row_wf__learning_row_and_scan
      F n live original_count snap wi_pre Hcoh ltac:(lia)) as [Hlen _].
    exact Hlen.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    reflexivity.
Qed.


Lemma proof_of_clause_learning_entail_wit_2 : clause_learning_entail_wit_2.
Proof.
  unfold clause_learning_entail_wit_2.
  left.
  intros.
  bind_fact ((Zlength (copied_2)) = n) as Hcopied_len.
  bind_fact (forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (copied_2) (0)) = (Znth (k) ((Znth (wi_pre) ((snap_rows (snap))) ((@nil Z)))) (0))))) as Hprefix.
  bind_fact (forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (copied_2) (0)) = 0))) as Hsuffix.
  Exists conflict_row_ptr_2
    (replace_Znth i
      (Znth i (Znth wi_pre (snap_rows snap) nil) 0) copied_2).
  entailer!.
  - unfold learning_focus_state.
    Exists v_data cl_data.
    unfold installed_row_focus_rep, StorePtrAsElement.storeA,
           sat_header_rep, var_header_rep, clause_header_rep.
    change (sizeof (PTR)) with ptr_size_Z.
    fold_arch.
    entailer!.
  - intros k_2 Hk.
    rewrite Znth_replace_Znth_Diff by (try rewrite Hcopied_len; lia).
    apply Hsuffix. lia.
  - intros k Hk.
    destruct (Z.eq_dec k i) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by (rewrite Hcopied_len; lia).
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hcopied_len; lia).
      apply Hprefix. lia.
  - rewrite Zlength_replace_Znth, Hcopied_len. reflexivity.
Qed.

Lemma proof_of_clause_learning_entail_wit_3 : clause_learning_entail_wit_3.
Proof.
  aggressive_pre_process.
  all: bind_fact (0 < logical_dl) as Hdl_pos.
  all: bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  all: bind_fact (stable_search_facts n snap ranks logical_dl ) as Hstable.
  all: bind_fact (forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (copied) (0)) = (Znth (k) ((Znth (wi_pre) ((snap_rows (snap))) ((@nil Z)))) (0))))) as Hprefix.
  all: bind_fact (learning_ready_conflict (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) wi_pre ) as Hready.
  - unfold installed_rows_capacity_rep.
    change (sizeof (PTR)) with ptr_size_Z.
    fold_arch.
    pose proof (installed_row_focus_merge row_table live wi_pre
      conflict_row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep, StorePtrAsElement.storeA in Hmerge.
    sep_apply_l_atomic Hmerge.
    entailer!.
  - dump_pre_spatial.
    unfold learning_ready_conflict in Hready.
    destruct Hready as [c [Hnth Hfalse]].
    assert (Hi : i = n) by lia.
    subst i.
    assert (Hcopied : copied = Znth wi_pre (snap_rows snap) nil).
    { apply (proj2
        (list_eq_ext copied (Znth wi_pre (snap_rows snap) nil) 0)).
      split; [lia|].
      intros k Hk. apply Hprefix. lia. }
    subst copied.
    pose proof (installed_conflict_learning_seed__learning_row_and_scan
      F n live original_count snap ranks logical_dl wi_pre c
      Hdl_pos ltac:(lia) Hcoh Hstable Hnth Hfalse) as Hseed.
    destruct Hseed as [Hwf [Hentails [Hfalse' Hsupport]]].
    unfold learning_loop. cbv zeta.
    split; [exact Hwf | ].
    split; [exact Hentails | ].
    split; [exact Hfalse' | ].
    split; [exact Hsupport | ].
    split; [lia | ].
    intros x Hx. lia.
Qed.

Lemma proof_of_clause_learning_entail_wit_6_manual_unused : clause_learning_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst scan.
  Exists working_2.
  split_pure_spatial.
  - cancel (IntArray.full res n working_2).
    cancel (learning_state s_pre values reasons levels states true_counts
      unassigned row_table n live cap logical_dl snap).
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try lia.
Qed.

Lemma proof_of_clause_learning_entail_wit_7 : clause_learning_entail_wit_7.
Proof.
  aggressive_pre_process; try entailer!.
  all: bind_fact ((Znth scan (snap_reasons (snap)) 0) <> (-1)) as Hreason_some.
  all: bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  all: pose proof
    (snapshot_reason_bounds__learning_row_and_scan
      F n live original_count snap scan Hcoh
      ltac:(unfold var_in_range; lia) Hreason_some) as Hbounds;
    lia.
Qed.


Lemma proof_of_clause_learning_entail_wit_8 : clause_learning_entail_wit_8.
Proof.
  aggressive_pre_process; try entailer!.
  all: bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  - assert (Hrows : Zlength (snap_rows snap) = live)
      by (unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto).
    rewrite (Znth_indep (snap_rows snap) wj
      __default__List_Z nil) by (rewrite Hrows; lia).
    entailer!.
  - pose proof (coherent_snapshot_row_wf__learning_row_and_scan
      F n live original_count snap wj Hcoh ltac:(lia)) as [Hlen _].
    exact Hlen.
Qed.


Lemma proof_of_clause_learning_entail_wit_9_1 : clause_learning_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  bind_fact ((Znth scan (snap_levels (snap)) 0) <> logical_dl) as Hlevel_ne.
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (learning_loop F (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n working_2 scan ) as Hloop.
  eapply learning_loop_scan_advance__learning_row_and_scan.
  - lia.
  - right. left. intro Hlevel.
    apply Hlevel_ne.
    eapply snapshot_level_cell__learning_row_and_scan;
      [exact Hcoh | unfold var_in_range; lia |].
    exact Hlevel.
  - exact Hloop.
Qed.

Lemma proof_of_clause_learning_entail_wit_9_2 : clause_learning_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  bind_fact ((Znth scan (snap_reasons (snap)) 0) = (-1)) as Hreason_none.
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (learning_loop F (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n working_2 scan ) as Hloop.
  bind_fact ((Znth scan (snap_levels (snap)) 0) = logical_dl) as Hlevel.
  eapply learning_loop_scan_advance__learning_row_and_scan.
  - lia.
  - right. right.
    eapply snapshot_reason_none_from_cell__learning_row_and_scan;
      [exact Hcoh | unfold var_in_range; lia | exact Hreason_none].
  - exact Hloop.
Qed.

Lemma proof_of_clause_learning_entail_wit_9_3 : clause_learning_entail_wit_9_3.
Proof.
  aggressive_pre_process.
  bind_fact ((Znth scan working_2 0) = 0) as Hcell_zero.
  bind_fact (learning_loop F (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n working_2 scan ) as Hloop.
  eapply learning_loop_scan_advance__learning_row_and_scan.
  - lia.
  - left. exact Hcell_zero.
  - exact Hloop.
Qed.

Lemma proof_of_clause_learning_entail_wit_10_1 : clause_learning_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  assert (scan_2 = n) by lia.
  subst scan_2.
  entailer!.
Qed.

Lemma proof_of_clause_learning_entail_wit_10_2 : clause_learning_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  all: bind_fact (row_wf n (dense_cancel_union (working_2) ((Znth (wj) ((snap_rows (snap))) ((@nil Z))))) ) as Hmerged_wf.
  all: bind_fact (wj = (Znth (i) ((snap_reasons (snap))) (0))) as Hwj_def.
  all: bind_fact ((Zlength ((Znth (wj) ((snap_rows (snap))) ((@nil Z))))) = n) as Hrow_len.
  all: bind_fact ((Znth (i) (working_2) (0)) <> 0) as Hcell_nz.
  all: bind_fact (0 < logical_dl) as Hdl_pos.
  all: bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  all: bind_fact (stable_search_facts n snap ranks logical_dl ) as Hstable.
  all: bind_fact (learning_loop F (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n working_2 i ) as Hloop.
  - unfold installed_rows_capacity_rep.
    change (sizeof (PTR)) with ptr_size_Z.
    fold_arch.
    pose proof (installed_row_focus_merge row_table live wj
      reason_row_ptr (snap_rows snap) ltac:(lia)) as Hmerge.
    unfold installed_row_focus_rep, StorePtrAsElement.storeA in Hmerge.
    rewrite Hrow_len in Hmerge.
    sep_apply_l_atomic Hmerge.
    entailer!.
  - dump_pre_spatial.
    exact (snapshot_learning_loop_resolution__learning_row_and_scan
      F n live original_count snap ranks logical_dl working_2 i wj
      Hdl_pos Hcoh Hstable ltac:(unfold var_in_range; lia) ltac:(lia)
      Hwj_def Hmerged_wf Hcell_nz Hloop).
Qed.

(* ===== clause_learning return wits (1 proofs) ===== *)
Lemma proof_of_clause_learning_return_wit_1 : clause_learning_return_wit_1.
Proof.
  aggressive_pre_process.
  all: bind_fact (learning_loop F (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n working scan ) as Hloop.
  - subst scan.
    unfold learning_loop in Hloop.
    destruct Hloop as [Hwf [Hentails [Hfalse [Hsupport [_ Hprocessed]]]]].
    exact (learning_loop_exit_cert__learning_row_and_scan
      F (cdcl_view_of_snapshot n snap ranks logical_dl) n working
      Hwf Hentails Hfalse Hsupport Hprocessed).
  - subst scan.
    unfold learning_loop in Hloop.
    destruct Hloop as [Hwf _].
    exact Hwf.
Qed.

(* ===== clause_learning partial_solve wits (1 proofs) ===== *)
(* Folding [clause_learning]'s contract into [learning_state] shifted this
   function's partial_solve chain.  The current generator also emits the two
   row-well-formedness split goals in their semantic order. *)
Lemma proof_of_clause_learning_partial_solve_wit_13_pure : clause_learning_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact ((Zlength ((Znth (wj) ((snap_rows (snap))) ((@nil Z))))) = n) as Hrow_len.
  bind_fact (0 < n) as Hn_pos.
  bind_fact (n < INT_MAX) as Hn_max.
  bind_fact (coherent_snapshot F n live original_count snap ) as Hcoh.
  bind_fact (learning_loop F (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n working i ) as Hloop.
  unfold learning_loop in Hloop.
  destruct Hloop as [Hworking _].
  pose proof (coherent_snapshot_row_wf__learning_row_and_scan
    F n live original_count snap wj Hcoh ltac:(lia)) as Hreason.
  split_pures.
  - dump_pre_spatial. exact Hn_pos.
  - dump_pre_spatial. exact Hn_max.
  - dump_pre_spatial. exact Hreason.
  - dump_pre_spatial. exact Hworking.
Qed.


(* ===== conflict_analysis entail wits (6 proofs) ===== *)
Lemma proof_of_conflict_analysis_entail_wit_1 : conflict_analysis_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold top_two_levels_prefix.
  entailer!.
  - unfold conflict_levels_rep.
    entailer!.
  - unfold top_two_levels_exact.
    left.
    split.
    + intros d Hprocessed.
      destruct Hprocessed as [x [[Hx0 Hxlt] _]].
      lia.
    + lia.
Qed.

Lemma proof_of_conflict_analysis_entail_wit_2_1 : conflict_analysis_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1 max2) as Hprefix.
  bind_fact ((Znth i row 0) <> 0) as Hcell_ne.
  prop_apply (IntArray.full_Zlength levels n (snap_levels snap)).
  Intros_p Hlevels.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  pose proof
    (dense_assigned_cell_level__learning_to_conflict_levels
      n snap ranks logical_dl row i Hrow Hassigned
      ltac:(lia) Hlevels Hcell_ne) as [Hlevel He].
  assert (Hstep :
    top_two_levels_exact
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      row (i + 1) (Znth i (snap_levels snap) 0) max1).
  {
    eapply top_two_levels_exact_step_new_max__learning_to_conflict_levels;
      eauto; lia.
  }
  unfold top_two_levels_prefix.
  entailer!.
  all: entailer!.
Qed.
Lemma proof_of_conflict_analysis_entail_wit_2_2 : conflict_analysis_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1 max2) as Hprefix.
  bind_fact ((Znth i row 0) <> 0) as Hcell_ne.
  prop_apply (IntArray.full_Zlength levels n (snap_levels snap)).
  Intros_p Hlevels.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  pose proof
    (dense_assigned_cell_level__learning_to_conflict_levels
      n snap ranks logical_dl row i Hrow Hassigned
      ltac:(lia) Hlevels Hcell_ne) as [Hlevel He].
  assert (Hstep :
    top_two_levels_exact
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      row (i + 1) max1 (Znth i (snap_levels snap) 0)).
  {
    eapply top_two_levels_exact_step_new_second__learning_to_conflict_levels;
      eauto; lia.
  }
  unfold top_two_levels_prefix.
  entailer!.
  all: entailer!.
Qed.
Lemma proof_of_conflict_analysis_entail_wit_2_3 : conflict_analysis_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1 max2) as Hprefix.
  bind_fact ((Znth i row 0) <> 0) as Hcell_ne.
  prop_apply (IntArray.full_Zlength levels n (snap_levels snap)).
  Intros_p Hlevels.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  pose proof
    (dense_assigned_cell_level__learning_to_conflict_levels
      n snap ranks logical_dl row i Hrow Hassigned
      ltac:(lia) Hlevels Hcell_ne) as [Hlevel He].
  assert (Hstep :
    top_two_levels_exact
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      row (i + 1) max1 max2).
  {
    eapply top_two_levels_exact_step_below_second__learning_to_conflict_levels;
      eauto; lia.
  }
  unfold top_two_levels_prefix.
  entailer!.
  all: entailer!.
Qed.
Lemma proof_of_conflict_analysis_entail_wit_2_4 : conflict_analysis_entail_wit_2_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1 max2) as Hprefix.
  bind_fact ((Znth i row 0) <> 0) as Hcell_ne.
  prop_apply (IntArray.full_Zlength levels n (snap_levels snap)).
  Intros_p Hlevels.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  pose proof
    (dense_assigned_cell_level__learning_to_conflict_levels
      n snap ranks logical_dl row i Hrow Hassigned
      ltac:(lia) Hlevels Hcell_ne) as [Hlevel He].
  assert (Hstep :
    top_two_levels_exact
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      row (i + 1) max1 max2).
  {
    eapply top_two_levels_exact_step_equal_max__learning_to_conflict_levels;
      eauto; lia.
  }
  unfold top_two_levels_prefix.
  entailer!.
  all: entailer!.
Qed.
Lemma proof_of_conflict_analysis_entail_wit_2_5 : conflict_analysis_entail_wit_2_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1 max2) as Hprefix.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  assert (Hstep :
    top_two_levels_exact
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      row (i + 1) max1 max2).
  {
    eapply top_two_levels_exact_step_zero__learning_to_conflict_levels;
      eauto; lia.
  }
  unfold top_two_levels_prefix.
  entailer!.
  all: entailer!.
Qed.
(* ===== conflict_analysis return wits (3 proofs) ===== *)
Lemma proof_of_conflict_analysis_return_wit_1 : conflict_analysis_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1_2 max2_2) as Hprefix.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  assert (Hi : i = n) by lia.
  subst i.
  Right.
  Exists max1_2 max2_2.
  entailer!.
  unfold conflict_levels_rep.
  entailer!.
Qed.
Lemma proof_of_conflict_analysis_return_wit_2 : conflict_analysis_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1_2 max2_2) as Hprefix.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  assert (Hi : i = n) by lia.
  subst i.
  Left.
  Exists max1_2 max2_2.
  entailer!.
  unfold conflict_levels_rep.
  entailer!.
Qed.
Lemma proof_of_conflict_analysis_return_wit_3 : conflict_analysis_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  bind_fact (top_two_levels_prefix (cdcl_view_of_snapshot (n) (snap) (ranks) (logical_dl)) n row i max1_2 max2_2) as Hprefix.
  unfold top_two_levels_prefix in Hprefix.
  destruct Hprefix as [Hrow [Hassigned [Hrange Hexact]]].
  assert (Hi : i = n) by lia.
  subst i.
  Exists max1_2 max2_2.
  entailer!.
  unfold conflict_levels_rep.
  entailer!.
Qed.
(* ===== bcp safety wits (3 proofs) ===== *)
Lemma proof_of_bcp_entail_wit_1 : bcp_entail_wit_1.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  unfold unit_scan.
  entailer!.
Qed.
Lemma proof_of_bcp_entail_wit_2 : bcp_entail_wit_2.
Proof.
  aggressive_pre_process.
  bind_fact (Znth (i - 0) (snap_states snap) 0 <> 2) as Hstate_ne_two.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (unit_scan (cdcl_view_of_snapshot n snap ranks logical_dl) live i) as Hclause_scan.
  unfold solver_arrays_rep, variable_arrays_rep.
  unfold unit_scan, bcp_ready.
  Intros.
  entailer!.
  unfold unit_scan in Hclause_scan.
  destruct Hclause_scan as [[Hi0 Hilive] Hscan].
  intros j Hj.
  destruct (Z_lt_ge_dec j i) as [Hji|Hji].
  - apply Hscan; lia.
  - assert (j = i) by lia; subst j.
    destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
      F n live original_count snap i Hcoh) as
      [row [Hrow [Hrowwf Hsummary]]]; [lia|].
    exists (dense_decode row); split.
    + cbn [cdcl_view_of_snapshot].
      eapply map_nth_error; exact Hrow.
    + intro Hunit.
      apply Hstate_ne_two.
      replace (i - 0) with i by lia.
      apply (proj2
        (summary_state_two_iff_unit__bcp_unit_to_assignment
          _ _ _ _ _ Hsummary)).
      exact Hunit.
Qed.
Lemma proof_of_bcp_entail_wit_3 : bcp_entail_wit_3.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  all: unfold unit_scan, unit_variable_scan, bcp_ready.
  all: Intros.
  all: entailer!.
  - bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    assert (Hrowslen : Zlength (snap_rows snap) = live).
    { unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto. }
    assert (Hindep :
      Znth i (snap_rows snap) __default__List_Z =
      Znth i (snap_rows snap) (@nil Z)).
    { apply Znth_indep. rewrite Hrowslen; lia. }
    rewrite Hindep; entailer!.
  - bind_fact (Znth (i - 0) (snap_states snap) 0 = 2) as Hstate_two.
    bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    destruct (coherent_snapshot_unit_row__bcp_unit_to_assignment
      F n live original_count snap i Hcoh ltac:(lia)
      ltac:(replace (i - 0) with i in Hstate_two by lia; exact Hstate_two)) as
      [row [Hrow [Hrowwf [Hunit Hunassigned]]]].
    exists (dense_decode row); split.
    + cbn [cdcl_view_of_snapshot]. eapply map_nth_error; exact Hrow.
    + split.
      * cbn [cdcl_view_of_snapshot]. exact Hunit.
      * intros x Hx; lia.
  - bind_fact (Znth (i - 0) (snap_states snap) 0 = 2) as Hstate_two.
    bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    destruct (coherent_snapshot_unit_row__bcp_unit_to_assignment
      F n live original_count snap i Hcoh ltac:(lia)
      ltac:(replace (i - 0) with i in Hstate_two by lia; exact Hstate_two)) as
      [row [Hrow [Hrowwf [Hunit Hunassigned]]]].
    exact Hunassigned.
  - bind_fact (Znth (i - 0) (snap_states snap) 0 = 2) as Hstate_two.
    bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    destruct (coherent_snapshot_unit_row__bcp_unit_to_assignment
      F n live original_count snap i Hcoh ltac:(lia)
      ltac:(replace (i - 0) with i in Hstate_two by lia; exact Hstate_two)) as
      [row [Hrow [[Hrowlen Hrowcells] [Hunit Hunassigned]]]].
    assert (Hz : Znth i (snap_rows snap) (@nil Z) = row).
    { unfold Znth; eapply nth_error_nth; exact Hrow. }
    rewrite Hz; exact Hrowlen.
Qed.
Lemma proof_of_bcp_entail_wit_4 : bcp_entail_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (unit_variable_scan (cdcl_view_of_snapshot n snap ranks logical_dl) n live unitcl 0) as Hvarscan.
  unfold variable_arrays_rep.
  unfold unit_variable_scan, bcp_ready.
  Intros.
  pose proof Hvarscan as Hscan.
  unfold unit_variable_scan in Hscan.
  destruct Hscan as [Hunitidx [Hnext [c [Hnth [Hunit Hprefix]]]]].
  destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
    F n live original_count snap unitcl Hcoh ltac:(lia)) as
    [row [Hrow [Hrowwf Hsummary]]].
  assert (Hc : c = dense_decode row).
  { change (nth_error (map dense_decode (snap_rows snap))
      (Z.to_nat unitcl) = Some c) in Hnth.
    rewrite nth_error_map, Hrow in Hnth.
    inversion Hnth; reflexivity. }
  subst c.
  change (clause_unit (snapshot_assignment n snap) (dense_decode row)) in Hunit.
  assert (Hcells : snapshot_cells_wf n live snap).
  { unfold coherent_snapshot in Hcoh; tauto. }
  destruct (unit_dense_row_candidate__bcp_unit_to_assignment
    n live snap row Hcells Hrowwf Hunit) as
    [candidate [Hcandidate [Hvalue Hcell]]].
  assert (Hzrow : Znth unitcl (snap_rows snap) (@nil Z) = row).
  { unfold Znth; eapply nth_error_nth; exact Hrow. }
  Exists candidate.
  entailer!.
  rewrite Hzrow; exact Hcell.
Qed.
Lemma proof_of_bcp_entail_wit_5_1 : bcp_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - bind_fact ((Zlength (Znth unitcl (snap_rows snap) (@nil Z))) = n) as Hrowlen.
    rewrite Hrowlen.
    unfold unit_variable_scan.
    bind_fact (Znth i (snap_values snap) 0 <> (-1)) as Hval_i.
    bind_fact (Znth candidate_2 (snap_values snap) (-1) = (-1)) as Hval_cand.
    bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    pose proof (snapshot_value_defaults_eq__bcp_unit_to_assignment
      F n live original_count snap i 0 (-1) Hcoh
        ltac:(unfold var_in_range; lia)) as Hdefaults.
    assert (Hicandidate : i < candidate_2).
    { destruct (Z.eq_dec i candidate_2) as [Heq|Hneq]; [|lia].
      subst candidate_2; exfalso; apply Hval_i.
      rewrite Hdefaults; exact Hval_cand. }
    Exists candidate_2.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. exact Hval_cand.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial.
      split; [lia | ].
      split; [lia | ].
      match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
        unfold unit_variable_scan in Hsrc;
        destruct Hsrc as [Hidx [Hnext [c [Hnth [Hunit Hprefix]]]]] end.
      exists c; split; [exact Hnth|].
      split; [exact Hunit|].
      change (forall x : Z,
        0 <= x < i + 1 ->
        snapshot_assignment n snap x = None ->
        ~ (In (Pos x) c \/ In (Neg x) c)).
      change (forall x : Z,
        0 <= x < i ->
        snapshot_assignment n snap x = None ->
        ~ (In (Pos x) c \/ In (Neg x) c)) in Hprefix.
      eapply unit_prefix_advance_assigned__bcp_unit_to_assignment;
        eauto; lia.
Qed.
Lemma proof_of_bcp_entail_wit_5_2 : bcp_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  unfold unit_variable_scan, bcp_ready.
  Intros.
  entailer!.
  match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
    unfold unit_variable_scan in Hsrc;
    destruct Hsrc as [Hidx [Hnext [c [Hnth [Hunit Hprefix]]]]] end.
  exists c; split; [exact Hnth|].
  split; [exact Hunit|].
  change (forall x : Z,
    0 <= x < i + 1 ->
    snapshot_assignment n snap x = None ->
    ~ (In (Pos x) c \/ In (Neg x) c)).
  change (forall x : Z,
    0 <= x < i ->
    snapshot_assignment n snap x = None ->
    ~ (In (Pos x) c \/ In (Neg x) c)) in Hprefix.
  eapply unit_prefix_advance_assigned__bcp_unit_to_assignment;
    eauto; lia.
Qed.
Lemma proof_of_bcp_entail_wit_5_3 : bcp_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  - unfold variable_arrays_rep.
    bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    bind_fact ((Zlength (Znth unitcl (snap_rows snap) (@nil Z))) = n) as Hrow_len.
    rewrite Hrow_len.
    unfold unit_variable_scan, bcp_ready.
    Intros.
    entailer!.
    assert (Hicandidate : i < candidate_2).
    { destruct (Z.eq_dec i candidate_2) as [Heq|Hneq]; [|lia].
      subst candidate_2; exfalso; apply PreH8; exact PreH1. }
    Exists candidate_2.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial.
        split; [lia | ].
        split; [lia | ].
        match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
          unfold unit_variable_scan in Hsrc;
          destruct Hsrc as [Hidx [Hnext [c [Hnth [Hunit Hprefix]]]]] end.
        destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
          F n live original_count snap unitcl Hcoh ltac:(lia)) as
          [row [Hrow [Hrowwf Hsummary]]].
        assert (Hc : c = dense_decode row).
        { pose proof Hnth as Hnth_map.
          change (nth_error (map dense_decode (snap_rows snap))
            (Z.to_nat unitcl) = Some c) in Hnth_map.
          rewrite nth_error_map, Hrow in Hnth_map.
          inversion Hnth_map; reflexivity. }
        assert (Hzrow : Znth unitcl (snap_rows snap) (@nil Z) = row).
        { unfold Znth; eapply nth_error_nth; exact Hrow. }
        rewrite Hzrow in PreH1.
        exists c; split; [exact Hnth|].
        split; [exact Hunit|].
        change (forall x : Z,
          0 <= x < i + 1 ->
          snapshot_assignment n snap x = None ->
          ~ (In (Pos x) c \/ In (Neg x) c)).
        change (forall x : Z,
          0 <= x < i ->
          snapshot_assignment n snap x = None ->
          ~ (In (Pos x) c \/ In (Neg x) c)) in Hprefix.
        eapply unit_prefix_advance_zero__bcp_unit_to_assignment;
          eauto; lia.
Qed.
Lemma proof_of_bcp_entail_wit_5_4 : bcp_entail_wit_5_4.
Proof.
  aggressive_pre_process.
  bind_fact (Znth i (Znth unitcl (snap_rows snap) (@nil Z)) 0 = 0) as Hcell_i.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  unfold variable_arrays_rep.
  unfold unit_variable_scan, bcp_ready.
  Intros.
  entailer!.
  match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
    unfold unit_variable_scan in Hsrc;
    destruct Hsrc as [Hidx [Hnext [c [Hnth [Hunit Hprefix]]]]] end.
  destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
    F n live original_count snap unitcl Hcoh ltac:(lia)) as
    [row [Hrow [Hrowwf Hsummary]]].
  assert (Hc : c = dense_decode row).
  { pose proof Hnth as Hnth_map.
    change (nth_error (map dense_decode (snap_rows snap))
      (Z.to_nat unitcl) = Some c) in Hnth_map.
    rewrite nth_error_map, Hrow in Hnth_map.
    inversion Hnth_map; reflexivity. }
  assert (Hzrow : Znth unitcl (snap_rows snap) (@nil Z) = row).
  { unfold Znth; eapply nth_error_nth; exact Hrow. }
  rewrite Hzrow in Hcell_i.
  exists c; split; [exact Hnth|].
  split; [exact Hunit|].
  change (forall x : Z,
    0 <= x < i + 1 ->
    snapshot_assignment n snap x = None ->
    ~ (In (Pos x) c \/ In (Neg x) c)).
  change (forall x : Z,
    0 <= x < i ->
    snapshot_assignment n snap x = None ->
    ~ (In (Pos x) c \/ In (Neg x) c)) in Hprefix.
  eapply unit_prefix_advance_zero__bcp_unit_to_assignment;
    eauto; lia.
Qed.
Lemma proof_of_bcp_entail_wit_6_3 : bcp_entail_wit_6_3.
Proof.
  solve_bcp_unit_unassigned_zero unitcl F n live original_count snap i.
  rewrite PreH13.
  exact PreH23.
Qed.


Lemma proof_of_bcp_entail_wit_6_2 : bcp_entail_wit_6_2.
Proof.
  solve_bcp_unit_unassigned_zero unitcl F n live original_count snap i.
  rewrite PreH14.
  exact PreH24.
Qed.


Lemma proof_of_bcp_entail_wit_6_1 : bcp_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (Znth candidate (snap_values snap) (-1) = (-1)) as Hvalue_minus.
  unfold variable_arrays_rep.
  replace (unitcl - 0) with unitcl by lia.
  pose proof (snapshot_value_defaults_eq__bcp_unit_to_assignment
    F n live original_count snap candidate 0 (-1) Hcoh
      ltac:(unfold var_in_range; lia)) as Hdefaults.
  assert (Hvalue_zero : Znth candidate (snap_values snap) 0 = -1).
  { rewrite Hdefaults; exact Hvalue_minus. }
  assert (Hunassigned_len : Zlength (snap_unassigned snap) = live).
  { unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto. }
  assert (Hupdated :
    Znth unitcl
      (replace_Znth unitcl
        (Znth unitcl (snap_unassigned snap) 0 - 1)
        (snap_unassigned snap)) 0 = 0).
  { rewrite Znth_replace_Znth_Same; [lia|].
    rewrite Hunassigned_len; lia. }
  Exists candidate.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. rewrite PreH11; lia.
    + dump_pre_spatial. exact Hupdated.
    + dump_pre_spatial.
      rewrite PreH11.
      unfold unit_variable_scan.
      split; [lia|].
      split; [lia|].
      match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
        unfold unit_variable_scan in Hsrc;
        destruct Hsrc as [Hidx [Hnext [c [Hnth [Hunit Hprefix]]]]] end.
      exists c; split; [exact Hnth|].
      split; [exact Hunit|].
      intros x Hx Hnone.
      apply Hprefix; [lia|exact Hnone].
Qed.

Lemma proof_of_bcp_entail_wit_7 : bcp_entail_wit_7.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists unit_row_ptr_2 updated_unassigned_2 scanned_2.
  split_pure_spatial.
  - unfold solver_row_focus_state, solver_arrays_rep, variable_arrays_rep,
      sat_header_rep, var_header_rep, clause_header_rep,
      clause_summaries_explicit_rep, installed_row_focus_rep,
      StorePtrAsElement.storeA.
    Exists v_data cl_data.
    try rewrite sizeof_ptr.
    fold_arch.
    sepcon_assoc_change.
    cancel;
      try (split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia).
  - split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
Qed.

Lemma proof_of_bcp_entail_wit_8_1 : bcp_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  bind_fact (Znth bcpvar (Znth unitcl (snap_rows snap) (@nil Z)) 0 = 1) as Hcell_pos.
  bind_fact (Znth bcpvar (snap_values snap) (-1) = (-1)) as Hval_bcpvar.
  bind_fact (Znth unitcl (snap_unassigned snap) 0 = 1) as Hunassigned_one.
  bind_fact (updated_unassigned =
    replace_Znth unitcl (Znth unitcl (snap_unassigned snap) 0 - 1)
      (snap_unassigned snap)) as Hupd_eq.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (stable_search_facts n snap ranks logical_dl) as Hstable.
  bind_fact (bcp_ready (cdcl_view_of_snapshot n snap ranks logical_dl)) as Hready.
  unfold variable_arrays_rep.
  Right.
  unfold unit_variable_scan, bcp_ready.
  Intros.
  match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
    unfold unit_variable_scan in Hsrc;
    destruct Hsrc as [Hunitidx [Hscanned [c [Hnth [Hunit Hprefix]]]]] end.
  destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
    F n live original_count snap unitcl Hcoh ltac:(lia)) as
    [row [Hrow [Hrowwf Hsummary]]].
  assert (Hc : c = dense_decode row).
  { change (nth_error (map dense_decode (snap_rows snap))
      (Z.to_nat unitcl) = Some c) in Hnth.
    rewrite nth_error_map, Hrow in Hnth.
    inversion Hnth; reflexivity. }
  assert (Hzrow : Znth unitcl (snap_rows snap) (@nil Z) = row).
  { unfold Znth; eapply nth_error_nth; exact Hrow. }
  assert (Hrange : var_in_range n bcpvar) by
    (unfold var_in_range; lia).
  assert (Hnone : snapshot_assignment n snap bcpvar = None).
  { unfold snapshot_assignment.
    assert (Hguard : andb (Z.leb 0 bcpvar) (Z.ltb bcpvar n) = true).
    { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    rewrite Hguard, Hval_bcpvar; reflexivity. }
  assert (Hin : In (Pos bcpvar) c).
  { rewrite Hc.
    apply (proj1 (dense_decode_pos n row bcpvar Hrowwf Hrange)).
    rewrite <- Hzrow; exact Hcell_pos. }
  assert (Hlength : snapshot_lengths n live snap).
  { unfold coherent_snapshot in Hcoh; tauto. }
  assert (Hsummaries : snapshot_summaries_exact n live snap).
  { unfold coherent_snapshot in Hcoh; tauto. }
  destruct (snapshot_unit_stable_assigns__bcp_unit_to_assignment
    n live snap ranks logical_dl bcpvar true unitcl c
    Hlength Hrange ltac:(lia) Hnone Hnth Hunit Hin Hstable) as
    [Hstable_new Hassigns].
  assert (Hunit_dense :
    clause_unit (snapshot_assignment n snap)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))).
  { assert (Hzc :
      Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal) = c).
    { unfold Znth; eapply nth_error_nth; exact Hnth. }
    rewrite Hzc; exact Hunit. }
  assert (Hin_dense :
    In (satisfying_literal bcpvar true)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))).
  { change (In (Pos bcpvar)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))).
    assert (Hzc :
      Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal) = c).
    { unfold Znth; eapply nth_error_nth; exact Hnth. }
    rewrite Hzc; exact Hin. }
  pose proof (mixed_summaries_unit_seed__bcp_unit_to_assignment
    n live cap snap bcpvar true unitcl Hlength Hrange
    ltac:(lia) ltac:(lia) Hsummaries Hnone Hunit_dense Hin_dense) as Hmixed.
  change (mixed_clause_summaries
    (snapshot_assignment n snap)
    (snapshot_assignment n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => snapshot_set_at snap x b reason d)
        snap bcpvar true logical_dl unitcl))
    (map dense_decode (snap_rows snap))
    (replace_Znth unitcl 0 (snap_states snap))
    (replace_Znth unitcl 1 (snap_true_counts snap))
    (replace_Znth unitcl 0 (snap_unassigned snap))
    live cap 0 (Some unitcl)) in Hmixed.
  assert (Hupdated :
    updated_unassigned = replace_Znth unitcl 0 (snap_unassigned snap)).
  { rewrite Hupd_eq, Hunassigned_one; replace (1 - 1) with 0 by lia; reflexivity. }
  Exists (replace_Znth unitcl 1 (snap_true_counts snap))
    (replace_Znth unitcl 0 (snap_unassigned snap))
    1 true
    ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => snapshot_set_at snap x b reason d)
      snap bcpvar true logical_dl unitcl)
    ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => Mapping.total_mapping_update ranks x (Some rx)) ranks bcpvar
      (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)))
    (replace_Znth unitcl 0 (snap_states snap)) 0.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_conflict_prefix, bcp_assignment_delta.
  rewrite Hupdated.
  pose proof (installed_row_focus_merge row_table live unitcl unit_row_ptr
    (snap_rows snap) ltac:(lia)) as Hm.
  unfold installed_row_focus_rep, StorePtrAsElement.storeA in Hm.
  try rewrite sizeof_ptr.
  fold_arch.
  sep_apply Hm.
  split_pure_spatial.
  - cbn [snap_values snap_reasons snap_levels].
    cancel.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try reflexivity;
      try lia.
    + cbn [snap_values snap_reasons snap_levels].
      repeat split; try reflexivity; try assumption; try lia.
    + pose proof Hready as H0. unfold bcp_ready, no_conflict in H0.
    assert (Hstates_len : Zlength (snap_states snap) = live).
    { unfold snapshot_lengths in Hlength; tauto. }
    destruct (Z.eq_dec 0 unitcl) as [Heq|Hneq].
    * subst unitcl.
      rewrite Znth_replace_Znth_Same; [lia|rewrite Hstates_len; lia].
    * rewrite Znth_replace_Znth_Diff; try lia;
        try (rewrite Hstates_len; lia).
      intro Hstate.
      destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
        F n live original_count snap 0 Hcoh ltac:(lia)) as
        [row0 [Hrow0 [Hrow0wf Hsummary0]]].
      apply (H0 (dense_decode row0)).
      { cbn [cdcl_view_of_snapshot].
        eapply nth_error_In; eapply map_nth_error; exact Hrow0.
      }
      { eapply summary_state_one_implies_false__bcp_unit_to_assignment;
          eauto. }
    + cbn [snap_rows snap_values snap_reasons snap_levels].
      split; [reflexivity|].
      split.
      { left; split; [exact Hcell_pos|reflexivity]. }
      { split; [reflexivity|].
        split; [reflexivity|].
        split; [reflexivity|].
        exact Hassigns. }
    + split; [exact Hassigns|].
      split; [lia|].
      exact Hmixed.
Qed.

Lemma proof_of_bcp_entail_wit_8_2 : bcp_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  bind_fact (Znth bcpvar (Znth unitcl (snap_rows snap) (@nil Z)) 0 <> 1) as Hcell_ne_one.
  bind_fact (Znth bcpvar (Znth unitcl (snap_rows snap) (@nil Z)) 0 <> 0) as Hcell_ne_zero.
  bind_fact (Znth bcpvar (snap_values snap) (-1) = (-1)) as Hval_bcpvar.
  bind_fact (Znth unitcl (snap_unassigned snap) 0 = 1) as Hunassigned_one.
  bind_fact (updated_unassigned =
    replace_Znth unitcl (Znth unitcl (snap_unassigned snap) 0 - 1)
      (snap_unassigned snap)) as Hupd_eq.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  bind_fact (stable_search_facts n snap ranks logical_dl) as Hstable.
  bind_fact (bcp_ready (cdcl_view_of_snapshot n snap ranks logical_dl)) as Hready.
  unfold variable_arrays_rep.
  Right.
  unfold unit_variable_scan, bcp_ready.
  Intros.
  match goal with Hsrc : unit_variable_scan _ _ _ _ _ |- _ =>
    unfold unit_variable_scan in Hsrc;
    destruct Hsrc as [Hunitidx [Hscanned [c [Hnth [Hunit Hprefix]]]]] end.
  destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
    F n live original_count snap unitcl Hcoh ltac:(lia)) as
    [row [Hrow [Hrowwf Hsummary]]].
  assert (Hc : c = dense_decode row).
  { change (nth_error (map dense_decode (snap_rows snap))
      (Z.to_nat unitcl) = Some c) in Hnth.
    rewrite nth_error_map, Hrow in Hnth.
    inversion Hnth; reflexivity. }
  assert (Hzrow : Znth unitcl (snap_rows snap) (@nil Z) = row).
  { unfold Znth; eapply nth_error_nth; exact Hrow. }
  assert (Hrange : var_in_range n bcpvar) by
    (unfold var_in_range; lia).
  assert (Hnone : snapshot_assignment n snap bcpvar = None).
  { unfold snapshot_assignment.
    assert (Hguard : andb (Z.leb 0 bcpvar) (Z.ltb bcpvar n) = true).
    { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    rewrite Hguard, Hval_bcpvar; reflexivity. }
  assert (Hcellneg :
    Znth bcpvar (Znth unitcl (snap_rows snap) (@nil Z)) 0 = -1).
  { rewrite Hzrow.
    pose proof (row_wf_cell_domain n row bcpvar Hrowwf Hrange) as Hdomain.
    rewrite Hzrow in Hcell_ne_one, Hcell_ne_zero.
    destruct Hdomain as [Hneg|[Hzero|Hpos]]; lia. }
  assert (Hin : In (Neg bcpvar) c).
  { rewrite Hc.
    apply (proj1 (dense_decode_neg n row bcpvar Hrowwf Hrange)).
    rewrite <- Hzrow; exact Hcellneg. }
  assert (Hlength : snapshot_lengths n live snap).
  { unfold coherent_snapshot in Hcoh; tauto. }
  assert (Hsummaries : snapshot_summaries_exact n live snap).
  { unfold coherent_snapshot in Hcoh; tauto. }
  destruct (snapshot_unit_stable_assigns__bcp_unit_to_assignment
    n live snap ranks logical_dl bcpvar false unitcl c
    Hlength Hrange ltac:(lia) Hnone Hnth Hunit Hin Hstable) as
    [Hstable_new Hassigns].
  assert (Hunit_dense :
    clause_unit (snapshot_assignment n snap)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))).
  { assert (Hzc :
      Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal) = c).
    { unfold Znth; eapply nth_error_nth; exact Hnth. }
    rewrite Hzc; exact Hunit. }
  assert (Hin_dense :
    In (satisfying_literal bcpvar false)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))).
  { change (In (Neg bcpvar)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))).
    assert (Hzc :
      Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal) = c).
    { unfold Znth; eapply nth_error_nth; exact Hnth. }
    rewrite Hzc; exact Hin. }
  pose proof (mixed_summaries_unit_seed__bcp_unit_to_assignment
    n live cap snap bcpvar false unitcl Hlength Hrange
    ltac:(lia) ltac:(lia) Hsummaries Hnone Hunit_dense Hin_dense) as Hmixed.
  change (mixed_clause_summaries
    (snapshot_assignment n snap)
    (snapshot_assignment n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => snapshot_set_at snap x b reason d)
        snap bcpvar false logical_dl unitcl))
    (map dense_decode (snap_rows snap))
    (replace_Znth unitcl 0 (snap_states snap))
    (replace_Znth unitcl 1 (snap_true_counts snap))
    (replace_Znth unitcl 0 (snap_unassigned snap))
    live cap 0 (Some unitcl)) in Hmixed.
  assert (Hupdated :
    updated_unassigned = replace_Znth unitcl 0 (snap_unassigned snap)).
  { rewrite Hupd_eq, Hunassigned_one; replace (1 - 1) with 0 by lia; reflexivity. }
  Exists (replace_Znth unitcl 1 (snap_true_counts snap))
    (replace_Znth unitcl 0 (snap_unassigned snap))
    0 false
    ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => snapshot_set_at snap x b reason d)
      snap bcpvar false logical_dl unitcl)
    ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => Mapping.total_mapping_update ranks x (Some rx)) ranks bcpvar
      (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)))
    (replace_Znth unitcl 0 (snap_states snap)) 0.
  unfold solver_explicit_state.
  Exists v_data cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_conflict_prefix, bcp_assignment_delta.
  rewrite Hupdated.
  pose proof (installed_row_focus_merge row_table live unitcl unit_row_ptr
    (snap_rows snap) ltac:(lia)) as Hm.
  unfold installed_row_focus_rep, StorePtrAsElement.storeA in Hm.
  try rewrite sizeof_ptr.
  fold_arch.
  sep_apply Hm.
  split_pure_spatial.
  - cbn [snap_values snap_reasons snap_levels].
    cancel.
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try reflexivity;
      try lia.
    + cbn [snap_values snap_reasons snap_levels].
      repeat split; try reflexivity; try assumption; try lia.
    + pose proof Hready as H0. unfold bcp_ready, no_conflict in H0.
    assert (Hstates_len : Zlength (snap_states snap) = live).
    { unfold snapshot_lengths in Hlength; tauto. }
    destruct (Z.eq_dec 0 unitcl) as [Heq|Hneq].
    * subst unitcl.
      rewrite Znth_replace_Znth_Same; [lia|rewrite Hstates_len; lia].
    * rewrite Znth_replace_Znth_Diff; try lia;
        try (rewrite Hstates_len; lia).
      intro Hstate.
      destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
        F n live original_count snap 0 Hcoh ltac:(lia)) as
        [row0 [Hrow0 [Hrow0wf Hsummary0]]].
      apply (H0 (dense_decode row0)).
      { cbn [cdcl_view_of_snapshot].
        eapply nth_error_In; eapply map_nth_error; exact Hrow0.
      }
      { eapply summary_state_one_implies_false__bcp_unit_to_assignment;
          eauto. }
    + cbn [snap_rows snap_values snap_reasons snap_levels].
      split; [reflexivity|].
      split.
      { right; split; [exact Hcellneg|reflexivity]. }
      { split; [reflexivity|].
        split; [reflexivity|].
        split; [reflexivity|].
        exact Hassigns. }
    + split; [exact Hassigns|].
      split; [lia|].
      exact Hmixed.
Qed.

