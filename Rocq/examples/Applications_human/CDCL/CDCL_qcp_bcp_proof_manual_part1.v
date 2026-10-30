From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_bcp_goal.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_bcp_proof_auto.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_lib.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_common.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_tactics.
Import naive_C_Rules.
Local Open Scope sac.

Ltac poly_store_unfold := cbn [poly_store poly_undef_store].

Lemma proof_of_bcp_entail_wit_1 : bcp_entail_wit_1.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  unfold unit_scan.
  cdcl_entailer.
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
  cdcl_entailer.
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
  all: (unfold unit_scan, unit_variable_scan, bcp_ready);
    (Intros);
    (cdcl_entailer).
  - bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
    assert (Hrowslen : Zlength (snap_rows snap) = live).
    { unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto. }
    assert (Hindep :
      Znth i (snap_rows snap) __default__List_Z =
      Znth i (snap_rows snap) (@nil Z)).
    { apply Znth_indep. rewrite Hrowslen; lia. }
    rewrite Hindep; cdcl_entailer.
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
  cdcl_entailer.
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
  cdcl_entailer.
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
    cdcl_entailer.
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
  cdcl_entailer.
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
    sepcon_assoc_change.
    msat_cancel_sound; cancel.
  - split_pures; dump_pre_spatial; assumption.
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
    ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => sat_function_update ranks x (Some rx)) ranks bcpvar
      (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)))
    (replace_Znth unitcl 0 (snap_states snap)) 0.
  unfold solver_explicit_state.
  Exists v_data.
  Exists cl_data.
  unfold sat_header_rep, var_header_rep, clause_header_rep,
    clause_arrays_explicit_rep, clause_summaries_explicit_rep,
    installed_rows_capacity_rep.
  unfold bcp_clause_scan, bcp_conflict_prefix, bcp_assignment_delta.
  rewrite Hupdated.
  pose proof (installed_row_focus_merge row_table live unitcl unit_row_ptr
    (snap_rows snap) ltac:(lia)) as Hm.
  unfold installed_row_focus_rep, StorePtrAsElement.storeA in Hm.
  simpl.
  split_pure_spatial.
  - cancel (&("i") # Int |-> 0).
    cancel (IntArray.full levels n
      (replace_Znth bcpvar logical_dl (snap_levels snap))).
    cancel (IntArray.full reasons n
      (replace_Znth bcpvar unitcl (snap_reasons snap))).
    cancel (IntArray.full values n
      (replace_Znth bcpvar 1 (snap_values snap))).
    cancel (PtrArray.undef_seg row_table live cap).
    cancel.
    sep_apply_l_atomic Hm.
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
    ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => sat_function_update ranks x (Some rx)) ranks bcpvar
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
  sep_apply Hm. clear Hm.
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



