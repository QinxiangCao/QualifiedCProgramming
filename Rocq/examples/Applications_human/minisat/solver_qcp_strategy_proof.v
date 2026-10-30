From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_strategy_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.
Local Open Scope string.

Lemma solver_qcp_strategy72_correctness : solver_qcp_strategy72.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst cursor.
  assert (Hindex : 0 < index) by
    (change (sizeof (INT)) with 4 in H0; lia).
  prop_apply_p (IntArray.seg_Zlength base 0 hi arr).
  Intros.
  sep_apply_l_atomic (IntArray.seg_split_to_missing_i base 0 (index - 1) hi arr 0).
  - dump_pre_spatial. lia.
  - unfold StoreIntAsElement.storeA.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
    Intros_r value.
    apply_sepcon_adjoint.
    Intros_p Hvalue.
    subst value.
    replace (index - 1 - 0) with (index - 1) by lia.
    replace (base + index * sizeof(INT) + -1 * sizeof(INT))
      with (base + (index - 1) * sizeof(INT)) by ring.
    simpl.
    replace (base + index * 4 + -4) with (base + (index - 1) * 4) by lia.
    cancel.
Qed.

Lemma solver_qcp_strategy73_correctness : solver_qcp_strategy73.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst cursor.
  replace (base + index * sizeof(INT) + -1 * sizeof(INT))
    with (base + (index - 1) * sizeof(INT)) by
      (change (sizeof (INT)) with 4; lia).
  unfold StoreIntAsElement.storeA.
  replace (base + index * 4 + -4)
    with (base + (index - 1) * sizeof(INT)) by
      (change (sizeof (INT)) with 4; lia).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_seg base 0 (index - 1) hi
    (Znth (index - 1) arr 0) arr).
  - dump_pre_spatial. lia.
  - replace (index - 1 - 0) with (index - 1) by lia.
    rewrite replace_Znth_Znth by lia.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy12_correctness : solver_qcp_strategy12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (DoubleArray.seg_Zlength p lo hi l).
  Intros.
  sep_apply_l_atomic
    (DoubleArray.seg_split_to_missing_i
       p lo i hi l msat_fp64_zero).
  - dump_pre_spatial. lia.
  - unfold StoreDoubleAsElement.storeA.
    cancel (DoubleArray.missing_i p i lo hi l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    unfold double_Znth.
    cancel.
Qed.

Lemma solver_qcp_strategy36_correctness : solver_qcp_strategy36.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.seg_split_to_missing_i p lo 0 hi l 0).
  - dump_pre_spatial.
    lia.
  - replace (p + 0 * 4) with p by lia.
    cancel (IntArray.missing_i p 0 lo hi l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hfocus.
    subst v.
    cancel.
    replace (p + 0 * sizeof ( INT )) with p
      by (rewrite sizeof_int; lia).
    replace (0 - lo) with (- lo) by lia.
    cancel.
Qed.

Lemma solver_qcp_strategy69_correctness : solver_qcp_strategy69.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Halias.
  assert (Hbase : p = q).
  { destruct Halias as [Hforward | Hbackward];
    [exact Hforward | symmetry; exact Hbackward]. }
  subst q.
  split_pure_spatial.
  - Intros.
    sep_apply_l_atomic (IntArray.seg_split_to_missing_i p lo 0 hi l 0).
    + dump_pre_spatial.
      lia.
    + replace (p + 0 * 4) with p by lia.
      cancel (IntArray.missing_i p 0 lo hi l).
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hfocus.
      subst v.
      cancel.
      replace (p + 0 * sizeof ( INT )) with p
        by (rewrite sizeof_int; lia).
      replace (0 - lo) with (- lo) by lia.
      cancel.
  - dump_pre_spatial.
    tauto.
Qed.

Lemma solver_qcp_strategy37_correctness : solver_qcp_strategy37.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q.
  sep_apply_l_atomic (IntArray.seg_split_to_missing_i p lo i hi l 0).
  - dump_pre_spatial. lia.
  - replace (p + i * 4) with (p + i * sizeof (INT))
      by (rewrite sizeof_int; lia).
    cancel (IntArray.missing_i p i lo hi l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hfocus.
    subst v.
    cancel.
Qed.

Lemma solver_qcp_strategy39_correctness : solver_qcp_strategy39.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst yp.
  cancel (learnt_sort_alias_remainder db activities xr xw xa).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  cancel.
Qed.

Lemma solver_qcp_strategy40_correctness : solver_qcp_strategy40.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst yp.
  cancel (learnt_sort_alias_remainder db activities xr xw xa).
  Intros_r other_size.
  Intros_r b.
  apply_sepcon_adjoint.
  Intros_p Hb.
  Intros_p Hsize.
  subst b other_size.
  cancel.
Qed.

Lemma solver_qcp_strategy41_correctness : solver_qcp_strategy41.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q.
  sep_apply_l_atomic
    (IntArray.seg_split_to_missing_i (clause_lits_addr cp) lo 0 hi l 0).
  - dump_pre_spatial.
    lia.
  - replace (clause_lits_addr cp + 0 * 4) with (clause_lits_addr cp) by lia.
    cancel (IntArray.missing_i (clause_lits_addr cp) 0 lo hi l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hfocus.
    subst v.
    cancel.
    replace (clause_lits_addr cp + 0 * sizeof ( INT )) with (clause_lits_addr cp)
      by (rewrite sizeof_int; lia).
    replace (0 - lo) with (- lo) by lia.
    cancel.
Qed.

Lemma solver_qcp_strategy61_correctness : solver_qcp_strategy61.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite !replace_Znth_Znth.
  cancel.
Qed.

Lemma solver_qcp_strategy75_correctness : solver_qcp_strategy75.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_cancel_root_frame.
  apply derivable1_wand_elim1.
Qed.

Lemma solver_qcp_strategy13_correctness : solver_qcp_strategy13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StoreDoubleAsElement.storeA, double_Znth.
  sep_apply_l_atomic
    (DoubleArray.missing_i_merge_to_seg
       p lo i hi (Znth (i - lo) l msat_fp64_zero) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma solver_qcp_strategy67_correctness : solver_qcp_strategy67.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q j.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_seg p lo i hi (Znth (i - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth. cancel.
Qed.

Lemma solver_qcp_strategy42_correctness : solver_qcp_strategy42.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q. subst i.
  assert (Hz : clause_lits_addr cp = clause_lits_addr cp + 0 * sizeof ( INT ))
    by (rewrite sizeof_int; lia).
  rewrite Hz at 2.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_seg (clause_lits_addr cp) lo 0 hi
       (Znth (0 - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth.
    cancel.
Qed.

Lemma solver_qcp_strategy58_correctness : solver_qcp_strategy58.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q j.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_seg p lo i hi (Znth (i - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth. cancel.
Qed.

Lemma solver_qcp_strategy57_correctness : solver_qcp_strategy57.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q j.
  change (p + i * 1) with (p + i * sizeof(CHAR)).
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_seg p lo i hi (Znth (i - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth. cancel.
Qed.

Lemma solver_qcp_strategy76_correctness : solver_qcp_strategy76.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q.
  change (sizeof (INT)) with 4.
  simpl.
  cancel.
  entailer!.
Qed.

Lemma solver_qcp_strategy77_correctness : solver_qcp_strategy77.
Proof.
  unfold solver_qcp_strategy77. intros. Intros. subst.
  simpl. rewrite ?Z.add_0_r. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  apply_sepcon_adjoint. (Intros; cancel).
Qed.

Lemma solver_qcp_strategy16_correctness : solver_qcp_strategy16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  Intros_r qtail cap trail levels assigns n reasons trl rsn lvl asg lim.
  apply_sepcon_adjoint.
  Intros_p Hn_nonnegative.
  Intros_p Hn_cap.
  Intros_p Hcap_max.
  Intros_p Hassigns_len.
  Intros_p Hlevels_len.
  Intros_p Hreasons_len.
  Intros_p Htrail_len.
  Intros_p Hqtail_nonnegative.
  Intros_p Hqtail_cap.
  unfold enqueue_state_at.
  Exists rsn trl.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy23_correctness : solver_qcp_strategy23.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma solver_qcp_strategy29_correctness : solver_qcp_strategy29.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  unfold removable_reason_array_hole, StorePtrAsElement.storeA.
  cancel.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_seg
       p 0 i n (Znth i words 0) words).
  - dump_pre_spatial. lia.
  - replace (i - 0) with i by lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma solver_qcp_strategy33_correctness : solver_qcp_strategy33.
Proof.
  unfold solver_qcp_strategy33, solver_clauses_rep.
  (LLM_pre_process ltac:(lia || nia || int_auto));
    cancel;
    Intros_r p w;
    apply_sepcon_adjoint;
    elim_emp;
    cancel.
Qed.

Lemma solver_qcp_strategy34_correctness : solver_qcp_strategy34.
Proof.
  unfold solver_qcp_strategy34, solver_clauses_rep.
  (LLM_pre_process ltac:(lia || nia || int_auto));
    cancel;
    Intros_r l;
    apply_sepcon_adjoint;
    elim_emp;
    cancel.
Qed.

Lemma solver_qcp_strategy43_correctness : solver_qcp_strategy43.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_scalars_root.
  sep_apply peel_vecs_trail_lim.
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_levels_slice_at.
  (Intros; cancel).
Qed.

Lemma solver_qcp_strategy44_correctness : solver_qcp_strategy44.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells.
  Intros act asg opos rsn trl tgs.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  cancel.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]); try (unfold solver_levels_slice_at; (Intros; cancel)).
Qed.

Lemma solver_qcp_strategy45_correctness : solver_qcp_strategy45.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at, solver_search_root_payload,
    solver_search_payload, solver_payload_cells,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_scalars_root.
  sep_apply peel_vecs_trail_lim.
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy46_correctness : solver_qcp_strategy46.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at, solver_search_root_payload,
    solver_search_payload, solver_payload_cells,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  cancel.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy47_correctness : solver_qcp_strategy47.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_var_arrays_rep,
    solver_trail_array_rep.
  Intros act opos rsn trl tgs.
  sep_apply peel_scalars_root.
  sep_apply peel_vecs_trail_lim.
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy48_correctness : solver_qcp_strategy48.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_search_conflict_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, stats_rep, stats_without_conflicts_rep.
  Intros act opos rsn trl tgs.
  sep_apply peel_scalars_root.
  sep_apply peel_vecs_trail_lim.
  cbv beta delta [stats_starts stats_decisions stats_propagations
    stats_inspects stats_conflicts stats_clauses stats_clauses_literals
    stats_learnts stats_learnts_literals stats_max_literals stats_tot_literals].
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy49_correctness : solver_qcp_strategy49.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_search_progress_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_var_arrays_rep,
    solver_trail_array_rep.
  Intros act opos rsn trl tgs.
  sep_apply peel_scalars_size.
  sep_apply peel_fp_progress.
  cancel.
  apply_sepcon_adjoint.
  Exists act opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy50_correctness : solver_qcp_strategy50.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_search_init_frame_at,
    solver_search_bundle_at, solver_search_payload, solver_payload_cells,
    solver_levels_slice_at, stats_rep,
    stats_without_starts_rep.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_fp_decays.
  sep_apply peel_vecs_model.
  cbv beta delta [stats_starts stats_decisions stats_propagations
    stats_inspects stats_conflicts stats_clauses stats_clauses_literals
    stats_learnts stats_learnts_literals stats_max_literals stats_tot_literals].
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy51_correctness : solver_qcp_strategy51.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_reducedb_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, db_words.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_scalars_qtail.
  sep_apply peel_vecs_learnts.
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_levels_slice_at.
  (Intros; cancel).
Qed.

Lemma solver_qcp_strategy52_correctness : solver_qcp_strategy52.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_reducedb_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_var_arrays_rep,
    solver_trail_array_rep, db_words.
  Intros act asg opos rsn trl tgs.
  sep_apply join_scalars_qtail.
  sep_apply join_vecs_learnts.
  Exists act asg opos rsn trl tgs.
  unfold solver_levels_slice_at.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy53_correctness : solver_qcp_strategy53.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_literal_stats_frame_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_trail_array_rep,
    solver_ptrs_rep, solver_var_arrays_rep,
    stats_rep, stats_analyze_frame.
  Intros act asg opos.
  cbv beta delta [stats_starts stats_decisions stats_propagations
    stats_inspects stats_conflicts stats_clauses stats_clauses_literals
    stats_learnts stats_learnts_literals stats_max_literals stats_tot_literals].
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy54_correctness : solver_qcp_strategy54.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_reasons_levels_wl_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_finish_frame_at,
    solver_search_bundle_at, solver_search_payload, solver_payload_cells,
    stats_without_simplify_totals_rep, stats_rep.
  Intros act asg opos trl tgs.
  sep_apply peel_scalars_simplify_control.
  cbv beta delta [stats_starts stats_decisions stats_propagations
    stats_inspects stats_conflicts stats_clauses stats_clauses_literals
    stats_learnts stats_learnts_literals stats_max_literals stats_tot_literals].
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy55_correctness : solver_qcp_strategy55.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_model_copy_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at,
    solver_levels_slice_at, solver_var_arrays_rep.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_scalars_size.
  sep_apply peel_vecs_model.
  Exists asg.
  (Intros; cancel).
  apply_sepcon_adjoint.
  Exists act opos rsn trl tgs.
  split_pure_spatial.
  - unfold solver_scalars_without_size_rep.
    cancel (clause_new_scalars_frame s M0).
    cancel.
  - split_pures; dump_pre_spatial; exact H.
Qed.

Lemma solver_qcp_strategy56_correctness : solver_qcp_strategy56.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (PtrArray.seg_Zlength rsn 0 n (ms_reason_words M0)).
  Intros_p Hlen.
  assert (Hn : n = ms_size M0).
  { unfold solver_shape in H. lia. }
  subst n.
  unfold solver_rep_analyze_at, solver_rep_at,
    solver_reason_levels_frame_at, solver_removable_frame_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_trail_array_rep,
    solver_ptrs_rep, solver_var_arrays_rep.
  Intros act asg opos.
  sep_apply join_scalars_size.
  sep_apply join_vecs_full.
  Exists act asg opos.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma solver_qcp_strategy62_correctness : solver_qcp_strategy62.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold setnvars_arrays_at.
  simpl Z.mul.
  (Intros; cancel).
  Intros_r y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma solver_qcp_strategy63_correctness : solver_qcp_strategy63.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_analyze_open_at.
  (Intros; cancel).
  Intros_r dl yd yf hi l lo y i.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy64_correctness : solver_qcp_strategy64.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_cancel_open_at.
  (Intros; cancel).
  Intros_r lo l hi dl y i.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy65_correctness : solver_qcp_strategy65.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold clause_remove_open_at, stats_rep.
  cbv beta delta [stats_starts stats_decisions stats_propagations
    stats_inspects stats_conflicts stats_clauses stats_clauses_literals
    stats_learnts stats_learnts_literals stats_max_literals stats_tot_literals].
  (Intros; cancel).
  Intros_r lo hi wn wmd l y i.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy66_correctness : solver_qcp_strategy66.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_propagate_open_at.
  assert (Hprop :
    &( s # "solver_t" ->ₛ "stats" .ₛ "propagations") =
    &( ((&( s # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations"))
    by (csimpl; reflexivity).
  assert (Hinspect :
    &( s # "solver_t" ->ₛ "stats" .ₛ "inspects") =
    &( ((&( s # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects"))
    by (csimpl; reflexivity).
  rewrite Hprop, Hinspect.
  (Intros; cancel).
  Intros_r l wmd wn hi lo y i.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy74_correctness : solver_qcp_strategy74.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply solver_cancel_root_peel.
  cancel. Intros_r value. apply_sepcon_adjoint. cancel.
  elim_emp. reflexivity.
Qed.

Lemma solver_qcp_strategy78_correctness : solver_qcp_strategy78.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_int_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r hi. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy79_correctness : solver_qcp_strategy79.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto). cancel.
  Intros_r cap. apply_sepcon_adjoint.
  unfold solver_int_tail, solver_array_tail.
  Intros. Exists physical. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.

Lemma solver_qcp_strategy80_correctness : solver_qcp_strategy80.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_ptr_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r hi. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy81_correctness : solver_qcp_strategy81.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto). cancel.
  Intros_r cap. apply_sepcon_adjoint.
  unfold solver_ptr_tail, solver_array_tail.
  Intros. Exists physical. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.

Lemma solver_qcp_strategy82_correctness : solver_qcp_strategy82.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_char_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r hi. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy83_correctness : solver_qcp_strategy83.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto). cancel.
  Intros_r cap. apply_sepcon_adjoint.
  unfold solver_char_tail, solver_array_tail.
  Intros. Exists physical. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.

Lemma solver_qcp_strategy84_correctness : solver_qcp_strategy84.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_double_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r hi. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy85_correctness : solver_qcp_strategy85.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto). cancel.
  Intros_r cap. apply_sepcon_adjoint.
  unfold solver_double_tail, solver_array_tail.
  Intros. Exists physical. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.

Lemma solver_qcp_strategy86_correctness : solver_qcp_strategy86.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_wlists_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r hi. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy87_correctness : solver_qcp_strategy87.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto). cancel.
  Intros_r cap. apply_sepcon_adjoint.
  unfold solver_wlists_tail, solver_array_tail.
  Intros. Exists physical. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.

Lemma solver_qcp_strategy88_correctness : solver_qcp_strategy88.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_int_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r value. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy89_correctness : solver_qcp_strategy89.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_ptr_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r value. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy90_correctness : solver_qcp_strategy90.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold solver_char_tail, solver_array_tail.
  Intros physical. Exists physical.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
  Intros_r value. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy92_correctness : solver_qcp_strategy92.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold clause_new_pending_at_root.
  cbn zeta.
  rewrite sel_vec_prob, sel_db_prob.
  unfold solver_selected_is_learnt, msat_false.
  simpl.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (tauto)] ..]).
  Intros_r target_l. apply_sepcon_adjoint. elim_emp. cancel.
Qed.

Lemma solver_qcp_strategy14_correctness : solver_qcp_strategy14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StoreDoubleAsElement.storeA.
  sep_apply_l_atomic
    (DoubleArray.missing_i_merge_to_seg p lo i hi v l).
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma solver_qcp_strategy59_correctness : solver_qcp_strategy59.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst q j.
  change (p + i * 1) with (p + i * sizeof(CHAR)).
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_seg p lo i hi v l).
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma solver_qcp_strategy38_correctness : solver_qcp_strategy38.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  subst q.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_seg p lo i hi v l).
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma solver_qcp_strategy93_correctness : solver_qcp_strategy93.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold wlists_rep.
  Intros.
  split_pure_spatial.
  - cancel.
    Intros_r l p.
    apply_sepcon_adjoint.
    Intros.
    cancel.
  - dump_pre_spatial.
    lia.
Qed.

Lemma solver_qcp_strategy94_correctness : solver_qcp_strategy94.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hw.
  unfold wlists_rep.
  Intros.
  split_pure_spatial.
  - cancel.
    Intros_r l p.
    apply_sepcon_adjoint.
    Intros.
    cancel.
  - split_pures; dump_pre_spatial; solve [tauto | lia].
Qed.
