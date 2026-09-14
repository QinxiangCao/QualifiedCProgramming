Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_strategy_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma solver_qcp_strategy12_correctness : solver_qcp_strategy12.
Proof.
  pre_process_default.
  prop_apply (DoubleArray.seg_Zlength p lo hi l).
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

Lemma solver_qcp_strategy13_correctness : solver_qcp_strategy13.
Proof.
  pre_process_default.
  unfold StoreDoubleAsElement.storeA, double_Znth.
  sep_apply_l_atomic
    (DoubleArray.missing_i_merge_to_seg
       p lo i hi (Znth (i - lo) l msat_fp64_zero) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth by lia.
    entailer_with ltac:(lia).
Qed.

Lemma solver_qcp_strategy2_correctness : solver_qcp_strategy2.
Proof.
  pre_process_default.
  unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Intros p.
  Exists p.
  entailer_with ltac:(lia).
  Intros_r target_p y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma solver_qcp_strategy3_correctness : solver_qcp_strategy3.
Proof.
  pre_process_default.
  cancel.
  Intros_r cap l p.
  apply_sepcon_adjoint.
  Intros_p Hlen_nonnegative.
  Intros_p Hlen_cap.
  Intros_p Hcap_positive.
  Intros_p Hcap_max.
  unfold veci_rep, veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  Exists p.
  entailer_with ltac:(lia).
Qed.

Lemma solver_qcp_strategy4_correctness : solver_qcp_strategy4.
Proof.
  pre_process_default.
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  entailer_with ltac:(lia).
  Intros_r y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma solver_qcp_strategy5_correctness : solver_qcp_strategy5.
Proof.
  pre_process_default.
  cancel.
  Intros_r cap l p.
  apply_sepcon_adjoint.
  Intros_p Hlen_nonnegative.
  Intros_p Hlen_cap.
  Intros_p Hcap_positive.
  Intros_p Hcap_max.
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  entailer_with ltac:(lia).
Qed.

Lemma solver_qcp_strategy6_correctness : solver_qcp_strategy6.
Proof.
  pre_process_default.
  unfold vecp_rep, vecp_rep_at, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  Intros p.
  Exists p.
  entailer_with ltac:(lia).
  Intros_r target_p y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma solver_qcp_strategy7_correctness : solver_qcp_strategy7.
Proof.
  pre_process_default.
  cancel.
  Intros_r cap l p.
  apply_sepcon_adjoint.
  Intros_p Hlen_nonnegative.
  Intros_p Hlen_cap.
  Intros_p Hcap_positive.
  Intros_p Hcap_max.
  unfold vecp_rep, vecp_rep_at, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  Exists p.
  entailer_with ltac:(lia).
Qed.

Lemma solver_qcp_strategy8_correctness : solver_qcp_strategy8.
Proof.
  pre_process_default.
  unfold vecp_rep_at, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  entailer_with ltac:(lia).
  Intros_r y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma solver_qcp_strategy9_correctness : solver_qcp_strategy9.
Proof.
  pre_process_default.
  cancel.
  Intros_r cap l p.
  apply_sepcon_adjoint.
  Intros_p Hlen_nonnegative.
  Intros_p Hlen_cap.
  Intros_p Hcap_positive.
  Intros_p Hcap_max.
  unfold vecp_rep_at, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  entailer_with ltac:(lia).
Qed.

Lemma solver_qcp_strategy14_correctness : solver_qcp_strategy14.
Proof.
  pre_process_default.
  unfold StoreDoubleAsElement.storeA.
  sep_apply_l_atomic
    (DoubleArray.missing_i_merge_to_seg p lo i hi v l).
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma solver_qcp_strategy16_correctness : solver_qcp_strategy16.
Proof.
  pre_process_default.
  cancel.
  Intros_r qtail cap trail levels assigns n reasons trl rsn lvl asg
           lim_cap lim.
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
  entailer_with ltac:(lia).
Qed.


Lemma solver_qcp_strategy23_correctness : solver_qcp_strategy23.
Proof.
  pre_process_default.
Qed.


Lemma solver_qcp_strategy29_correctness : solver_qcp_strategy29.
Proof.
  pre_process_default.
  subst j.
  unfold removable_reason_array_hole, StorePtrAsElement.storeA.
  (* Fold the unfolded Arch alias back to the derived ptr_size_Z that
     PtrArray's lemmas are stated with, so the sep_apply_l_atomic below
     matches syntactically; stays arch-agnostic. *)
  fold_arch.
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
  unfold solver_qcp_strategy33, solver_clause_count_cell, vecp_size_addr.
  pre_process_default;
    cancel;
    Intros_r value;
    apply_sepcon_adjoint;
    elim_emp;
    cancel.
Qed.

Lemma solver_qcp_strategy34_correctness : solver_qcp_strategy34.
Proof.
  unfold solver_qcp_strategy34, solver_clause_count_cell, vecp_size_addr.
  pre_process_default;
    cancel;
    Intros_r n;
    apply_sepcon_adjoint;
    elim_emp;
    cancel.
Qed.

Lemma solver_qcp_strategy35_correctness : solver_qcp_strategy35.
Proof.
  pre_process_default.
  subst closed_v required_cut.
  unfold vecp_rep, vecp_rep_at, vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  Exists p.
  entailer_with ltac:(lia).
Qed.

(* Focus the base cell of an integer segment for an unindexed write.  Modelled
   on int_array_strategy7_correctness; the only difference is that the target
   address is the segment base itself rather than `p + i * sizeof(INT)`. *)
Lemma solver_qcp_strategy36_correctness : solver_qcp_strategy36.
Proof.
  pre_process_default.
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
    entailer_with ltac:(lia).
Qed.

(* Match an explicitly recorded alias before focusing the segment base. *)
Lemma solver_qcp_strategy69_correctness : solver_qcp_strategy69.
Proof.
  pre_process_default.
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
      entailer_with ltac:(lia).
  - dump_pre_spatial.
    tauto.
Qed.

(* Modelled on int_array_strategy7_correctness.  Two deltas from that model:
   the extra `q == p` check means `pre_process_default` already binds H1, so the
   focused-value equation needs a fresh name; and the store address is spelled
   with `q`, which the same check lets us rewrite to the segment base. *)
Lemma solver_qcp_strategy37_correctness : solver_qcp_strategy37.
Proof.
  pre_process_default.
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

(* Modelled on int_array_strategy12_correctness, plus the `q == p` and `i == j`
   checks that let the native store address be renamed to the segment base and
   the logically focused index. *)
Lemma solver_qcp_strategy38_correctness : solver_qcp_strategy38.
Proof.
  pre_process_default.
  subst j.
  subst q.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_seg p lo i hi v l).
  - dump_pre_spatial. lia.
  - cancel.
Qed.


(* Rules 39/40 bridge a clause object that is spelled `xp` in the heap to the `yp` the
   caller asks for, under the `xp = yp` alias check.  QCP has no congruence closure, so
   nothing else relates `clause_hdr_addr xp` to `clause_hdr_addr yp`; the alias is real
   (sortrnd compares the pivot element against itself), so it cannot be specified away.
   Both rules keep `learnt_sort_alias_remainder` as a non-erased trigger, which is what
   confines them to the single [learnt_sort_alias_remainder] arm.

   The obligation is therefore trivial: rewrite along the alias, then hand the very cell
   we started with to the universally-quantified consumer once `v = w` fixes its value. *)
Lemma solver_qcp_strategy39_correctness : solver_qcp_strategy39.
Proof.
  pre_process_default.
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
  pre_process_default.
  subst yp.
  cancel (learnt_sort_alias_remainder db activities xr xw xa).
  Intros_r b.
  apply_sepcon_adjoint.
  Intros_p Hb.
  subst b.
  cancel.
Qed.

(* Rules 41/42 are rules 36/38 restated for a BARE base address that is only
   provably -- not syntactically -- the segment base.  `*clause_begin(c)` reads
   through the pointer clause_begin returned, and clause_begin's Ensure only
   states `__return = clause_lits_addr c`; it does not carry the heap, so the
   literal array stays keyed on `clause_lits_addr c`.  Both proofs are the
   corresponding pre-existing proof with `subst q` (and, for 42, `subst i`) in
   front: once the alias is substituted the obligation is literally rule 36's /
   rule 38's, so neither rule widens the trusted base. *)
Lemma solver_qcp_strategy41_correctness : solver_qcp_strategy41.
Proof.
  pre_process_default.
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
    entailer_with ltac:(lia).
Qed.

Lemma solver_qcp_strategy42_correctness : solver_qcp_strategy42.
Proof.
  pre_process_default.
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

(* Expose root control while preserving the watcher-table address. *)
Lemma solver_qcp_strategy43_correctness : solver_qcp_strategy43.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
  unfold solver_levels_slice_at.
  entailer_with ltac:(lia).
Qed.

(* Rejoin root control with the same watcher-table address. *)
Lemma solver_qcp_strategy44_correctness : solver_qcp_strategy44.
Proof.
  pre_process_default.
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells.
  Intros act asg opos rsn trl tgs.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  cancel.
  Exists act asg opos rsn trl tgs.
  entailer_with ltac:(lia); try (unfold solver_levels_slice_at; entailer_with ltac:(lia)).
Qed.

(* Expose root control and the level slice, retaining the watcher table. *)
Lemma solver_qcp_strategy45_correctness : solver_qcp_strategy45.
Proof.
  pre_process_default.
  unfold solver_rep_levels_wl_at, solver_search_root_payload,
    solver_search_payload, solver_payload_cells,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_scalars_root.
  sep_apply peel_vecs_trail_lim.
  cancel.
  apply_sepcon_adjoint.
  Exists act asg opos rsn trl tgs.
  entailer_with ltac:(lia).
Qed.

(* Rejoin root control and levels with the same watcher table. *)
Lemma solver_qcp_strategy46_correctness : solver_qcp_strategy46.
Proof.
  pre_process_default.
  unfold solver_rep_levels_wl_at, solver_search_root_payload,
    solver_search_payload, solver_payload_cells,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  sep_apply join_scalars_root.
  sep_apply join_vecs_trail_lim.
  cancel.
  Exists act asg opos rsn trl tgs.
  entailer_with ltac:(lia).
Qed.

(* Expose root control from cached assignment and level pointers. *)
Lemma solver_qcp_strategy47_correctness : solver_qcp_strategy47.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose conflict bookkeeping while retaining the watcher-table address. *)
Lemma solver_qcp_strategy48_correctness : solver_qcp_strategy48.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose progress inputs while preserving all cached backing pointers. *)
Lemma solver_qcp_strategy49_correctness : solver_qcp_strategy49.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose search initialization fields and retain the watcher-table address. *)
Lemma solver_qcp_strategy50_correctness : solver_qcp_strategy50.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose the learnt vector and queue tail, retaining the watcher table. *)
Lemma solver_qcp_strategy51_correctness : solver_qcp_strategy51.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
  unfold solver_levels_slice_at.
  entailer_with ltac:(lia).
Qed.

(* Rejoin the learnt vector and queue tail with the same watcher table. *)
Lemma solver_qcp_strategy52_correctness : solver_qcp_strategy52.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose literal counters while preserving the analyzer backing pointers. *)
Lemma solver_qcp_strategy53_correctness : solver_qcp_strategy53.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose simplify bookkeeping and retain the cached watcher-table address. *)
Lemma solver_qcp_strategy54_correctness : solver_qcp_strategy54.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Expose the assignment array and model vector, retaining the watcher table. *)
Lemma solver_qcp_strategy55_correctness : solver_qcp_strategy55.
Proof.
  pre_process_default.
  unfold solver_rep_levels_wl_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_model_copy_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at,
    solver_levels_slice_at, solver_var_arrays_rep.
  Intros act asg opos rsn trl tgs.
  sep_apply peel_scalars_size.
  sep_apply peel_vecs_model.
  Exists asg.
  entailer_with ltac:(lia).
  apply_sepcon_adjoint.
  Exists act opos rsn trl tgs.
  entailer_with ltac:(int_auto).
Qed.

(* Rejoin reason and level slices with the analyzer watcher-table address. *)
Lemma solver_qcp_strategy56_correctness : solver_qcp_strategy56.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
Qed.

(* Rules 57-61 bridge the `pointer_offset(p, i, T)` address form V2.1.0 emits,
   which the built-in refolds do not match -- they recognize the arithmetic
   form `p + i * sizeof(T)`.  Each carries a StrategyCheck correctness
   obligation, discharged here. *)

Lemma solver_qcp_strategy57_correctness : solver_qcp_strategy57.
Proof.
  pre_process_default.
  subst q j.
  (* the obligation reduces sizeof(CHAR) to the literal 1, while
     StoreCharAsElement.storeA keeps it symbolic; re-spell so the refold matches *)
  change (p + i * 1) with (p + i * sizeof(CHAR)).
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_seg p lo i hi (Znth (i - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth. cancel.
Qed.

Lemma solver_qcp_strategy58_correctness : solver_qcp_strategy58.
Proof.
  pre_process_default.
  subst q j.
  (* The obligation carries Arch32.ptr_size_Z, the library lemma the
     arch-parametric ptr_size_Z; fold the Arch alias back to the derived name so
     the two spellings match syntactically. *)
  fold_arch.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_seg p lo i hi (Znth (i - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth. cancel.
Qed.

Lemma solver_qcp_strategy59_correctness : solver_qcp_strategy59.
Proof.
  pre_process_default.
  subst q j.
  change (p + i * 1) with (p + i * sizeof(CHAR)).
  sep_apply_l_atomic
    (CharArray.missing_i_merge_to_seg p lo i hi v l).
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma solver_qcp_strategy60_correctness : solver_qcp_strategy60.
Proof.
  pre_process_default.
  subst q.
  cancel.
Qed.

Lemma solver_qcp_strategy61_correctness : solver_qcp_strategy61.
Proof.
  pre_process_default.
  rewrite !replace_Znth_Znth.
  cancel.
Qed.

(* Rule 62, the left-unfold of the setnvars array bundle on any hidden-field
   demand.  Same shape as strategy4 -- there is no existential to introduce --
   with the bundle unfolded and [Z.mul] simplified before the closer. *)
Lemma solver_qcp_strategy62_correctness : solver_qcp_strategy62.
Proof.
  pre_process_default.
  unfold setnvars_arrays_at.
  simpl Z.mul.
  entailer_with ltac:(lia).
  Intros_r y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

(* Demand-driven unfolding of the four working views. Introduce exactly
   the explicit demand binders before converting the wand to an entailment.
   Rule66 reconciles nested field addresses only on isolated equalities. *)
Lemma solver_qcp_strategy63_correctness : solver_qcp_strategy63.
Proof.
  pre_process_default.
  unfold solver_analyze_open_at.
  entailer_with ltac:(lia).
  Intros_r floats dbl flt capacity hi contents lo value index.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy64_correctness : solver_qcp_strategy64.
Proof.
  pre_process_default.
  unfold solver_cancel_open_at.
  entailer_with ltac:(lia).
  Intros_r lo contents hi floats capacity value index.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy65_correctness : solver_qcp_strategy65.
Proof.
  pre_process_default.
  unfold clause_remove_open_at, stats_rep.
  cbv beta delta [stats_starts stats_decisions stats_propagations
    stats_inspects stats_conflicts stats_clauses stats_clauses_literals
    stats_learnts stats_learnts_literals stats_max_literals stats_tot_literals].
  entailer_with ltac:(lia).
  Intros_r lo hi count wcaps watches contents value index.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy66_correctness : solver_qcp_strategy66.
Proof.
  pre_process_default.
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
  entailer_with ltac:(lia).
  Intros_r contents capacity watches wcaps count hi lo value index.
  apply_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

Lemma solver_qcp_strategy67_correctness : solver_qcp_strategy67.
Proof.
  pre_process_default.
  subst q j.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_seg p lo i hi (Znth (i - lo) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth. cancel.
Qed.

Lemma solver_qcp_strategy68_correctness : solver_qcp_strategy68.
Proof.
  LLM_pre_process ltac:(lia).
  subst q lo2 hi2.
  cancel.
Qed.
