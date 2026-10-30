From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P029_690D1_the_wall_easy_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P029_690D1_the_wall_easy_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P029_690D1_the_wall_easy_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WallColumnsAfterRows.
  split.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    reflexivity.
  - intros col Hcol.
    unfold OccupancyValue.
    right.
    split.
    + unfold repeat_Z.
      rewrite Znth_repeat.
      reflexivity.
    + unfold NonemptyWallColumnBefore.
      intros [row [[Hrow0 Hrowlt] Hcell]].
      lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply pre_from_quantified_rows__row_boundaries.
  - lia.
  - lia.
  - exact PreH5.
  - exact PreH6.
  - intros row col Hbounds.
    apply PreH7.
    exact Hbounds.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply wall_columns_during_row_zero__row_boundaries.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Array2.replace_mixed_row_Znth.
  rewrite (Znth_indep grid_mem i __default__List__App_option_Z nil) by lia.
  unfold Array2.mixed_val.
  rewrite PreH5.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Array2.replace_mixed_row_Znth.
  rewrite (Znth_indep grid_mem i __default__List__App_option_Z nil) by lia.
  unfold Array2.mixed_val.
  rewrite PreH5.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Array2.replace_mixed_row_Znth.
  rewrite (Znth_indep grid_mem i __default__List__App_option_Z nil) by lia.
  unfold Array2.mixed_def.
  dump_pre_spatial.
  exists (Znth j (Znth i grid_data nil) 0).
  exact PreH5.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Array2.replace_mixed_row_Znth.
  rewrite (Znth_indep grid_mem i __default__List__App_option_Z nil) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply wall_columns_mark_current__cell_updates; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(exact PreH8).
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_spatial : solver_entail_wit_4_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Array2.replace_mixed_row.
  rewrite (replace_Znth_same_inbounds__cell_updates
             _ i grid_mem nil) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply wall_columns_skip_current__cell_updates; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(exact PreH8).
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_spatial : solver_entail_wit_4_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  fold (CharArray.mixedstoreA
          (grid_pre + i * (sizeof (CHAR) * 105)) j (Some cell)).
  sep_apply_l_atomic
    (CharArray.mixed_missing_i_merge_to_mixed_full
       (grid_pre + i * (sizeof (CHAR) * 105)) j 105
       (Some cell) (Znth i grid_mem nil)).
  - dump_pre_spatial. lia.
  - rewrite <- PreH15.
    rewrite replace_Znth_Znth by lia.
    replace (grid_pre + i * (sizeof (CHAR) * 105))
      with (CharArray2.row_addr grid_pre 105 i) by
        (unfold CharArray2.row_addr; nia).
    unfold CharArray.mixed_full, CharArray.mixedstoreA.
    fold (CharArray2.ElemArray.mixed_full
            (CharArray2.row_addr grid_pre 105 i) 105
            (Znth i grid_mem nil)).
    pose proof
      (CharArray2.mixed_missing_i_merge_to_mixed_full
         grid_pre i r_pre 105 grid_mem (Znth i grid_mem nil)
         ltac:(lia)) as Hmerge_outer.
    unfold CharArray2.ElemArray.mixed_full,
      CharArray2.ElemArray.mixedstoreA in Hmerge_outer.
    sep_apply_l_atomic Hmerge_outer.
    rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_spatial.
  - Goal_apply
      (dump_spatial_left
         (((grid_pre + i * (sizeof (CHAR) * 105) + j * sizeof (CHAR))
              # Char |-> cell) **
          (CharArray.mixed_missing_i
             (grid_pre + i * (sizeof (CHAR) * 105)) j 0 105
             (Znth i grid_mem nil) **
           CharArray2.mixed_missing_i
             grid_pre i 0 r_pre 105 grid_mem))
         _
         (wall_columns_skip_current__cell_updates
            grid_data i j occupied_data_2
            ltac:(lia)
            ltac:(intro Hcell; apply PreH1; rewrite PreH14; exact Hcell)
            PreH13)).
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = c_pre) by lia.
  subst j.
  eapply wall_columns_during_row_complete__row_boundaries.
  - exact PreH6.
  - lia.
  - exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(apply segment_count_prefix_zero__row_boundaries).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = r_pre) by lia.
  subst i.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (pre_first_row_length__segment_scan _ _ _ PreH9) as Hfirstlen.
  unfold Pre in PreH9.
  destruct PreH9 as [[Hrlo Hrhi] [[Hclo Hchi] [Hgrid Hrows]]].
  destruct PreH16 as [_ Hcolumns].
  pose proof (Hcolumns j ltac:(lia)) as Hjvalue.
  pose proof
    (proj2 (occupancy_value_reflects_presence__segment_scan _ _ Hjvalue)
       PreH3) as Hjpresent.
  pose proof (Hcolumns (j - 1) ltac:(lia)) as Hprevvalue.
  pose proof
    (proj1
       (proj1
          (occupancy_value_reflects_presence__segment_scan _ _ Hprevvalue))
       PreH1) as Hprevabsent.
  assert (Hjnonempty : NonemptyWallColumn grid_data j).
  { destruct Hjpresent as [row [Hrow Hcell]].
    exists row. split; [rewrite Hgrid; exact Hrow | exact Hcell]. }
  assert (Hprevempty : ~ NonemptyWallColumn grid_data (j - 1)).
  { intros [row [Hrow Hcell]].
    apply Hprevabsent. exists row.
    split; [rewrite <- Hgrid; exact Hrow | exact Hcell]. }
  apply segment_count_prefix_add_start__segment_scan.
  - exact PreH12.
  - unfold StartsWallSegment.
    split; [rewrite Hfirstlen; lia |].
    split; [exact Hjnonempty |].
    right. exact Hprevempty.
  - exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst j.
  assert (segments = 0) by lia.
  subst segments.
  pose proof
    (pre_first_row_length__segment_scan _ _ _ PreH8) as Hfirstlen.
  unfold Pre in PreH8.
  destruct PreH8 as [[Hrlo Hrhi] [[Hclo Hchi] [Hgrid Hrows]]].
  destruct PreH15 as [_ Hcolumns].
  pose proof (Hcolumns 0 ltac:(lia)) as Hvalue.
  pose proof
    (proj2 (occupancy_value_reflects_presence__segment_scan _ _ Hvalue)
       PreH2) as Hpresent.
  assert (Hnonempty : NonemptyWallColumn grid_data 0).
  { destruct Hpresent as [row [Hrow Hcell]].
    exists row. split; [rewrite Hgrid; exact Hrow | exact Hcell]. }
  apply segment_count_prefix_add_start__segment_scan.
  - lia.
  - unfold StartsWallSegment.
    split; [rewrite Hfirstlen; lia |].
    split; [exact Hnonempty |].
    left. reflexivity.
  - exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_3_split_goal_1 : solver_entail_wit_8_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH7.
  destruct PreH7 as [[Hrlo Hrhi] [[Hclo Hchi] [Hgrid Hrows]]].
  destruct PreH14 as [_ Hcolumns].
  pose proof (Hcolumns j ltac:(lia)) as Hvalue.
  pose proof
    (proj1
       (proj1
          (occupancy_value_reflects_presence__segment_scan _ _ Hvalue))
       PreH1) as Habsent.
  assert (Hempty : ~ NonemptyWallColumn grid_data j).
  { intros [row [Hrow Hcell]].
    apply Habsent. exists row.
    split; [rewrite <- Hgrid; exact Hrow | exact Hcell]. }
  apply segment_count_prefix_skip_nonstart__segment_scan.
  - exact PreH10.
  - intros Hstart.
    unfold StartsWallSegment in Hstart.
    destruct Hstart as [_ [Hnonempty _]].
    exact (Hempty Hnonempty).
  - exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_4_split_goal_1 : solver_entail_wit_8_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Pre in PreH9.
  destruct PreH9 as [[Hrlo Hrhi] [[Hclo Hchi] [Hgrid Hrows]]].
  destruct PreH16 as [_ Hcolumns].
  pose proof (Hcolumns j ltac:(lia)) as Hjvalue.
  pose proof
    (proj2 (occupancy_value_reflects_presence__segment_scan _ _ Hjvalue)
       PreH3) as Hjpresent.
  pose proof (Hcolumns (j - 1) ltac:(lia)) as Hprevvalue.
  pose proof
    (proj2 (occupancy_value_reflects_presence__segment_scan _ _ Hprevvalue)
       PreH1) as Hprevpresent.
  assert (Hjnonempty : NonemptyWallColumn grid_data j).
  { destruct Hjpresent as [row [Hrow Hcell]].
    exists row. split; [rewrite Hgrid; exact Hrow | exact Hcell]. }
  assert (Hprevnonempty : NonemptyWallColumn grid_data (j - 1)).
  { destruct Hprevpresent as [row [Hrow Hcell]].
    exists row. split; [rewrite Hgrid; exact Hrow | exact Hcell]. }
  apply segment_count_prefix_skip_nonstart__segment_scan.
  - exact PreH12.
  - intros Hstart.
    unfold StartsWallSegment in Hstart.
    destruct Hstart as [_ [Hcurrent [Hjzero | Hprevempty]]].
    + contradiction.
    + exact (Hprevempty Hprevnonempty).
  - exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_4_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = c_pre) by lia.
  subst j.
  apply segment_count_prefix_full_to_spec__final_result with (r := r_pre).
  - exact PreH6.
  - exact PreH2.
  - exact PreH14.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH16 i ltac:(lia)) as [[_ Hcells] _].
  specialize (Hcells j ltac:(lia)).
  dump_pre_spatial.
  exact Hcells.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (CharArray2.mixed_full_split_to_mixed_missing_i
       grid_pre i r_pre 105 grid_mem ltac:(lia)).
  unfold CharArray2.row_addr.
  replace (grid_pre + i * 105 * sizeof (CHAR)) with
    (grid_pre + i * (105 * sizeof (CHAR))) by ring.
  unfold CharArray2.ElemArray.mixed_full, CharArray.mixed_full.
  unfold CharArray2.ElemArray.mixedstoreA, CharArray.mixedstoreA.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed.
