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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P085_498D_traffic_jams_in_the_land_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P085_498D_traffic_jams_in_the_land_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P085_498D_traffic_jams_in_the_land_lib.
Local Open Scope sac.

Lemma proof_of_pull_safety_wit_5_split_goal_1 : pull_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60))).
  { apply row_is_value__pull_frame with (ps := NodeSlice arr (mid + 1) hi).
    - exact PreH16.
    - lia.
    - exact PreH18.
    - lia. }
  rewrite (Array2.mixed_cell_val _ _ _ Hcell).
  pose proof (delta_bounds__pull_frame (NodeSlice arr (mid + 1) hi)
                ((r + left) % 60)) as Hb.
  rewrite (node_slice_facts__pull_frame arr (mid + 1) hi
             ltac:(lia) ltac:(lia) ltac:(lia)) in Hb.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_5_split_goal_2 : pull_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60))).
  { apply row_is_value__pull_frame with (ps := NodeSlice arr (mid + 1) hi).
    - exact PreH16.
    - lia.
    - exact PreH18.
    - lia. }
  rewrite (Array2.mixed_cell_val _ _ _ Hcell).
  pose proof (delta_bounds__pull_frame (NodeSlice arr (mid + 1) hi)
                ((r + left) % 60)) as Hb.
  rewrite (node_slice_facts__pull_frame arr (mid + 1) hi
             ltac:(lia) ltac:(lia) ltac:(lia)) in Hb.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_5 : pull_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_pull_entail_wit_1_split_goal_1 : pull_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowsAgreeExcept. intros u Hu. reflexivity.
Qed.

Lemma proof_of_pull_entail_wit_1_split_goal_2 : pull_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowPrefixIs. intros r0 Hr0. exfalso. lia.
Qed.

Lemma proof_of_pull_entail_wit_1 : pull_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_pull_entail_wit_2 : pull_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell : Znth r (Znth (2 * v_pre) cellsr __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr lo mid) r)).
  { apply row_is_value__pull_frame with (ps := NodeSlice arr lo mid).
    - exact PreH12.
    - lia.
    - exact PreH13.
    - lia. }
  assert (Hval : Array2.mixed_val
                   (Znth (2 * v_pre) cellsr __default__List__App_option_Z) r
                 = delta (NodeSlice arr lo mid) r)
    by (apply Array2.mixed_cell_val; exact Hcell).
  pose proof (delta_bounds__pull_frame (NodeSlice arr lo mid) r) as Hb.
  rewrite (node_slice_facts__pull_frame arr lo mid
             ltac:(lia) ltac:(lia) ltac:(lia)) in Hb.
  Exists cellsr.
  split_pure_spatial.
  - fold (IntArray.mixedstoreA
            ( &( "seg" ) + 2 * v_pre * (sizeof(INT) * 60)) r
            (Some (Array2.mixed_val
                     (Znth (2 * v_pre) cellsr __default__List__App_option_Z) r))).
    sep_apply_l_atomic (IntArray.mixed_missing_i_merge_to_mixed_full
      ( &( "seg" ) + 2 * v_pre * (sizeof(INT) * 60)) r 60
      (Some (Array2.mixed_val
               (Znth (2 * v_pre) cellsr __default__List__App_option_Z) r))
      (Znth (2 * v_pre) cellsr __default__List__App_option_Z) ltac:(lia)).
    rewrite <- (Array2.mixed_def_val
                  (Znth (2 * v_pre) cellsr __default__List__App_option_Z) r
                  (ex_intro _ _ Hcell)).
    rewrite replace_Znth_Znth.
    assert (Hrow_addr : &( "seg" ) + 2 * v_pre * (sizeof(INT) * 60)
                      = IntArray2.row_addr ( &( "seg" ) ) 60 (2 * v_pre))
      by (unfold IntArray2.row_addr; ring).
    rewrite Hrow_addr.
    unfold IntArray.mixed_full, IntArray.mixedstoreA.
    fold (IntArray2.ElemArray.mixed_full
            (IntArray2.row_addr ( &( "seg" ) ) 60 (2 * v_pre)) 60
            (Znth (2 * v_pre) cellsr __default__List__App_option_Z)).
    pose proof (IntArray2.mixed_missing_i_merge_to_mixed_full
      ( &( "seg" ) ) (2 * v_pre) 400020 60 cellsr
      (Znth (2 * v_pre) cellsr __default__List__App_option_Z) ltac:(lia)) as Hmerge.
    unfold IntArray2.ElemArray.mixed_full,
      IntArray2.ElemArray.mixedstoreA in Hmerge.
    sep_apply_l_atomic Hmerge.
    rewrite replace_Znth_Znth.
    cancel.
  - assert (Hnn : 0 <= r + Array2.mixed_val
                    (Znth (2 * v_pre) cellsr __default__List__App_option_Z) r).
    { rewrite Hval. lia. }
    pose proof (Z.rem_bound_pos
      (r + Array2.mixed_val
             (Znth (2 * v_pre) cellsr __default__List__App_option_Z) r)
      60 Hnn ltac:(lia)) as Hrem.
    split_pures; dump_pre_spatial; try assumption; try lia;
      rewrite Hval; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_split_goal_1 : pull_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength cellsr_2 = 400020) by (destruct PreH16 as [H _]; exact H).
  assert (Hd : Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z
             = Znth (2 * v_pre + 1) cellsr_2 (@nil (option Z)))
    by (apply Znth_indep; lia).
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60)))
    by (rewrite Hd; apply PreH18; lia).
  rewrite <- (Array2.mixed_def_val
                (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z)
                ((r + left) % 60) (ex_intro _ _ Hcell)).
  rewrite Array2.replace_mixed_row_roundtrip.
  unfold Array2.replace_mixed_row.
  unfold RowsAgreeExcept in *.
  intros u Hu.
  rewrite Znth_replace_Znth_diff__pull_merge by lia.
  apply PreH20. exact Hu.
Qed.

Lemma proof_of_pull_entail_wit_3_split_goal_2 : pull_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength cellsr_2 = 400020) by (destruct PreH16 as [H _]; exact H).
  assert (Hd : Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z
             = Znth (2 * v_pre + 1) cellsr_2 (@nil (option Z)))
    by (apply Znth_indep; lia).
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60)))
    by (rewrite Hd; apply PreH18; lia).
  assert (Hrowlen : Zlength (Znth v_pre cellsr_2 (@nil (option Z))) = 60).
  { destruct PreH16 as [_ H]. apply H. lia. }
  rewrite <- (Array2.mixed_def_val
                (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z)
                ((r + left) % 60) (ex_intro _ _ Hcell)).
  rewrite Array2.replace_mixed_row_roundtrip.
  unfold Array2.replace_mixed_row.
  assert (Hval : Array2.mixed_val
                   (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z)
                   ((r + left) % 60)
                 = delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60))
    by (apply Array2.mixed_cell_val; exact Hcell).
  rewrite Hval.
  assert (Hrem : (r + left) % 60 = (r + left) mod 60)
    by (apply Zquot.Zrem_Zmod_pos; lia).
  rewrite Hrem.
  assert (Hdel : left + delta (NodeSlice arr (mid + 1) hi) ((r + left) mod 60)
               = delta (NodeSlice arr lo hi) r).
  { rewrite (node_slice_split__pull_merge arr lo mid hi) by lia.
    rewrite delta_merge__pull_merge.
    rewrite <- PreH10.
    rewrite <- (delta_mod60__pull_merge (NodeSlice arr (mid + 1) hi) (r + left)).
    - reflexivity.
    - apply periods_ok_sublist__pull_merge. exact PreH15. }
  rewrite Hdel.
  rewrite (Znth_indep cellsr_2 v_pre __default__List__App_option_Z (@nil (option Z))) by lia.
  apply row_prefix_step__pull_merge.
  - lia.
  - rewrite Hrowlen. lia.
  - exact PreH19.
Qed.

Lemma proof_of_pull_entail_wit_3_split_goal_3 : pull_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength cellsr_2 = 400020) by (destruct PreH16 as [H _]; exact H).
  assert (Hd : Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z
             = Znth (2 * v_pre + 1) cellsr_2 (@nil (option Z)))
    by (apply Znth_indep; lia).
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60)))
    by (rewrite Hd; apply PreH18; lia).
  rewrite <- (Array2.mixed_def_val
                (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z)
                ((r + left) % 60) (ex_intro _ _ Hcell)).
  rewrite Array2.replace_mixed_row_roundtrip.
  unfold Array2.replace_mixed_row.
  unfold RowIs in *.
  intros r0 Hr0.
  rewrite Znth_replace_Znth_diff__pull_merge by lia.
  apply PreH18. exact Hr0.
Qed.

Lemma proof_of_pull_entail_wit_3_split_goal_4 : pull_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength cellsr_2 = 400020) by (destruct PreH16 as [H _]; exact H).
  assert (Hd : Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z
             = Znth (2 * v_pre + 1) cellsr_2 (@nil (option Z)))
    by (apply Znth_indep; lia).
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60)))
    by (rewrite Hd; apply PreH18; lia).
  rewrite <- (Array2.mixed_def_val
                (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z)
                ((r + left) % 60) (ex_intro _ _ Hcell)).
  rewrite Array2.replace_mixed_row_roundtrip.
  unfold Array2.replace_mixed_row.
  unfold RowIs in *.
  intros r0 Hr0.
  rewrite Znth_replace_Znth_diff__pull_merge by lia.
  apply PreH17. exact Hr0.
Qed.

Lemma proof_of_pull_entail_wit_3_split_goal_5 : pull_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength cellsr_2 = 400020) by (destruct PreH16 as [H _]; exact H).
  assert (Hd : Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z
             = Znth (2 * v_pre + 1) cellsr_2 (@nil (option Z)))
    by (apply Znth_indep; lia).
  assert (Hcell : Znth ((r + left) % 60)
                    (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z) None
                = Some (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60)))
    by (rewrite Hd; apply PreH18; lia).
  assert (Hrowlen : Zlength (Znth v_pre cellsr_2 __default__List__App_option_Z) = 60).
  { rewrite (Znth_indep cellsr_2 v_pre __default__List__App_option_Z (@nil (option Z))) by lia.
    destruct PreH16 as [_ H]. apply H. lia. }
  rewrite <- (Array2.mixed_def_val
                (Znth (2 * v_pre + 1) cellsr_2 __default__List__App_option_Z)
                ((r + left) % 60) (ex_intro _ _ Hcell)).
  rewrite Array2.replace_mixed_row_roundtrip.
  unfold Array2.replace_mixed_row.
  apply cells_shaped_replace__pull_merge.
  - exact PreH16.
  - lia.
  - rewrite Zlength_replace_Znth__pull_merge. exact Hrowlen.
Qed.

Lemma proof_of_pull_entail_wit_3 : pull_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_pull_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_pull_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_pull_entail_wit_3_split_goal_5.
Qed.


Lemma proof_of_pull_return_wit_1_split_goal_1 : pull_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hr : r = 60) by lia.
  subst r.
  unfold RowIs, RowPrefixIs in *.
  intros r0 Hr0. apply PreH15. lia.
Qed.

Lemma proof_of_pull_return_wit_1 : pull_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pull_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_pull_partial_solve_wit_1_pure_split_goal_1 : pull_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Array2.mixed_def.
  exists (delta (NodeSlice arr lo mid) r).
  apply row_is_value__pull_frame with (ps := NodeSlice arr lo mid).
  - exact PreH16.
  - lia.
  - exact PreH17.
  - lia.
Qed.

Lemma proof_of_pull_partial_solve_wit_1_pure : pull_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pull_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_pull_partial_solve_wit_2_pure_split_goal_1 : pull_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Array2.mixed_def.
  exists (delta (NodeSlice arr (mid + 1) hi) ((r + left) % 60)).
  apply row_is_value__pull_frame with (ps := NodeSlice arr (mid + 1) hi).
  - exact PreH22.
  - lia.
  - exact PreH24.
  - lia.
Qed.

Lemma proof_of_pull_partial_solve_wit_2_pure : pull_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pull_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_build_safety_wit_10_split_goal_1 : build_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_10_split_goal_2 : build_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_10 : build_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_10_split_goal_2.
Qed. 

Lemma proof_of_build_safety_wit_12_split_goal_1 : build_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_12_split_goal_2 : build_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_12 : build_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_12_split_goal_2.
Qed. 

Lemma proof_of_build_safety_wit_14_split_goal_1 : build_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH5) as [Hv1 [Hv2 [Hlo Hle]]].
  all: destruct (quot2_bounds__node_safety (lo_pre + hi_pre)) as [Hq1 Hq2]; [lia |].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_14_split_goal_2 : build_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH5) as [Hv1 [Hv2 [Hlo Hle]]].
  all: destruct (quot2_bounds__node_safety (lo_pre + hi_pre)) as [Hq1 Hq2]; [lia |].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_14 : build_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_14_split_goal_2.
Qed. 

Lemma proof_of_build_safety_wit_15_split_goal_1 : build_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH5) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_15_split_goal_2 : build_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH5) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_15 : build_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_15_split_goal_2.
Qed. 

Lemma proof_of_build_safety_wit_16_split_goal_1 : build_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH5) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_16_split_goal_2 : build_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH5) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_build_safety_wit_16 : build_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_16_split_goal_2.
Qed. 

Lemma proof_of_build_entail_wit_1_split_goal_1 : build_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowsAgreeExcept. intros u Hu. reflexivity.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_2 : build_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowPrefixIs. intros r Hr. exfalso. lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_3 : build_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  pose proof (periods_znth__leaf_loop arr (hi_pre - 1) PreH7 ltac:(lia)) as Hp.
  lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_4 : build_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  pose proof (periods_znth__leaf_loop arr (hi_pre - 1) PreH7 ltac:(lia)) as Hp.
  lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_5 : build_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_6 : build_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_7 : build_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  lia.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_7.
Qed.

Lemma proof_of_build_entail_wit_2_1_split_goal_1 : build_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply rows_agree_replace__leaf_loop; [lia | exact PreH20].
Qed.

Lemma proof_of_build_entail_wit_2_1_split_goal_2 : build_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lo_pre.
  destruct PreH18 as [Hlen Hrows].
  unfold Array2.replace_mixed_row.
  apply row_prefix_step__leaf_loop.
  - exact Hlen.
  - lia.
  - apply Hrows. lia.
  - lia.
  - exact PreH19.
  - apply leaf_delta_rem_zero__leaf_loop; lia.
Qed.

Lemma proof_of_build_entail_wit_2_1_split_goal_3 : build_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply cells_shaped_replace__leaf_loop; [exact PreH18 | lia | lia].
Qed.

Lemma proof_of_build_entail_wit_2_1 : build_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_build_entail_wit_2_2_split_goal_1 : build_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply rows_agree_replace__leaf_loop; [lia | exact PreH20].
Qed.

Lemma proof_of_build_entail_wit_2_2_split_goal_2 : build_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lo_pre.
  destruct PreH18 as [Hlen Hrows].
  unfold Array2.replace_mixed_row.
  apply row_prefix_step__leaf_loop.
  - exact Hlen.
  - lia.
  - apply Hrows. lia.
  - lia.
  - exact PreH19.
  - apply leaf_delta_rem_nonzero__leaf_loop; lia.
Qed.

Lemma proof_of_build_entail_wit_2_2_split_goal_3 : build_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply cells_shaped_replace__leaf_loop; [exact PreH18 | lia | lia].
Qed.

Lemma proof_of_build_entail_wit_2_2 : build_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH8). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  apply cells_agree_outside_compose__tree_frame with (cellsa := cells1).
  - lia.
  - lia.
  - rewrite <- Hq. exact PreH6.
  - rewrite <- Hq. exact PreH3.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_2 : build_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH8). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  apply tree_ok_frame__tree_frame with (cells := cells1)
    (w' := 2 * v_pre + 1) (lo' := (lo_pre + hi_pre) ÷ 2 + 1) (hi' := hi_pre).
  - exact PreH5.
  - exact PreH3.
  - intros u Hin Hin2.
    apply (child_subtrees_disjoint__tree_frame v_pre lo_pre ((lo_pre + hi_pre) ÷ 2)
             ((lo_pre + hi_pre) ÷ 2 + 1) hi_pre u); [lia | exact Hin | exact Hin2].
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_3 : build_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH8). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  apply (nodefits_child_lt__tree_frame v_pre lo_pre hi_pre PreH8 ltac:(lia)).
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_4 : build_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH8). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  lia.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_5 : build_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH8). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  lia.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_6 : build_entail_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH8). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  lia.
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_6.
Qed.

Lemma proof_of_build_return_wit_1_split_goal_1 : build_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply leaf_cells_agree__leaf_loop. exact PreH19.
Qed.

Lemma proof_of_build_return_wit_1_split_goal_2 : build_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lo_pre.
  apply leaf_tree_ok__leaf_loop with (r := r); [lia | exact PreH18].
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_return_wit_1_split_goal_1.
  - Goal_apply proof_of_build_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_build_return_wit_2_split_goal_1 : build_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply cells_agree_outside_row__tree_frame with (cells2 := cells2).
  - exact PreH18.
  - exact PreH3.
Qed.

Lemma proof_of_build_return_wit_2_split_goal_2 : build_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH4). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  apply tree_ok_compose__tree_frame with (cells2 := cells2).
  - lia.
  - lia.
  - exact PreH2.
  - exact PreH3.
  - rewrite <- Hq, <- PreH12. exact PreH16.
  - rewrite <- Hq, <- PreH12. exact PreH17.
Qed.

Lemma proof_of_build_return_wit_2 : build_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_return_wit_2_split_goal_1.
  - Goal_apply proof_of_build_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_build_partial_solve_wit_4_pure_split_goal_1 : build_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH10 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  exact (proj1 (node_fits_child__tree_descent v_pre lo_pre hi_pre PreH10 Hlt)).
Qed.

Lemma proof_of_build_partial_solve_wit_4_pure_split_goal_2 : build_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH10 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  destruct (mid_quot_div__tree_descent lo_pre hi_pre Hlo Hlt) as [_ [Hml Hmr]].
  lia.
Qed.

Lemma proof_of_build_partial_solve_wit_4_pure : build_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_build_partial_solve_wit_4_pure_split_goal_1 _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16).
    cancel.
  - sep_apply (proof_of_build_partial_solve_wit_4_pure_split_goal_2 _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16).
    cancel.
Qed.

Lemma proof_of_build_partial_solve_wit_5_pure_split_goal_1 : build_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH13 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  exact (proj2 (node_fits_child__tree_descent v_pre lo_pre hi_pre PreH13 Hlt)).
Qed.

Lemma proof_of_build_partial_solve_wit_5_pure : build_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  sep_apply (proof_of_build_partial_solve_wit_5_pure_split_goal_1 _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19).
  cancel.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_1 : build_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH9 as [Hv [Hlo [Hle Hk]]].
  lia.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_2 : build_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH17.
  apply PreH21. apply InSub_self.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_3 : build_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH17.
  apply PreH22. apply InSub_self.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_4 : build_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH17.
  apply PreH22. apply InSub_self.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_5 : build_partial_solve_wit_6_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH17.
  apply PreH21. apply InSub_self.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure : build_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_build_partial_solve_wit_6_pure_split_goal_1 _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
    cancel.
  - sep_apply (proof_of_build_partial_solve_wit_6_pure_split_goal_2 _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
    cancel.
  - sep_apply (proof_of_build_partial_solve_wit_6_pure_split_goal_3 _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
    cancel.
  - sep_apply (proof_of_build_partial_solve_wit_6_pure_split_goal_4 _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
    cancel.
  - sep_apply (proof_of_build_partial_solve_wit_6_pure_split_goal_5 _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
    cancel.
Qed.

Lemma proof_of_update_safety_wit_10_split_goal_1 : update_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_10_split_goal_2 : update_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_10 : update_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_update_safety_wit_10_split_goal_2.
Qed. 

Lemma proof_of_update_safety_wit_12_split_goal_1 : update_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH3) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_12_split_goal_2 : update_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH3) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_12 : update_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_update_safety_wit_12_split_goal_2.
Qed. 

Lemma proof_of_update_safety_wit_15_split_goal_1 : update_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH3) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_15_split_goal_2 : update_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH3) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_15 : update_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_update_safety_wit_15_split_goal_2.
Qed. 

Lemma proof_of_update_safety_wit_16_split_goal_1 : update_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH3) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_16_split_goal_2 : update_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (node_fits_int_bounds__node_safety _ _ _ PreH3) as [Hv1 [Hv2 [Hlo Hle]]].
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_update_safety_wit_16 : update_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_update_safety_wit_16_split_goal_2.
Qed. 

Lemma proof_of_update_entail_wit_1_split_goal_1 : update_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowsAgreeExcept. intros u Hu. reflexivity.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_2 : update_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowPrefixIs. intros r Hr. exfalso. lia.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_3 : update_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  pose proof (periods_znth__leaf_loop arr (hi_pre - 1) PreH9 ltac:(lia)) as Hp.
  lia.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_4 : update_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  pose proof (periods_znth__leaf_loop arr (hi_pre - 1) PreH9 ltac:(lia)) as Hp.
  lia.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_5 : update_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_6 : update_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_7 : update_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (node_fits_bounds__leaf_loop _ _ _ PreH2) as [Hv1 [Hv2 [Hlo Hle]]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_1 : update_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_7.
Qed.

Lemma proof_of_update_entail_wit_2_1_split_goal_1 : update_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply rows_agree_replace__leaf_loop; [lia | exact PreH21].
Qed.

Lemma proof_of_update_entail_wit_2_1_split_goal_2 : update_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lo_pre.
  destruct PreH19 as [Hlen Hrows].
  unfold Array2.replace_mixed_row.
  apply row_prefix_step__leaf_loop.
  - exact Hlen.
  - lia.
  - apply Hrows. lia.
  - lia.
  - exact PreH20.
  - apply leaf_delta_rem_zero__leaf_loop; lia.
Qed.

Lemma proof_of_update_entail_wit_2_1_split_goal_3 : update_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply cells_shaped_replace__leaf_loop; [exact PreH19 | lia | lia].
Qed.

Lemma proof_of_update_entail_wit_2_1 : update_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_update_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_update_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_update_entail_wit_2_2_split_goal_1 : update_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply rows_agree_replace__leaf_loop; [lia | exact PreH21].
Qed.

Lemma proof_of_update_entail_wit_2_2_split_goal_2 : update_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lo_pre.
  destruct PreH19 as [Hlen Hrows].
  unfold Array2.replace_mixed_row.
  apply row_prefix_step__leaf_loop.
  - exact Hlen.
  - lia.
  - apply Hrows. lia.
  - lia.
  - exact PreH20.
  - apply leaf_delta_rem_nonzero__leaf_loop; lia.
Qed.

Lemma proof_of_update_entail_wit_2_2_split_goal_3 : update_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Array2.replace_mixed_row.
  apply cells_shaped_replace__leaf_loop; [exact PreH19 | lia | lia].
Qed.

Lemma proof_of_update_entail_wit_2_2 : update_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_update_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_update_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_update_entail_wit_3_1_split_goal_1 : update_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  apply cells_agree_outside_left__tree_frame.
  - lia.
  - rewrite <- Hq. exact PreH3.
Qed.

Lemma proof_of_update_entail_wit_3_1_split_goal_2 : update_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  destruct PreH15 as [arr0 [Hae Htree]].
  assert (Hlen : Zlength arr0 = Zlength arr).
  { unfold AgreeExceptIdx in Hae. destruct Hae as [H1 _]. exact H1. }
  apply tree_ok_stale_frame__tree_frame with (cells := cells) (arr0 := arr0)
    (k := pos_pre - 1) (w' := 2 * v_pre) (lo' := lo_pre)
    (hi' := (lo_pre + hi_pre) ÷ 2).
  - rewrite Hq. apply tree_ok_right__tree_frame; [lia | exact Htree].
  - exact PreH3.
  - intros u Hin Hin2.
    apply (child_subtrees_disjoint__tree_frame v_pre lo_pre ((lo_pre + hi_pre) ÷ 2)
             ((lo_pre + hi_pre) ÷ 2 + 1) hi_pre u); [lia | exact Hin2 | exact Hin].
  - exact Hae.
  - lia.
  - lia.
  - lia.
  - left. lia.
Qed.

Lemma proof_of_update_entail_wit_3_1_split_goal_3 : update_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  apply (nodefits_child_lt__tree_frame v_pre lo_pre hi_pre PreH6 ltac:(lia)).
Qed.

Lemma proof_of_update_entail_wit_3_1_split_goal_4 : update_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_3_1_split_goal_5 : update_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_3_1 : update_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_update_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_update_entail_wit_3_1_split_goal_3.
  - Goal_apply proof_of_update_entail_wit_3_1_split_goal_4.
  - Goal_apply proof_of_update_entail_wit_3_1_split_goal_5.
Qed.

Lemma proof_of_update_entail_wit_3_2_split_goal_1 : update_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  apply cells_agree_outside_right__tree_frame.
  - lia.
  - rewrite <- Hq. exact PreH3.
Qed.

Lemma proof_of_update_entail_wit_3_2_split_goal_2 : update_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  destruct PreH15 as [arr0 [Hae Htree]].
  assert (Hlen : Zlength arr0 = Zlength arr).
  { unfold AgreeExceptIdx in Hae. destruct Hae as [H1 _]. exact H1. }
  apply tree_ok_stale_frame__tree_frame with (cells := cells) (arr0 := arr0)
    (k := pos_pre - 1) (w' := 2 * v_pre + 1)
    (lo' := (lo_pre + hi_pre) ÷ 2 + 1) (hi' := hi_pre).
  - rewrite Hq. apply tree_ok_left__tree_frame; [lia | exact Htree].
  - exact PreH3.
  - intros u Hin Hin2.
    apply (child_subtrees_disjoint__tree_frame v_pre lo_pre ((lo_pre + hi_pre) ÷ 2)
             ((lo_pre + hi_pre) ÷ 2 + 1) hi_pre u); [lia | exact Hin | exact Hin2].
  - exact Hae.
  - lia.
  - lia.
  - lia.
  - right. lia.
Qed.

Lemma proof_of_update_entail_wit_3_2_split_goal_3 : update_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  apply (nodefits_child_lt__tree_frame v_pre lo_pre hi_pre PreH6 ltac:(lia)).
Qed.

Lemma proof_of_update_entail_wit_3_2_split_goal_4 : update_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_3_2_split_goal_5 : update_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH6). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  lia.
Qed.

Lemma proof_of_update_entail_wit_3_2 : update_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_update_entail_wit_3_2_split_goal_2.
  - Goal_apply proof_of_update_entail_wit_3_2_split_goal_3.
  - Goal_apply proof_of_update_entail_wit_3_2_split_goal_4.
  - Goal_apply proof_of_update_entail_wit_3_2_split_goal_5.
Qed.

Lemma proof_of_update_return_wit_1_split_goal_1 : update_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply leaf_cells_agree__leaf_loop. exact PreH20.
Qed.

Lemma proof_of_update_return_wit_1_split_goal_2 : update_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lo_pre.
  apply leaf_tree_ok__leaf_loop with (r := r); [lia | exact PreH19].
Qed.

Lemma proof_of_update_return_wit_1 : update_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_return_wit_1_split_goal_1.
  - Goal_apply proof_of_update_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_update_return_wit_2_split_goal_1 : update_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply cells_agree_outside_row__tree_frame with (cells2 := cells2).
  - exact PreH20.
  - exact PreH3.
Qed.

Lemma proof_of_update_return_wit_2_split_goal_2 : update_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfits := PreH4). unfold NodeFits in Hfits.
  destruct Hfits as [Hv [Hlo [Hle Hkk]]].
  destruct (mid_quot_div__tree_frame lo_pre hi_pre Hlo ltac:(lia)) as [Hq [Hm1 Hm2]].
  apply tree_ok_compose__tree_frame with (cells2 := cells2).
  - lia.
  - lia.
  - exact PreH2.
  - exact PreH3.
  - rewrite <- Hq, <- PreH12. exact PreH18.
  - rewrite <- Hq, <- PreH12. exact PreH19.
Qed.

Lemma proof_of_update_return_wit_2 : update_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_return_wit_2_split_goal_1.
  - Goal_apply proof_of_update_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_1 : update_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH13 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  exact (proj1 (node_fits_child__tree_descent v_pre lo_pre hi_pre PreH13 Hlt)).
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_2 : update_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH13 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  destruct (mid_quot_div__tree_descent lo_pre hi_pre Hlo Hlt) as [_ [Hml Hmr]].
  lia.
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_3 : update_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH13 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  exact (proj1 (stale_child_descend__tree_descent _ _ _ _ _ _ Hlo Hlt PreH22)).
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure : update_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_update_partial_solve_wit_4_pure_split_goal_1 _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_4_pure_split_goal_2 _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_4_pure_split_goal_3 _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
    cancel.
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure_split_goal_1 : update_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH13 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  exact (proj2 (node_fits_child__tree_descent v_pre lo_pre hi_pre PreH13 Hlt)).
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure_split_goal_2 : update_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH13 as HF. destruct HF as [Hv [Hlo [Hle Hk]]].
  assert (Hlt : lo_pre < hi_pre) by lia.
  exact (proj2 (stale_child_descend__tree_descent _ _ _ _ _ _ Hlo Hlt PreH22)).
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure : update_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_update_partial_solve_wit_5_pure_split_goal_1 _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_5_pure_split_goal_2 _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
    cancel.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_1 : update_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH11 as [Hv [Hlo [Hle Hk]]].
  lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_2 : update_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH19.
  apply PreH25. apply InSub_self.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_3 : update_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH19.
  apply PreH26. apply InSub_self.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_4 : update_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH19.
  apply PreH26. apply InSub_self.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_5 : update_partial_solve_wit_6_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH19.
  apply PreH25. apply InSub_self.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure : update_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_update_partial_solve_wit_6_pure_split_goal_1 _ _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_6_pure_split_goal_2 _ _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_6_pure_split_goal_3 _ _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_6_pure_split_goal_4 _ _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27).
    cancel.
  - sep_apply (proof_of_update_partial_solve_wit_6_pure_split_goal_5 _ _ _ _ _ _ _ _ _ PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27).
    cancel.
Qed.

Lemma proof_of_query_safety_wit_1_split_goal_1 : query_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH22 as [Hc _]. lia. }
  assert (Hcell : forall d, Znth (Z.rem t_pre 60) (Znth v_pre cells d) None
                  = Some (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60))).
  { intros d. apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre d
      (Z.rem t_pre 60) Hv PreH23 ltac:(lia)). }
  pose proof (node_slice_facts__query_node arr lo_pre hi_pre PreH6 PreH7
    ltac:(lia) PreH21) as [Hlen Hpk].
  pose proof (delta_bounds__query_node (NodeSlice arr lo_pre hi_pre)
    (Z.rem t_pre 60)) as Hdb.
  unfold Array2.mixed_val. rewrite Hcell. cbv iota. lia.
Qed.

Lemma proof_of_query_safety_wit_1_split_goal_2 : query_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH22 as [Hc _]. lia. }
  assert (Hcell : forall d, Znth (Z.rem t_pre 60) (Znth v_pre cells d) None
                  = Some (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60))).
  { intros d. apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre d
      (Z.rem t_pre 60) Hv PreH23 ltac:(lia)). }
  pose proof (node_slice_facts__query_node arr lo_pre hi_pre PreH6 PreH7
    ltac:(lia) PreH21) as [Hlen Hpk].
  pose proof (delta_bounds__query_node (NodeSlice arr lo_pre hi_pre)
    (Z.rem t_pre 60)) as Hdb.
  unfold Array2.mixed_val. rewrite Hcell. cbv iota. lia.
Qed.

Lemma proof_of_query_safety_wit_1 : query_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NodeFits in PreH1.
  destruct PreH1 as (HNv & HNlo & HNlohi & k & Hk0 & Hk1 & Hk2).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk0) as Hpow.
  pose proof (Z.rem_bound_pos t_pre 60 PreH11 ltac:(lia)) as Hrem.
  nia.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_2 : query_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NodeFits in PreH1.
  destruct PreH1 as (HNv & HNlo & HNlohi & k & Hk0 & Hk1 & Hk2).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk0) as Hpow.
  pose proof (Z.rem_bound_pos t_pre 60 PreH11 ltac:(lia)) as Hrem.
  nia.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_3 : query_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NodeFits in PreH1.
  destruct PreH1 as (HNv & HNlo & HNlohi & k & Hk0 & Hk1 & Hk2).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk0) as Hpow.
  pose proof (Z.rem_bound_pos t_pre 60 PreH11 ltac:(lia)) as Hrem.
  nia.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_4 : query_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NodeFits in PreH1.
  destruct PreH1 as (HNv & HNlo & HNlohi & k & Hk0 & Hk1 & Hk2).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk0) as Hpow.
  pose proof (Z.rem_bound_pos t_pre 60 PreH11 ltac:(lia)) as Hrem.
  nia.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_5 : query_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NodeFits in PreH1.
  destruct PreH1 as (HNv & HNlo & HNlohi & k & Hk0 & Hk1 & Hk2).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk0) as Hpow.
  pose proof (Z.rem_bound_pos t_pre 60 PreH11 ltac:(lia)) as Hrem.
  nia.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_6 : query_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NodeFits in PreH1.
  destruct PreH1 as (HNv & HNlo & HNlohi & k & Hk0 & Hk1 & Hk2).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk0) as Hpow.
  pose proof (Z.rem_bound_pos t_pre 60 PreH11 ltac:(lia)) as Hrem.
  nia.
Qed.

Lemma proof_of_query_entail_wit_1 : query_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_6.
Qed.

Lemma proof_of_query_return_wit_1_split_goal_1 : query_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_query_return_wit_1_split_goal_2 : query_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_query_return_wit_1_split_goal_3 : query_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (query_slice_split__query_compose arr lo_pre hi_pre ql_pre qr_pre ((lo_pre + hi_pre) ÷ 2)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hs as [Hs1 [Hs2 Hs3]].
  rewrite Hs1 by lia.
  rewrite cross_app.
  rewrite <- PreH4.
  reflexivity.
Qed.

Lemma proof_of_query_return_wit_1 : query_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_1_split_goal_1.
  - Goal_apply proof_of_query_return_wit_1_split_goal_2.
  - Goal_apply proof_of_query_return_wit_1_split_goal_3.
Qed. 

Lemma proof_of_query_return_wit_2_split_goal_1 : query_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_query_return_wit_2_split_goal_2 : query_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_query_return_wit_2_split_goal_3 : query_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (query_slice_split__query_compose arr lo_pre hi_pre ql_pre qr_pre ((lo_pre + hi_pre) ÷ 2)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hs as [Hs1 [Hs2 Hs3]].
  rewrite Hs1 by lia.
  rewrite cross_app.
  rewrite <- PreH4.
  reflexivity.
Qed.

Lemma proof_of_query_return_wit_2 : query_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_2_split_goal_1.
  - Goal_apply proof_of_query_return_wit_2_split_goal_2.
  - Goal_apply proof_of_query_return_wit_2_split_goal_3.
Qed. 

Lemma proof_of_query_return_wit_3_split_goal_1 : query_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  lia.
Qed.

Lemma proof_of_query_return_wit_3_split_goal_2 : query_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (query_slice_split__query_compose arr lo_pre hi_pre ql_pre qr_pre ((lo_pre + hi_pre) ÷ 2)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hs as [Hs1 [Hs2 Hs3]].
  rewrite Hs2 by lia.
  exact PreH1.
Qed.

Lemma proof_of_query_return_wit_3 : query_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_3_split_goal_1.
  - Goal_apply proof_of_query_return_wit_3_split_goal_2.
Qed. 

Lemma proof_of_query_return_wit_4_split_goal_1 : query_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  lia.
Qed.

Lemma proof_of_query_return_wit_4_split_goal_2 : query_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (query_slice_split__query_compose arr lo_pre hi_pre ql_pre qr_pre ((lo_pre + hi_pre) ÷ 2)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hs as [Hs1 [Hs2 Hs3]].
  rewrite Hs2 by lia.
  exact PreH1.
Qed.

Lemma proof_of_query_return_wit_4 : query_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_4_split_goal_1.
  - Goal_apply proof_of_query_return_wit_4_split_goal_2.
Qed. 

Lemma proof_of_query_return_wit_5_split_goal_1 : query_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  lia.
Qed.

Lemma proof_of_query_return_wit_5_split_goal_2 : query_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (query_slice_split__query_compose arr lo_pre hi_pre ql_pre qr_pre ((lo_pre + hi_pre) ÷ 2)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hs as [Hs1 [Hs2 Hs3]].
  rewrite Hs3 by lia.
  exact PreH1.
Qed.

Lemma proof_of_query_return_wit_5 : query_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_5_split_goal_1.
  - Goal_apply proof_of_query_return_wit_5_split_goal_2.
Qed. 

Lemma proof_of_query_return_wit_6_split_goal_1 : query_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  lia.
Qed.

Lemma proof_of_query_return_wit_6_split_goal_2 : query_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mid_quot_div__query_compose lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (query_slice_split__query_compose arr lo_pre hi_pre ql_pre qr_pre ((lo_pre + hi_pre) ÷ 2)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hs as [Hs1 [Hs2 Hs3]].
  rewrite Hs3 by lia.
  exact PreH1.
Qed.

Lemma proof_of_query_return_wit_6 : query_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_6_split_goal_1.
  - Goal_apply proof_of_query_return_wit_6_split_goal_2.
Qed. 

Lemma proof_of_query_return_wit_7_split_goal_1 : query_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH22 as [Hc _]. lia. }
  assert (Hcell : forall d, Znth (Z.rem t_pre 60) (Znth v_pre cells d) None
                  = Some (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60))).
  { intros d. apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre d
      (Z.rem t_pre 60) Hv PreH23 ltac:(lia)). }
  pose proof (node_slice_facts__query_node arr lo_pre hi_pre PreH6 PreH7
    ltac:(lia) PreH21) as [Hlen Hpk].
  pose proof (delta_bounds__query_node (NodeSlice arr lo_pre hi_pre)
    (Z.rem t_pre 60)) as Hdb.
  unfold Array2.mixed_val. rewrite Hcell. cbv iota. lia.
Qed.

Lemma proof_of_query_return_wit_7_split_goal_2 : query_return_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH22 as [Hc _]. lia. }
  assert (Hcell : forall d, Znth (Z.rem t_pre 60) (Znth v_pre cells d) None
                  = Some (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60))).
  { intros d. apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre d
      (Z.rem t_pre 60) Hv PreH23 ltac:(lia)). }
  pose proof (node_slice_facts__query_node arr lo_pre hi_pre PreH6 PreH7
    ltac:(lia) PreH21) as [Hlen Hpk].
  pose proof (delta_bounds__query_node (NodeSlice arr lo_pre hi_pre)
    (Z.rem t_pre 60)) as Hdb.
  unfold Array2.mixed_val. rewrite Hcell. cbv iota. lia.
Qed.

Lemma proof_of_query_return_wit_7_split_goal_3 : query_return_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH22 as [Hc _]. lia. }
  assert (Hcell : forall d, Znth (Z.rem t_pre 60) (Znth v_pre cells d) None
                  = Some (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60))).
  { intros d. apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre d
      (Z.rem t_pre 60) Hv PreH23 ltac:(lia)). }
  pose proof (node_slice_facts__query_node arr lo_pre hi_pre PreH6 PreH7
    ltac:(lia) PreH21) as [Hlen Hpk].
  pose proof (delta_bounds__query_node (NodeSlice arr lo_pre hi_pre)
    (Z.rem t_pre 60)) as Hdb.
  rewrite (query_slice_full__query_node arr lo_pre hi_pre ql_pre qr_pre PreH2 PreH1).
  rewrite (delta_mod60__query_node (NodeSlice arr lo_pre hi_pre) t_pre Hpk PreH17).
  unfold Array2.mixed_val. rewrite Hcell. cbv iota. reflexivity.
Qed.

Lemma proof_of_query_return_wit_7_split_goal_spatial : query_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH22 as [Hc _]. lia. }
  assert (Hsome : Znth (Z.rem t_pre 60)
                    (Znth v_pre cells __default__List__App_option_Z) None
                  = Some (Array2.mixed_val
                            (Znth v_pre cells __default__List__App_option_Z)
                            (Z.rem t_pre 60))).
  { apply Array2.mixed_def_val.
    exists (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60)).
    apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre
      __default__List__App_option_Z (Z.rem t_pre 60) Hv PreH23 ltac:(lia)). }
  rewrite <- Hsome.
  rewrite Array2.replace_mixed_row_roundtrip.
  cancel (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells).
Qed.

Lemma proof_of_query_return_wit_7 : query_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_query_return_wit_7_split_goal_1.
  - Goal_apply proof_of_query_return_wit_7_split_goal_2.
  - Goal_apply proof_of_query_return_wit_7_split_goal_3.
Qed.

Lemma proof_of_query_partial_solve_wit_1_pure_split_goal_1 : query_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hv : 0 <= v_pre < Zlength cells).
  { destruct PreH34 as [Hc _]. lia. }
  unfold Array2.mixed_def.
  exists (delta (NodeSlice arr lo_pre hi_pre) (Z.rem t_pre 60)).
  apply (root_row_cell__query_node cells arr v_pre lo_pre hi_pre
    __default__List__App_option_Z (Z.rem t_pre 60) Hv PreH35 ltac:(lia)).
Qed.

Lemma proof_of_query_partial_solve_wit_1_pure : query_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_query_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_query_partial_solve_wit_2_pure_split_goal_1 : query_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_left__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_2_pure_split_goal_2 : query_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_2_pure_split_goal_3 : query_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_2_pure_split_goal_4 : query_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_left__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_2_pure : query_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_2_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_2_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_2_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_2_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_2_pure_split_goal_3 as Hx.
    unfold query_partial_solve_wit_2_pure_split_goal_3 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_2_pure_split_goal_4 as Hx.
    unfold query_partial_solve_wit_2_pure_split_goal_4 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_3_pure_split_goal_1 : query_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_left__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_3_pure_split_goal_2 : query_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_3_pure_split_goal_3 : query_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_3_pure_split_goal_4 : query_partial_solve_wit_3_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_left__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_3_pure : query_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_3_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_3_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_3_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_3_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_3_pure_split_goal_3 as Hx.
    unfold query_partial_solve_wit_3_pure_split_goal_3 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_3_pure_split_goal_4 as Hx.
    unfold query_partial_solve_wit_3_pure_split_goal_4 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_4_pure_split_goal_1 : query_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_right__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_4_pure_split_goal_2 : query_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_4_pure_split_goal_3 : query_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_right__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_4_pure : query_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_4_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_4_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_4_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_4_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_4_pure_split_goal_3 as Hx.
    unfold query_partial_solve_wit_4_pure_split_goal_3 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_5_pure_split_goal_1 : query_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_right__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_5_pure_split_goal_2 : query_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_5_pure_split_goal_3 : query_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_right__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_5_pure : query_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_5_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_5_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_5_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_5_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_5_pure_split_goal_3 as Hx.
    unfold query_partial_solve_wit_5_pure_split_goal_3 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_6_pure_split_goal_1 : query_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_left__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_6_pure_split_goal_2 : query_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (mid_quot_div__query_descent lo_pre hi_pre ltac:(lia) ltac:(lia)) as Hmid.
  destruct Hmid as [Hq Hr].
  lia.
Qed.

Lemma proof_of_query_partial_solve_wit_6_pure_split_goal_3 : query_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_left__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_6_pure : query_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_6_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_6_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_6_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_6_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_6_pure_split_goal_3 as Hx.
    unfold query_partial_solve_wit_6_pure_split_goal_3 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_7_pure_split_goal_1 : query_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_left__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_7_pure_split_goal_2 : query_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_left__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_7_pure : query_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_7_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_7_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_7_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_7_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_8_pure_split_goal_1 : query_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_right__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_8_pure_split_goal_2 : query_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_right__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_8_pure : query_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_8_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_8_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells retval).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_8_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_8_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells retval).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_query_partial_solve_wit_9_pure_split_goal_1 : query_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_right__query_descent; [lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_9_pure_split_goal_2 : query_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply tree_ok_right__query_descent; [lia | lia | assumption].
Qed.

Lemma proof_of_query_partial_solve_wit_9_pure : query_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - pose proof proof_of_query_partial_solve_wit_9_pure_split_goal_1 as Hx.
    unfold query_partial_solve_wit_9_pure_split_goal_1 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells retval).
    all: try assumption.
    cancel.
  - pose proof proof_of_query_partial_solve_wit_9_pure_split_goal_2 as Hx.
    unfold query_partial_solve_wit_9_pure_split_goal_2 in Hx.
    sep_apply (Hx t_pre qr_pre ql_pre hi_pre lo_pre v_pre n arr cells retval).
    all: try assumption.
    cancel.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite node_slice_nil__solver_init by lia; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply periods_ok_of_znth__solver_init.
  intros i Hi. apply PreH12. lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst copied_2.
  replace (i + 1 - 1) with i by lia.
  apply node_slice_prefix__solver_init; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cells0_2.
  assert (Hi : i = n_pre + 1) by lia. subst i.
  replace (n_pre + 1 - 1) with n_pre in PreH17 by lia.
  rewrite <- PreH6 in PreH17.
  rewrite node_slice_all__solver_init in PreH17.
  subst copied.
  unfold IntArray.undef_seg.
  replace (Z.to_nat (n_pre + 1 - (n_pre + 1))) with O by lia.
  simpl.
  Intros_p Hemp.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cells1 (@nil Z) periods (periods :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_pre q_pre).
    rewrite (IntArray.full_empty out_pre 0).
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - split_pures; dump_pre_spatial;
    first
      [ assumption
      | reflexivity
      | (symmetry; apply ask_count_zero__solver_step)
      | (rewrite Zlength_cons, Zlength_nil; lia)
      | (intros j Hj; lia)
      | lia ].
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hq : Znth i queries (0, 0, 0) = (67, Znth i xs 0, Znth i ys 0)).
  { rewrite (PreH18 i ltac:(lia)). rewrite PreH5. reflexivity. }
  assert (Hy : 2 <= Znth i ys 0 <= 6).
  { destruct (PreH19 i ltac:(lia)) as [[[[H65 _] _] _] | [[[_ H2] H2b] H6]];
      [ rewrite PreH5 in H65; discriminate | lia ]. }
  assert (Hne : let ' (d, _, _) := Znth i queries (0, 0, 0) in d <> 65).
  { rewrite Hq. cbn. discriminate. }
  Exists cells1 answers_2
    (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr_2)
    (states_2 ++ (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr_2 :: nil)).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
    first
      [ (rewrite (ask_count_step__solver_step queries i Hne); assumption)
      | (rewrite Zlength_replace_Znth; lia)
      | (apply periods_ok_replace__solver_step; [ assumption | lia | lia ])
      | (rewrite (Zlength_app_cons states_2); lia)
      | (rewrite (app_Znth1 (@nil Z) states_2 _ 0) by lia; assumption)
      | (replace (i + 1) with (Zlength states_2) by lia;
         rewrite (znth_app_last__solver_step (list Z) (@nil Z) states_2);
         reflexivity)
      | (rewrite PreH27; apply query_steps_step__solver_step;
         [ lia | lia | exact Hq | exact PreH33 ])
      | (apply (answers_step__solver_step queries states_2 answers_2 _ i
                 (Znth i xs 0) (Znth i ys 0));
         [ lia | lia | exact Hq | exact PreH34 ])
      | assumption
      | lia ].
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH19 i ltac:(lia)) as
    [[[[Hk65 Hx1] Hxy] Hy] | [[[[H1 H2] H3] H4] H5]];
    [| exfalso; apply PreH5; exact H1].
  assert (Hq : Znth i queries (0, 0, 0) = (65, Znth i xs 0, Znth i ys 0)).
  { rewrite (PreH18 i ltac:(lia)). rewrite Hk65. reflexivity. }
  assert (Hslice : QuerySlice arr_2 1 n_pre (Znth i xs 0) (Znth i ys 0 - 1)
                   = sublist (Znth i xs 0 - 1) (Znth i ys 0 - 1) arr_2).
  { unfold QuerySlice, NodeSlice.
    replace (Z.max 1 (Znth i xs 0)) with (Znth i xs 0) by lia.
    replace (Z.min n_pre (Znth i ys 0 - 1)) with (Znth i ys 0 - 1) by lia.
    reflexivity. }
  assert (Hride : RideTime (Znth i states_2 nil) (Znth i xs 0) (Znth i ys 0) retval).
  { rewrite <- PreH27. rewrite PreH1. rewrite Hslice.
    apply ride_time_cross__solver_final; try assumption; try lia. }
  assert (HSL : Zlength (states_2 ++ (Znth i states_2 nil) :: nil) = i + 1 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (H0S : Znth 0 (states_2 ++ (Znth i states_2 nil) :: nil) nil = periods)
    by (rewrite app_Znth1 by lia; exact PreH26).
  assert (HarrS : arr_2 = Znth (i + 1) (states_2 ++ (Znth i states_2 nil) :: nil) nil).
  { rewrite app_Znth2 by lia.
    replace (i + 1 - Zlength states_2) with 0 by lia. exact PreH27. }
  assert (HAL : Zlength (answers_2 ++ retval :: nil) = nout + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (HAsk : nout + 1 = AskCount queries (i + 1)).
  { rewrite (ask_count_ask__solver_final queries i (Znth i xs 0) (Znth i ys 0)
              ltac:(lia) Hq). lia. }
  assert (HQS : QueryStepsOK queries (states_2 ++ (Znth i states_2 nil) :: nil) (i + 1))
    by (apply (query_steps_extend__solver_final queries states_2 i
                 (Znth i xs 0) (Znth i ys 0)); try lia; assumption).
  assert (HAns : AnswersOK queries (states_2 ++ (Znth i states_2 nil) :: nil)
                   (answers_2 ++ retval :: nil) (i + 1))
    by (apply (answers_extend__solver_final queries states_2 answers_2 i
                 (Znth i xs 0) (Znth i ys 0) retval); try lia; assumption).
  Exists cells_2 (answers_2 ++ retval :: nil) arr_2
         (states_2 ++ (Znth i states_2 nil) :: nil).
  split_pure_spatial.
  - do 8 cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cells_2 answers_2.
  unfold CellsShaped in PreH26. destruct PreH26 as [Hc1 Hc2].
  assert (Hi : i_2 = q_pre) by lia. subst i_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_seg_shape (&( "a_" )) 1 (n_pre + 1) arr).
    cancel.
  - split_pures; dump_pre_spatial; try lia; try exact Hc1; try exact Hc2.
    unfold Spec. exists states.
    apply (traffic_trace_of_invariant__solver_final queries states answers_2 periods q_pre);
      try assumption; try lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_root__solver_init; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  sep_apply (proof_of_solver_partial_solve_wit_4_pure_split_goal_1
    out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells0
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19).
  cancel.
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_1 : solver_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_root__solver_step; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_2 : solver_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_3 : solver_partial_solve_wit_10_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hy : 2 <= Znth i ys 0 <= 6).
  { destruct (PreH24 i ltac:(lia)) as [[[[H65 _] _] _] | [[[_ H2] H2b] H6]];
      [ rewrite PreH10 in H65; discriminate | lia ]. }
  apply periods_ok_replace__solver_step; [ assumption | lia | lia ].
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_4 : solver_partial_solve_wit_10_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hx : 1 <= Znth i xs 0 <= n_pre).
  { destruct (PreH24 i ltac:(lia)) as [[[[H65 _] _] _] | [[[[_ H1] Hn] _] _]];
      [ rewrite PreH10 in H65; discriminate | lia ]. }
  apply (stale_after_write__solver_step cells arr n_pre (Znth i xs 0) (Znth i ys 0));
    [ assumption | lia | lia | assumption ].
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_5 : solver_partial_solve_wit_10_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hx : 1 <= Znth i xs 0 <= n_pre).
  { destruct (PreH24 i ltac:(lia)) as [[[[H65 _] _] _] | [[[[_ H1] Hn] _] _]];
      [ rewrite PreH10 in H65; discriminate | lia ]. }
  apply (stale_after_write__solver_step cells arr n_pre (Znth i xs 0) (Znth i ys 0));
    [ assumption | lia | lia | assumption ].
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_6 : solver_partial_solve_wit_10_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure_split_goal_7 : solver_partial_solve_wit_10_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_root__solver_step; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_10_pure : solver_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_1
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ NodeFits 1 1 n_pre ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_2
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ n_pre = Zlength (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_3
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ PeriodsOK (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_4
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ TreeStaleAt cells (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) 1
               1 n_pre (Znth i xs 0) ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_5
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ TreeStaleAt cells (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) 1
               1 n_pre (Znth i xs 0) ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_6
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ n_pre = Zlength (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_10_pure_split_goal_7
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qx_pre q_pre xs **
       (IntArray.seg &( "a_") 1 (n_pre + 1)
          (replace_Znth (Znth i xs 0 - 1) (Znth i ys 0) arr) **
        (IntArray.full qy_pre q_pre ys **
         (CharArray.full type_pre q_pre kinds **
          (&( "n") # Int |-> n_pre **
           (&( "q") # Int |-> q_pre **
            (&( "a") # Ptr |-> a_pre **
             (&( "type") # Ptr |-> type_pre **
              (&( "qx") # Ptr |-> qx_pre **
               (&( "qy") # Ptr |-> qy_pre **
                (&( "out") # Ptr |-> out_pre **
                 (&( "i") # Int |-> i **
                  (&( "nout") # Int |-> nout **
                   (IntArray.seg a_pre 1 (n_pre + 1) periods **
                    (IntArray.full out_pre nout answers **
                     (IntArray.undef_seg out_pre nout q_pre **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ NodeFits 1 1 n_pre ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_13_pure_split_goal_1 : solver_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_root__solver_step; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_13_pure_split_goal_2 : solver_partial_solve_wit_13_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply node_fits_root__solver_step; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_13_pure : solver_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_13_pure_split_goal_1
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qy_pre q_pre ys **
       (IntArray.full qx_pre q_pre xs **
        (CharArray.full type_pre q_pre kinds **
         (&( "n") # Int |-> n_pre **
          (&( "q") # Int |-> q_pre **
           (&( "a") # Ptr |-> a_pre **
            (&( "type") # Ptr |-> type_pre **
             (&( "qx") # Ptr |-> qx_pre **
              (&( "qy") # Ptr |-> qy_pre **
               (&( "out") # Ptr |-> out_pre **
                (&( "i") # Int |-> i **
                 (&( "nout") # Int |-> nout **
                  (IntArray.seg a_pre 1 (n_pre + 1) periods **
                   (IntArray.full out_pre nout answers **
                    (IntArray.undef_seg out_pre nout q_pre **
                     (IntArray.seg &( "a_") 1 (n_pre + 1) arr **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ NodeFits 1 1 n_pre ”)).
  - Goal_apply ((ltac:(
      sep_apply (proof_of_solver_partial_solve_wit_13_pure_split_goal_2
        out_pre qy_pre qx_pre type_pre q_pre a_pre n_pre queries ys xs kinds periods cells answers arr states nout i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39);
      cancel)) :
      (IntArray.full qy_pre q_pre ys **
       (IntArray.full qx_pre q_pre xs **
        (CharArray.full type_pre q_pre kinds **
         (&( "n") # Int |-> n_pre **
          (&( "q") # Int |-> q_pre **
           (&( "a") # Ptr |-> a_pre **
            (&( "type") # Ptr |-> type_pre **
             (&( "qx") # Ptr |-> qx_pre **
              (&( "qy") # Ptr |-> qy_pre **
               (&( "out") # Ptr |-> out_pre **
                (&( "i") # Int |-> i **
                 (&( "nout") # Int |-> nout **
                  (IntArray.seg a_pre 1 (n_pre + 1) periods **
                   (IntArray.full out_pre nout answers **
                    (IntArray.undef_seg out_pre nout q_pre **
                     (IntArray.seg &( "a_") 1 (n_pre + 1) arr **
                      IntArray2.mixed_full &( "seg") 400020 60 cells)))))))))))))))
       |-- “ NodeFits 1 1 n_pre ”)).
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (Array2Convert.undef_rows 400020 60).
  split_pure_spatial.
  - apply (Array2Convert.int_undef_full_to_mixed_full (&( "seg" )) 400020 60).
  - split_pures; dump_pre_spatial.
    unfold Array2Convert.undef_rows.
    exact undef_cells__solver_init.
Qed. 

