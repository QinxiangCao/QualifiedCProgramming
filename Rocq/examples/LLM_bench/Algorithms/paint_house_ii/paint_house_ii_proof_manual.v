From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.paint_house_ii Require Import paint_house_ii_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.paint_house_ii.paint_house_ii_lib.
Local Open Scope sac.
Require Import AUXLib.MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Ltac paint_math :=
  unfold PaintHouseIICompletedMinima in *;
  try solve [assumption | reflexivity];
  try solve [assumption | reflexivity | intuition lia];
  try solve [intros; eauto 3; intuition lia].

(* Current generated split goals; the witnesses below use the whole-goal route. *)
Lemma proof_of_paint_house_ii_entail_wit_1_split_goal_1 : paint_house_ii_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_2_split_goal_1 : paint_house_ii_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_2_split_goal_2 : paint_house_ii_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_1_split_goal_1 : paint_house_ii_entail_wit_3_1_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_1_split_goal_2 : paint_house_ii_entail_wit_3_1_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_1_split_goal_3 : paint_house_ii_entail_wit_3_1_split_goal_3.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_1_split_goal_4 : paint_house_ii_entail_wit_3_1_split_goal_4.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_2_split_goal_1 : paint_house_ii_entail_wit_3_2_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_2_split_goal_2 : paint_house_ii_entail_wit_3_2_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_2_split_goal_3 : paint_house_ii_entail_wit_3_2_split_goal_3.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_3_2_split_goal_4 : paint_house_ii_entail_wit_3_2_split_goal_4.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_1_split_goal_1 : paint_house_ii_entail_wit_4_1_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_1_split_goal_2 : paint_house_ii_entail_wit_4_1_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_2_split_goal_1 : paint_house_ii_entail_wit_4_2_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_2_split_goal_2 : paint_house_ii_entail_wit_4_2_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_2_split_goal_3 : paint_house_ii_entail_wit_4_2_split_goal_3.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_2_split_goal_4 : paint_house_ii_entail_wit_4_2_split_goal_4.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_3_split_goal_1 : paint_house_ii_entail_wit_4_3_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_3_split_goal_2 : paint_house_ii_entail_wit_4_3_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_3_split_goal_3 : paint_house_ii_entail_wit_4_3_split_goal_3.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_3_split_goal_4 : paint_house_ii_entail_wit_4_3_split_goal_4.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_4_3_split_goal_5 : paint_house_ii_entail_wit_4_3_split_goal_5.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_5_split_goal_1 : paint_house_ii_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_5_split_goal_2 : paint_house_ii_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_5_split_goal_3 : paint_house_ii_entail_wit_5_split_goal_3.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_5_split_goal_4 : paint_house_ii_entail_wit_5_split_goal_4.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_5_split_goal_5 : paint_house_ii_entail_wit_5_split_goal_5.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_5_split_goal_6 : paint_house_ii_entail_wit_5_split_goal_6.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_6_split_goal_1 : paint_house_ii_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_6_split_goal_spatial : paint_house_ii_entail_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_paint_house_ii_return_wit_1_split_goal_1 : paint_house_ii_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_paint_house_ii_entail_wit_1 : paint_house_ii_entail_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hinitial : PaintHouseIIRowMinima costs_l n_pre k_pre 0 0 0 (-1)).
  { unfold PaintHouseIIRowMinima. left. repeat split; reflexivity. }
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_2 : paint_house_ii_entail_wit_2.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  assert (Hinner : (0 <= i < n_pre /\ 0 <= 0 <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i 0 min1
    min2 min1_color 1000000000 1000000000 (-1))).
  { unfold PaintHouseIIColorMinima, PaintHouseIIInf.
    repeat split; auto; try lia. }
  sep_apply_l_atomic (paint_open_row costs_pre costs_l n_pre i
    __default__List_Z ltac:(lia) ltac:(lia)).
  Intros row_ptr.
  Exists row_ptr.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_3_1 : paint_house_ii_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  pose proof (PaintHouseIIDPState_values_bound__loop_core
    costs_l n_pre k_pre i min1 min2 min1_color ltac:(lia) Hcost_bound Hdp)
    as [Hmin1 Hmin2].
  pose proof (Hcosts i c ltac:(lia) ltac:(lia)) as Hcurrent_cost.
  assert (Hselection : PaintHouseIIPrevSelection min1 min2 min1_color c min2).
  { unfold PaintHouseIIPrevSelection. destruct (Z.eq_dec c min1_color); congruence. }
  Exists row_ptr_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_3_2 : paint_house_ii_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  pose proof (PaintHouseIIDPState_values_bound__loop_core
    costs_l n_pre k_pre i min1 min2 min1_color ltac:(lia) Hcost_bound Hdp)
    as [Hmin1 Hmin2].
  pose proof (Hcosts i c ltac:(lia) ltac:(lia)) as Hcurrent_cost.
  assert (Hselection : PaintHouseIIPrevSelection min1 min2 min1_color c min1).
  { unfold PaintHouseIIPrevSelection. destruct (Z.eq_dec c min1_color); congruence. }
  Exists row_ptr_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_1 : paint_house_ii_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  assert (Hinner : (0 <= i < n_pre /\ 0 <= c <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i c min1
    min2 min1_color new_min1 new_min2 new_min1_color)) by paint_math.
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
    costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color
    ltac:(lia) Hcost_bound Hinner) as [Hnew1 [Hnew2 Hnew_color]].
  assert (Hcost_at : PaintCostAt costs_l i c = Znth c (Znth i costs_l __default__List_Z) 0).
  { unfold PaintCostAt. rewrite (Znth_indep costs_l i nil __default__List_Z) by lia. reflexivity. }
  assert (Hnext : (0 <= i < n_pre /\ 0 <= (c + 1) <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i (c
    + 1) min1 min2 min1_color (prev + Znth c (Znth i costs_l __default__List_Z) 0) new_min1 c)).
  { eapply PaintHouseIIInnerState_update_best__loop_core
      with (prev := prev) (new_min2 := new_min2) (new_color := new_min1_color);
      [lia | lia | eassumption | rewrite Hcost_at; reflexivity | exact Hinner]. }
  sep_apply_l_atomic (paint_open_row costs_pre costs_l n_pre i
    __default__List_Z ltac:(lia) ltac:(lia)).
  Intros row_ptr.
  Exists row_ptr.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_2 : paint_house_ii_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  assert (Hinner : (0 <= i < n_pre /\ 0 <= c <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i c min1
    min2 min1_color new_min1 new_min2 new_min1_color)) by paint_math.
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
    costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color
    ltac:(lia) Hcost_bound Hinner) as [Hnew1 [Hnew2 Hnew_color]].
  assert (Hcost_at : PaintCostAt costs_l i c = Znth c (Znth i costs_l __default__List_Z) 0).
  { unfold PaintCostAt. rewrite (Znth_indep costs_l i nil __default__List_Z) by lia. reflexivity. }
  assert (Hnext : (0 <= i < n_pre /\ 0 <= (c + 1) <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i (c
    + 1) min1 min2 min1_color new_min1 (prev + Znth c (Znth i costs_l __default__List_Z) 0) new_min1_color)).
  { eapply PaintHouseIIInnerState_update_second__loop_core
      with (prev := prev) (new_min2 := new_min2);
      [lia | lia | lia | eassumption | rewrite Hcost_at; reflexivity | exact Hinner]. }
  sep_apply_l_atomic (paint_open_row costs_pre costs_l n_pre i
    __default__List_Z ltac:(lia) ltac:(lia)).
  Intros row_ptr.
  Exists row_ptr.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_3 : paint_house_ii_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  assert (Hinner : (0 <= i < n_pre /\ 0 <= c <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i c min1
    min2 min1_color new_min1 new_min2 new_min1_color)) by paint_math.
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
    costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color
    ltac:(lia) Hcost_bound Hinner) as [Hnew1 [Hnew2 Hnew_color]].
  assert (Hcost_at : PaintCostAt costs_l i c = Znth c (Znth i costs_l __default__List_Z) 0).
  { unfold PaintCostAt. rewrite (Znth_indep costs_l i nil __default__List_Z) by lia. reflexivity. }
  pose proof (PaintHouseIIDPState_values_bound__loop_core
    costs_l n_pre k_pre i min1 min2 min1_color ltac:(lia) Hcost_bound Hdp)
    as [Hmin1 Hmin2].
  pose proof (Hcosts i c ltac:(lia) ltac:(lia)) as Hcurrent_cost.
  assert (Htotal_bound : prev + Znth c (Znth i costs_l __default__List_Z) 0 < PaintHouseIIInf).
  { assert (Hselection : PaintHouseIIPrevSelection min1 min2 min1_color c prev) by assumption.
    unfold PaintHouseIIPrevSelection in Hselection.
    destruct (Z.eq_dec c min1_color); subst prev; unfold PaintHouseIIInf; lia. }
  assert (Hnext : (0 <= i < n_pre /\ 0 <= (c + 1) <= k_pre /\ PaintHouseIIColorMinima costs_l n_pre k_pre i (c
    + 1) min1 min2 min1_color new_min1 new_min2 new_min1_color)).
  { eapply PaintHouseIIInnerState_keep__loop_core
      with (prev := prev) (total := prev + Znth c (Znth i costs_l __default__List_Z) 0);
      [lia | lia | lia | exact Htotal_bound | eassumption |
       rewrite Hcost_at; reflexivity | exact Hinner]. }
  sep_apply_l_atomic (paint_open_row costs_pre costs_l n_pre i
    __default__List_Z ltac:(lia) ltac:(lia)).
  Intros row_ptr.
  Exists row_ptr.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_5 : paint_house_ii_entail_wit_5.
Proof.
  LLM_pre_process ltac:(assumption).
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as Hrows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as Hcosts.
  assert (Hcost_bound : forall r col, 0 <= r < n_pre -> 0 <= col < k_pre ->
    0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply Hcosts; assumption. }
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  pose proof (PaintHouseIIDPState_values_bound__loop_core
    costs_l n_pre k_pre i min1 min2 min1_color ltac:(lia) Hcost_bound Hdp)
    as [Hmin1 Hmin2].
  assert (Hcolor_bound : -1 <= min1_color < k_pre).
  { unfold PaintHouseIIRowMinima in Hdp.
    destruct Hdp as [[_ [_ [_ Hcolor]]] | [Hrow [Hbest _]]].
    - subst; lia.
    - pose proof (PaintHouseIIPrefixCost_color_bound__loop_core
        costs_l n_pre k_pre i min1_color min1 Hrow (proj1 Hbest)); lia. }
  Exists row_ptr_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_6 : paint_house_ii_entail_wit_6.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hck : c = k_pre) by lia.
  subst c.
  assert (Hinner : 0 <= i < n_pre /\ 0 <= k_pre <= k_pre /\
    PaintHouseIIColorMinima costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color) by paint_math.
  pose proof (PaintHouseIIInnerState_completed_row__loop_core costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color ltac:(lia) Hinner) as Hcompleted.
  pose proof (proj2 Hcompleted) as Hnext.
  split_pure_spatial.
  - pose proof (IntPtrArray2.missing_i_merge_to_full costs_pre i n_pre row_ptr costs_l (Znth i costs_l __default__List_Z)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    normalize_ptr_size.
    change (IntPtrArray2.ElemArray.full row_ptr (Zlength (Znth i costs_l __default__List_Z)) (Znth i costs_l __default__List_Z)) with (IntArray.full row_ptr (Zlength (Znth i costs_l __default__List_Z)) (Znth i costs_l __default__List_Z)) in Hmerge.
    rewrite replace_Znth_Znth in Hmerge by lia.
    eapply derivable1_trans; [|apply Hmerge; lia].
    repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_paint_house_ii_return_wit_1 : paint_house_ii_return_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hdp : PaintHouseIIRowMinima costs_l n_pre k_pre i min1 min2 min1_color) by paint_math.
  assert (Hanswer : PaintHouseIIOptimalCost costs_l n_pre k_pre min1).
  { replace i with n_pre in Hdp by lia.
    eapply PaintHouseIIDPState_answer__answer; eauto; lia. }
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.
