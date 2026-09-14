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
From SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus Require Import sightseeing_bus_goal.
From SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus Require Import sightseeing_bus_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus.sightseeing_bus_lib.
Local Open Scope sac.

Lemma proof_of_solve_safety_wit_6_split_goal_1 : solve_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH4 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_6_split_goal_2 : solve_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH4 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_8_split_goal_1 : solve_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH4 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_8_split_goal_2 : solve_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH4 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_1 : solve_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_2 : solve_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_12_split_goal_1 : solve_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_12_split_goal_2 : solve_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_22_split_goal_1 : solve_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH9 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  specialize (PreH13 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_22_split_goal_2 : solve_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH9 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  specialize (PreH13 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_23_split_goal_1 : solve_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH9 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_23_split_goal_2 : solve_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH9 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_39_split_goal_1 : solve_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH22 j ltac:(lia)).
  unfold SightseeingInputsBounded in PreH16.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_39_split_goal_2 : solve_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH22 j ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_39 : solve_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_46_split_goal_1 : solve_safety_wit_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH18 pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_46_split_goal_2 : solve_safety_wit_46_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH18 pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_46 : solve_safety_wit_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_46_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_46_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_50_split_goal_1 : solve_safety_wit_50_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH19 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_50_split_goal_2 : solve_safety_wit_50_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH19 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_50 : solve_safety_wit_50.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_50_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_50_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_61_split_goal_1 : solve_safety_wit_61_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH23 (Znth i destinations 0 - 1) ltac:(lia)).
  specialize (PreH24 i ltac:(lia)).
  unfold SightseeingInputsBounded in PreH20.
  destruct PreH20 as [_ [Hm _]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_61_split_goal_2 : solve_safety_wit_61_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH21 as Hstate.
  unfold OptimizedBusState in Hstate.
  destruct Hstate as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hoptimum]]]].
  assert (Hdist_nonnegative :
    forall edge, 0 <= edge < n_pre - 1 ->
      0 <= Znth edge final_dist 0).
  {
    destruct Hfeasible as [_ [Hdist_bounds _]].
    intros edge Hedge.
    specialize (Hdist_bounds edge Hedge).
    lia.
  }
  pose proof
    (arrival_dominates_passenger_time__travel_and_return
       n_pre m_pre dist times origins destinations
       final_dist latest arrivals i
       PreH20 Hlatest (or_intror Hdist_nonnegative) Hschedule
       ltac:(lia)) as Harrival_dominates.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_61 : solve_safety_wit_61.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_61_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_61_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_62_split_goal_1 : solve_safety_wit_62_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH23 (Znth i destinations 0 - 1) ltac:(lia)).
  unfold SightseeingInputsBounded in PreH20.
  destruct PreH20 as [_ [Hm _]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_62_split_goal_2 : solve_safety_wit_62_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH23 (Znth i destinations 0 - 1) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_62 : solve_safety_wit_62.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_62_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_62_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_1_split_goal_1 : solve_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold WorkspacesZeroPrefix in *; cbn in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_1_split_goal_2 : solve_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_1_split_goal_3 : solve_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(cbn in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_1_split_goal_4 : solve_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(unfold SightseeingInputsBounded in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_1 : solve_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold WorkspacesZeroPrefix in *.
  intros station Hstation.
  specialize (PreH6 station).
  destruct (Z_lt_ge_dec station i) as [Hbefore | Hat].
  - specialize (PreH6 ltac:(lia)).
    destruct PreH6 as [Hlatest Hcounts].
    split.
    + rewrite app_Znth1 by (rewrite PreH4; lia).
      exact Hlatest.
    + rewrite app_Znth1 by (rewrite PreH5; lia).
      exact Hcounts.
  - assert (station = i) by lia.
    subst station.
    split.
    + rewrite app_Znth2 by (rewrite PreH4; lia).
      rewrite PreH4.
      replace (i - i) with 0 by lia.
      reflexivity.
    + rewrite app_Znth2 by (rewrite PreH5; lia).
      rewrite PreH5.
      replace (i - i) with 0 by lia.
      reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_2 : solve_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app; cbn; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_3 : solve_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app; cbn; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists counts_prefix latest_prefix.
  split_pure_spatial.
  - assert (Hi : i = n_pre) by lia.
    rewrite Hi in *.
    rewrite (IntArray.undef_seg_empty late_pre n_pre).
    sep_apply_l_atomic
      (IntArray.seg_to_full late_pre 0 n_pre latest_prefix).
    replace (late_pre + 0 * sizeof(INT)) with late_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full late_pre n_pre latest_prefix).
    rewrite (IntArray.undef_seg_empty off_pre n_pre).
    sep_apply_l_atomic
      (IntArray.seg_to_full off_pre 0 n_pre counts_prefix).
    replace (off_pre + 0 * sizeof(INT)) with off_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full off_pre n_pre counts_prefix).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact PreH7.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      intros station Hstation.
      unfold WorkspacesZeroPrefix in PreH6.
      specialize (PreH6 station ltac:(lia)).
      destruct PreH6 as [Hlatest Hcounts].
      unfold SightseeingInputsBounded in PreH7.
      lia.
    + dump_pre_spatial.
      unfold PassengerAggregationPrefix.
      split.
      * intros station Hstation.
        unfold WorkspacesZeroPrefix in PreH6.
        specialize (PreH6 station ltac:(lia)).
        destruct PreH6 as [Hlatest _].
        rewrite Hlatest.
        unfold LatestAtStationPrefix.
        apply MaxMin.max_default_default.
        intros passenger Hpassenger.
        lia.
      * intros station Hstation.
        unfold WorkspacesZeroPrefix in PreH6.
        specialize (PreH6 station ltac:(lia)).
        destruct PreH6 as [_ Hcount].
        rewrite Hcount.
        unfold Sum.sum.
        cbn.
        reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH6 station ltac:(lia)).
  destruct PreH6 as [[[Hlatest_nonnegative Hlatest_upper]
    Hcount_nonnegative] Hcount_upper].
  unfold PassengerAggregationPrefix in PreH7.
  destruct PreH7 as [_ Hcounts].
  specialize (Hcounts station ltac:(lia)).
  unfold Sum.sum in Hcounts.
  cbn in Hcounts.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold SightseeingInputsBounded in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_5_split_goal_1 : solve_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH16.
  destruct PreH16 as [_ [_ [_ [_ [_ [_ [_ Hpassenger]]]]]]].
  specialize (Hpassenger i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_5_split_goal_2 : solve_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH16.
  destruct PreH16 as [_ [_ [_ [_ [_ [_ [_ Hpassenger]]]]]]].
  specialize (Hpassenger i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_1 : solve_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH18.
  destruct PreH18 as [_ [_ [_ [_ [_ [_ [_ Hpassenger]]]]]]].
  specialize (Hpassenger i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_2 : solve_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH18.
  destruct PreH18 as [_ [_ [_ [_ [_ [_ [_ Hpassenger]]]]]]].
  specialize (Hpassenger i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_1 : solve_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (passenger_aggregation_prefix_step__passenger_aggregation
       n_pre m_pre times origins destinations i latest_2 counts_2
       ltac:(lia) PreH22 PreH23 ltac:(lia) ltac:(lia) PreH25) as Hstep.
  rewrite
    (MaxMin.max_r Z.le
       (Znth (Znth i origins 0 - 1) latest_2 0)
       (Znth i times 0) ltac:(lia)) in Hstep.
  exact Hstep.
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_2 : solve_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH23.
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_3 : solve_entail_wit_7_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH22.
Qed.

Lemma proof_of_solve_entail_wit_7_1 : solve_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_1 : solve_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (passenger_aggregation_prefix_step__passenger_aggregation
       n_pre m_pre times origins destinations i latest_2 counts_2
       ltac:(lia) PreH22 PreH23 ltac:(lia) ltac:(lia) PreH25) as Hstep.
  rewrite
    (MaxMin.max_l Z.le
       (Znth (Znth i origins 0 - 1) latest_2 0)
       (Znth i times 0) ltac:(lia)) in Hstep.
  rewrite replace_Znth_Znth in Hstep.
  exact Hstep.
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_2 : solve_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH23.
Qed.

Lemma proof_of_solve_entail_wit_7_2 : solve_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_8_split_goal_1 : solve_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia.
  subst i.
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_solve_entail_wit_8_split_goal_2 : solve_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (passenger_aggregation_complete__comparison_completion
    n_pre m_pre times origins destinations i latest_2 counts_2).
  - lia.
  - exact PreH7.
  - exact PreH8.
  - exact PreH10.
Qed.

Lemma proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_8_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_9_split_goal_1 : solve_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ArrivalSimulationPrefix.
  split.
  - intros station Hstation.
    lia.
  - left.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_9_split_goal_2 : solve_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  exact H.
Qed.

Lemma proof_of_solve_entail_wit_9_split_goal_3 : solve_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_9_split_goal_4 : solve_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH1.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_9_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_1 : solve_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH14.
  - left.
    split; lia.
Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_2 : solve_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, PreH8.
  cbn.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_3 : solve_entail_wit_10_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH13 i ltac:(lia)) as Hlatest.
  unfold SightseeingInputsBounded in PreH9.
  destruct PreH9 as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  specialize (Hdist i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_4 : solve_entail_wit_10_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH13 i ltac:(lia)) as Hlatest.
  unfold SightseeingInputsBounded in PreH9.
  destruct PreH9 as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  specialize (Hdist i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_1 : solve_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_10_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_10_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_10_1_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_1 : solve_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH14.
  - right.
    split; lia.
Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_2 : solve_entail_wit_10_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, PreH8.
  cbn.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_3 : solve_entail_wit_10_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH9 as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  assert (Hlatest : forall station, 0 <= station < n_pre ->
      0 <= Znth station latest_2 0 <= 100000).
  {
    intros station Hstation.
    pose proof (PreH13 station Hstation).
    lia.
  }
  pose proof
    (arrival_simulation_prefix_pending_bound__arrival_simulation
       n_pre dist latest_2 arrivals_prefix_2 i cur
       Hn Hdist Hlatest ltac:(lia) PreH14) as Hcur.
  specialize (Hdist i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_4 : solve_entail_wit_10_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH9.
  destruct PreH9 as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  specialize (Hdist i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_2 : solve_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_10_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_10_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_10_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_10_2_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_1 : solve_entail_wit_10_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre - 1) by lia.
  assert (Hdist_zero : Znth i dist 0 = 0).
  {
    unfold SightseeingInputsBounded in PreH9.
    destruct PreH9 as
      [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
        [Hdestinations_length [Hdist Hpassengers]]]]]]].
    apply Znth_at_or_past_length_default__arrival_simulation; lia.
  }
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH14.
  - left.
    split; lia.
Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_2 : solve_entail_wit_10_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, PreH8.
  cbn.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_3 : solve_entail_wit_10_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH13 i ltac:(lia)) as Hlatest.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_3 : solve_entail_wit_10_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_10_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_10_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_10_3_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_1 : solve_entail_wit_10_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre - 1) by lia.
  assert (Hdist_zero : Znth i dist 0 = 0).
  {
    unfold SightseeingInputsBounded in PreH9.
    destruct PreH9 as
      [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
        [Hdestinations_length [Hdist Hpassengers]]]]]]].
    apply Znth_at_or_past_length_default__arrival_simulation; lia.
  }
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH14.
  - right.
    split; lia.
Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_2 : solve_entail_wit_10_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, PreH8.
  cbn.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_10_4 : solve_entail_wit_10_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_10_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_10_4_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists latest_2 counts_2 arrivals_prefix.
  split_pure_spatial.
  - assert (Hi : i = n_pre) by lia.
    rewrite Hi.
    rewrite (IntArray.undef_seg_empty arr_pre n_pre).
    sep_apply_l_atomic
      (IntArray.seg_to_full arr_pre 0 n_pre arrivals_prefix).
    replace (arr_pre + 0 * sizeof(INT)) with arr_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact PreH4.
    + dump_pre_spatial.
      exact PreH5.
    + dump_pre_spatial.
      exact PreH7.
    + dump_pre_spatial.
      exact PreH8.
    + dump_pre_spatial.
      exact PreH9.
    + dump_pre_spatial.
      unfold CanonicalBusState.
      split; [exact PreH10 |].
      pose proof PreH7 as Hinputs.
      unfold SightseeingInputsBounded in Hinputs.
      destruct Hinputs as
        [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
          [Hdestinations_length [Hdist Hpassengers]]]]]]].
      assert (Hlatest : forall station, 0 <= station < n_pre ->
          0 <= Znth station latest_2 0 <= 100000).
      {
        intros station Hstation.
        pose proof (PreH11 station Hstation).
        lia.
      }
      destruct
        (arrival_simulation_complete__comparison_completion
           n_pre dist latest_2 arrivals_prefix cur Hn Hdist Hlatest
           ltac:(lia)
           ltac:(replace n_pre with i by lia; exact PreH12))
        as [Hschedule Harrivals].
      exact Hschedule.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      pose proof PreH7 as Hinputs.
      unfold SightseeingInputsBounded in Hinputs.
      destruct Hinputs as
        [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
          [Hdestinations_length [Hdist Hpassengers]]]]]]].
      assert (Hlatest : forall station, 0 <= station < n_pre ->
          0 <= Znth station latest_2 0 <= 100000).
      {
        intros station_2 Hstation.
        pose proof (PreH11 station_2 Hstation).
        lia.
      }
      destruct
        (arrival_simulation_complete__comparison_completion
           n_pre dist latest_2 arrivals_prefix cur Hn Hdist Hlatest
           ltac:(lia)
           ltac:(replace n_pre with i by lia; exact PreH12))
        as [Hschedule Harrivals].
      exact Harrivals.
Qed.

Lemma proof_of_solve_entail_wit_12_split_goal_1 : solve_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply booster_progress_initial_active__booster_and_scan_initialization;
    eauto.
Qed.

Lemma proof_of_solve_entail_wit_12_split_goal_2 : solve_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : 0 <= station < n_pre |- _ => rename H into Hstation
  end.
  pose proof
    (canonical_station_bounds__booster_and_scan_initialization
      n_pre m_pre dist times origins destinations latest_2 counts_2 arrivals_2
      station PreH3 PreH6 PreH8 Hstation) as Hbounds.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_12_split_goal_3 : solve_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : 0 <= edge < n_pre - 1 |- _ => rename H into Hedge
  end.
  unfold SightseeingInputsBounded in PreH3.
  destruct PreH3 as [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  apply Hdist.
  exact Hedge.
Qed.

Lemma proof_of_solve_entail_wit_12_split_goal_4 : solve_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanonicalBusState, StationSummaryState,
    DestinationCounts in PreH6.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_12_split_goal_5 : solve_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanonicalBusState, StationSummaryState,
    LatestDepartures in PreH6.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_12_split_goal_6 : solve_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH3.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_12 : solve_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_12_split_goal_6.
Qed.

Lemma proof_of_solve_entail_wit_13_split_goal_1 : solve_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EdgeChoicePrefix.
  split.
  - apply MaxMin.max_default_default.
    intros [edge benefit] Heligible.
    unfold EligibleEdgeBenefit in Heligible.
    cbn in Heligible.
    lia.
  - left.
    lia.
Qed.

Lemma proof_of_solve_entail_wit_13_split_goal_2 : solve_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH11.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_13_split_goal_3 : solve_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_13_split_goal_4 : solve_entail_wit_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH5.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_split_goal_5 : solve_entail_wit_13_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH5.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13 : solve_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_13_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_13_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_13_split_goal_5.
Qed.

Lemma proof_of_solve_entail_wit_14_split_goal_1 : solve_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply marginal_benefit_scan_empty__booster_and_scan_initialization.
Qed.

Lemma proof_of_solve_entail_wit_14_split_goal_2 : solve_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH18.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_14_split_goal_3 : solve_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH17.
  assumption.
Qed.

Lemma proof_of_solve_entail_wit_14 : solve_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_14_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_15_split_goal_1 : solve_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply marginal_benefit_scan_snoc__edge_benefit_scan;
    [lia | exact PreH26 | lia].
Qed.

Lemma proof_of_solve_entail_wit_15_split_goal_2 : solve_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress in PreH24.
  destruct PreH24 as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  unfold SightseeingInputsBounded in PreH17.
  eapply
    (marginal_benefit_scan_extended_upper__booster_and_scan_initialization
      n_pre m_pre destinations counts_2 latest_2 arrivals_2 i j cnt);
    [lia | lia | lia | lia | exact Hcounts | exact PreH26].
Qed.

Lemma proof_of_solve_entail_wit_15_split_goal_3 : solve_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH23 j ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_15 : solve_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_15_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_16_1_split_goal_1 : solve_entail_wit_16_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply marginal_scan_to_edge_benefit__edge_benefit_scan
    with (next := j) (benefit := cnt).
  - lia.
  - lia.
  - exact PreH25.
  - left. split; lia.
Qed.

Lemma proof_of_solve_entail_wit_16_1 : solve_entail_wit_16_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_16_1_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_1 : solve_entail_wit_16_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply marginal_scan_to_edge_benefit__edge_benefit_scan
    with (next := j) (benefit := cnt).
  - lia.
  - lia.
  - exact PreH26.
  - right.
    split; [lia |].
    split; [exact PreH1 | reflexivity].
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_2 : solve_entail_wit_16_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH17 as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as [Hn [Hm Hinput_rest]].
  pose proof PreH24 as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  pose proof
    (destination_count_interval_bound__edge_benefit_scan
      n_pre m_pre destinations counts (i + 1) (j + 1)
      ltac:(lia) ltac:(repeat split; lia) Hcounts) as Hinterval_bound.
  unfold MarginalBenefitScan in PreH26.
  destruct PreH26 as [Hcnt Hstrict].
  rewrite ZRange.sum_Z_range_extend_right in Hinterval_bound by lia.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_3 : solve_entail_wit_16_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH23 j ltac:(lia)) as Hstation_bounds.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_16_2 : solve_entail_wit_16_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_1 : solve_entail_wit_17_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (edge_choice_prefix_step__edge_choice
      n_pre current_dist_2 counts_2 latest_2 arrivals_2
      i best pos cnt PreH18 PreH5 PreH6 PreH15 PreH19)
    as [Hbetter Hnot_better].
  apply Hbetter.
  exact PreH1.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_2 : solve_entail_wit_17_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hstation : 0 <= station /\ station < n_pre |- _ =>
      pose proof
        (booster_progress_station_bounds__edge_benefit_and_choice
          n_pre m_pre k_pre k dist times origins destinations
          current_dist_2 latest_2 counts_2 arrivals_2
          PreH16 PreH17 station Hstation) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_3 : solve_entail_wit_17_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hedge : 0 <= edge /\ edge < n_pre - 1 |- _ =>
      pose proof PreH16 as Hinput_fields;
      unfold SightseeingInputsBounded in Hinput_fields;
      destruct Hinput_fields as
        [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
          [Hdestinations_len [Hinitial_bounds Hpassenger_bounds]]]]]]];
      pose proof PreH17 as Hprogress_fields;
      unfold BoosterProgress in Hprogress_fields;
      destruct Hprogress_fields as
        [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]];
      unfold FeasibleBoostedDistances in Hfeasible;
      destruct Hfeasible as [Hcurrent_len [Hcurrent_bounds Hbudget]];
      specialize (Hinitial_bounds edge Hedge);
      specialize (Hcurrent_bounds edge Hedge)
  end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_4 : solve_entail_wit_17_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, BusArrivalSchedule in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_5 : solve_entail_wit_17_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, DestinationCounts in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_6 : solve_entail_wit_17_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, LatestDepartures in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_7 : solve_entail_wit_17_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, FeasibleBoostedDistances in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_1 : solve_entail_wit_17_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_1 : solve_entail_wit_17_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (edge_choice_prefix_step__edge_choice
      n_pre current_dist_2 counts_2 latest_2 arrivals_2
      i best pos cnt PreH18 PreH5 PreH6 PreH15 PreH19)
    as [Hbetter Hnot_better].
  apply Hnot_better.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_2 : solve_entail_wit_17_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hstation : 0 <= station /\ station < n_pre |- _ =>
      pose proof
        (booster_progress_station_bounds__edge_benefit_and_choice
          n_pre m_pre k_pre k dist times origins destinations
          current_dist_2 latest_2 counts_2 arrivals_2
          PreH16 PreH17 station Hstation) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_3 : solve_entail_wit_17_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hedge : 0 <= edge /\ edge < n_pre - 1 |- _ =>
      pose proof PreH16 as Hinput_fields;
      unfold SightseeingInputsBounded in Hinput_fields;
      destruct Hinput_fields as
        [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
          [Hdestinations_len [Hinitial_bounds Hpassenger_bounds]]]]]]];
      pose proof PreH17 as Hprogress_fields;
      unfold BoosterProgress in Hprogress_fields;
      destruct Hprogress_fields as
        [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]];
      unfold FeasibleBoostedDistances in Hfeasible;
      destruct Hfeasible as [Hcurrent_len [Hcurrent_bounds Hbudget]];
      specialize (Hinitial_bounds edge Hedge);
      specialize (Hcurrent_bounds edge Hedge)
  end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_4 : solve_entail_wit_17_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, BusArrivalSchedule in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_5 : solve_entail_wit_17_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, DestinationCounts in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_6 : solve_entail_wit_17_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, LatestDepartures in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_7 : solve_entail_wit_17_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, FeasibleBoostedDistances in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_17_2 : solve_entail_wit_17_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_17_3_split_goal_1 : solve_entail_wit_17_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply edge_choice_prefix_skip__edge_choice.
  - exact PreH1.
  - lia.
  - lia.
  - intros edge Hedge.
    pose proof (PreH17 edge Hedge) as Hedge_bounds.
    lia.
  - exact PreH20.
Qed.

Lemma proof_of_solve_entail_wit_17_3 : solve_entail_wit_17_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_17_3_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_18 : solve_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre - 1) by lia.
  subst i.
  assert (Hbest : 0 < best) by lia.
  assert (Hchoice :
    BestBoostChoice n_pre current_dist counts_2 latest_2 arrivals best pos).
  {
    unfold BestBoostChoice.
    exact PreH21.
  }
  pose proof (best_boost_choice_positive_edge__saturation
    n_pre current_dist counts_2 latest_2 arrivals best pos
    Hbest Hchoice) as [Hpos_range Hpos_positive].
  assert (Hnew_dist_length :
    Zlength (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist) =
    n_pre - 1).
  {
    rewrite Zlength_replace_Znth.
    exact PreH14.
  }
  assert (Hnew_dist_bounds : forall edge,
    0 <= edge < n_pre - 1 ->
    0 <= Znth edge
      (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist) 0 <=
      100).
  {
    intros edge Hedge.
    destruct (Z.eq_dec edge pos) as [Heq | Hne].
    - subst edge.
      rewrite Znth_replace_Znth_Same by lia.
      specialize (PreH18 pos ltac:(lia)).
      lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      apply PreH18.
      exact Hedge.
  }
  assert (Hrepair :
    ArrivalRepairProgress n_pre current_dist arrivals
      (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist)
      arrivals latest_2 pos (pos + 1)).
  {
    eapply arrival_repair_progress_init__arrival_repair;
      eauto.
  }
  Exists counts_2 latest_2 arrivals arrivals
    (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist)
    current_dist.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_19 : solve_entail_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi_range : 0 <= i < n_pre) by lia.
  assert (Hnew_arrivals_length :
    Zlength
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) =
    n_pre).
  {
    rewrite Zlength_replace_Znth.
    exact PreH16.
  }
  assert (Hnew_arrivals_bounds : forall station,
    0 <= station < n_pre ->
    (((0 <= Znth station latest_2 0 <= 100000 /\
       0 <= Znth station counts_2 0) /\
      Znth station counts_2 0 <= m_pre) /\
     0 <= Znth station
       (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) 0) /\
    Znth station
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) 0 <=
    200000).
  {
    intros station Hstation.
    specialize (PreH20 station Hstation).
    destruct (Z.eq_dec station i) as [Heq | Hne].
    - subst station.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same in PreH1 by lia.
      destruct PreH20 as
        [[[[Hlatest_bounds Hcount_lower] Hcount_upper]
          Harrival_lower] Harrival_upper].
      repeat split; try assumption; lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      exact PreH20.
  }
  assert (Hrepair :
    ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2)
      latest_2 pos (i + 1)).
  {
    eapply arrival_repair_progress_step__arrival_repair;
      eauto; lia.
  }
  Exists counts_2 latest_2
    (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2)
    old_arrivals_2 new_dist_2 old_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_20_1 : solve_entail_wit_20_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Houtcome :
    ArrivalRepairOutcome n_pre old_dist_2 old_arrivals_2
      new_dist_2 new_arrivals_2 latest_2 pos).
  {
    eapply arrival_repair_progress_outcome__arrival_repair
      with (new_arrivals := new_arrivals_2) (stop := n_pre);
      eauto; try lia.
  }
  Exists old_dist_2 latest_2 counts_2 old_arrivals_2
    new_arrivals_2 new_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_20_2 : solve_entail_wit_20_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew_arrivals_length :
    Zlength
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) =
    n_pre).
  {
    rewrite Zlength_replace_Znth.
    exact PreH16.
  }
  assert (Houtcome :
    ArrivalRepairOutcome n_pre old_dist_2 old_arrivals_2 new_dist_2
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2)
      latest_2 pos).
  {
    eapply arrival_repair_progress_outcome__arrival_repair
      with (new_arrivals := new_arrivals_2) (stop := i).
    - exact PreH16.
    - lia.
    - lia.
    - exact PreH23.
    - right.
      repeat split; try assumption; reflexivity.
  }
  Exists old_dist_2 latest_2 counts_2 old_arrivals_2
    (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2)
    new_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solve_entail_wit_21 : solve_entail_wit_21.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcertificate :
    SelectedExchangeCertificate
      n_pre m_pre k_pre k dist times origins destinations
      old_dist_2 latest_2 counts_2 old_arrivals_2 best).
  {
    eapply selected_exchange_certificate_from_repair__normalization;
      eauto.
  }
  Exists old_dist_2 latest_2 counts_2 old_arrivals_2
    new_arrivals_2 new_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | lia].
Qed.

Lemma proof_of_solve_entail_wit_22_split_goal_1 : solve_entail_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH13 as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [old_total [Hold_total [Hold_minimum Hold_total_bounds]]]]]]].
  assert (Hnew_feasible :
    FeasibleBoostedDistances
      n_pre (k_pre - (k - 1)) dist new_dist).
  {
    eapply feasible_boosted_distances_step__exchange_certificate_transition;
      eauto.
  }
  assert (Hnew_schedule :
    BusArrivalSchedule n_pre new_dist latest_2 new_arrivals).
  {
    eapply arrival_repair_outcome_schedule__saturation; eauto.
  }
  assert (Hnew_total :
    PassengerTravelTotal
      m_pre times destinations new_arrivals (old_total - best)).
  {
    eapply passenger_travel_total_after_repair__saturation; eauto.
  }
  assert (Hnew_minimum :
    SightseeingMinimumTotal
      n_pre m_pre (k_pre - (k - 1))
      dist times origins destinations (old_total - best)).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset.
    exists (old_total - best).
    split.
    - split.
      + unfold SightseeingCandidateTotal.
        exists new_dist, latest_2, new_arrivals.
        exact (conj Hlatest
          (conj Hnew_feasible (conj Hnew_schedule Hnew_total))).
      + intros candidate_total Hcandidate.
        eapply selected_exchange_adjacent_lower_bound__exchange;
          try eassumption.
        replace (k_pre - k + 1) with (k_pre - (k - 1)) by lia.
        exact Hcandidate.
    - reflexivity.
  }
  pose proof Hnew_feasible as Hnew_feasible_fields.
  unfold FeasibleBoostedDistances in Hnew_feasible_fields.
  destruct Hnew_feasible_fields as
    [Hnew_dist_length [Hnew_dist_bounds Hnew_budget]].
  assert (Hnew_total_nonnegative : 0 <= old_total - best).
  {
    eapply passenger_travel_total_nonnegative__exchange_certificate_transition
      with (n := n_pre) (initial_dist := dist)
           (origins := origins) (final_dist := new_dist)
           (latest := latest_2) (arrivals := new_arrivals);
      eauto.
    intros edge Hedge.
    exact (proj1 (Hnew_dist_bounds edge Hedge)).
  }
  unfold BoosterProgress.
  split; [exact Hlatest |].
  split; [exact Hcounts |].
  split; [exact Hnew_feasible |].
  split; [exact Hnew_schedule |].
  exists (old_total - best).
  split; [exact Hnew_total |].
  split; [exact Hnew_minimum |].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_22_split_goal_2 : solve_entail_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : 0 <= station /\ station < n_pre |- _ =>
      pose proof H as Hstation
  end.
  pose proof PreH12 as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  pose proof PreH13 as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  pose proof (latest_at_station_bounds__exchange_certificate_transition
    n_pre m_pre dist times origins destinations latest_2 station
    PreH12 Hlatest Hstation) as Hlatest_bounds.
  pose proof (destination_count_bounds__exchange_certificate_transition
    n_pre m_pre destinations counts_2 station
    ltac:(lia) Hcounts Hstation) as Hcount_bounds.
  pose proof (arrival_repair_outcome_bounds__exchange_certificate_transition
    n_pre m_pre k_pre k dist times origins destinations
    old_dist old_arrivals new_dist new_arrivals latest_2 counts_2 best pos
    PreH12 PreH13 PreH6 PreH14 PreH16 station Hstation)
    as Harrival_bounds.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_22_split_goal_3 : solve_entail_wit_22_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : 0 <= edge /\ edge < n_pre - 1 |- _ =>
      pose proof H as Hedge
  end.
  eapply arrival_repair_outcome_distance_bounds__exchange_certificate_transition;
    eauto.
Qed.

Lemma proof_of_solve_entail_wit_22_split_goal_4 : solve_entail_wit_22_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, DestinationCounts in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_22_split_goal_5 : solve_entail_wit_22_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress, LatestDepartures in *.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_22 : solve_entail_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_22_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_22_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_22_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_22_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_22_split_goal_5.
Qed.

Lemma proof_of_solve_entail_wit_23_1_split_goal_1 : solve_entail_wit_23_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_23_1_split_goal_2 : solve_entail_wit_23_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH5.
  destruct PreH5 as [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger H).
  destruct Hpassenger_bounds as
    [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_23_1_split_goal_3 : solve_entail_wit_23_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH11 station H) as Hstation_bounds.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_23_1_split_goal_4 : solve_entail_wit_23_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BoosterProgress in PreH12.
  unfold OptimizedBusState.
  replace (k_pre - k) with k_pre in PreH12 by lia.
  exact PreH12.
Qed.

Lemma proof_of_solve_entail_wit_23_1_split_goal_5 : solve_entail_wit_23_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH5.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_23_1 : solve_entail_wit_23_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_23_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_23_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_23_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_23_1_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_23_1_split_goal_5.
Qed.

Lemma proof_of_solve_entail_wit_23_2_split_goal_1 : solve_entail_wit_23_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_23_2_split_goal_2 : solve_entail_wit_23_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH12.
  destruct PreH12 as [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger H).
  destruct Hpassenger_bounds as
    [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_23_2_split_goal_3 : solve_entail_wit_23_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH18 station H) as Hstation_bounds.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_23_2_split_goal_4 : solve_entail_wit_23_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbest_choice :
    BestBoostChoice n_pre current_dist counts_2 latest_2 arrivals_2
      best pos).
  {
    unfold BestBoostChoice.
    replace (n_pre - 1) with i by lia.
    exact PreH20.
  }
  assert (Hbest_zero : best = 0).
  {
    unfold EdgeChoicePrefix in PreH20.
    destruct PreH20 as [Hmaximum [Hdefault | Heligible]].
    - tauto.
    - unfold EligibleEdgeBenefit in Heligible.
      cbn in Heligible.
      lia.
  }
  exact (booster_progress_zero_best_optimized__termination_and_travel_total
    n_pre m_pre k_pre k dist times origins destinations
    current_dist latest_2 counts_2 arrivals_2 best pos
    ltac:(lia) PreH4 PreH12 PreH19 Hbest_choice Hbest_zero).
Qed.

Lemma proof_of_solve_entail_wit_23_2 : solve_entail_wit_23_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_23_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_23_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_23_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_23_2_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_23_3_split_goal_1 : solve_entail_wit_23_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_entail_wit_23_3_split_goal_2 : solve_entail_wit_23_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SightseeingInputsBounded in PreH13.
  destruct PreH13 as [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger H).
  destruct Hpassenger_bounds as
    [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_23_3_split_goal_3 : solve_entail_wit_23_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 station H) as Hstation_bounds.
  tauto.
Qed.

Lemma proof_of_solve_entail_wit_23_3_split_goal_4 : solve_entail_wit_23_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbest_choice :
    BestBoostChoice n_pre current_dist counts_2 latest_2 arrivals_2
      best pos).
  {
    unfold BestBoostChoice.
    replace (n_pre - 1) with i by lia.
    exact PreH21.
  }
  exact (booster_progress_zero_best_optimized__termination_and_travel_total
    n_pre m_pre k_pre k dist times origins destinations
    current_dist latest_2 counts_2 arrivals_2 best pos
    ltac:(lia) PreH5 PreH13 PreH20 Hbest_choice PreH1).
Qed.

Lemma proof_of_solve_entail_wit_23_3 : solve_entail_wit_23_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_23_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_23_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_23_3_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_23_3_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_24_split_goal_1 : solve_entail_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24_split_goal_2 : solve_entail_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_24 : solve_entail_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_24_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_24_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_25_split_goal_1 : solve_entail_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (travel_sum_prefix_step__travel_and_return
    m_pre times destinations arrivals_2 i ans
    PreH15 PreH11 PreH25) as Hstep.
  unfold TravelSumPrefix in Hstep.
  unfold TravelSumPrefix.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_25_split_goal_2 : solve_entail_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH23 (Znth i destinations 0 - 1) ltac:(lia))
    as Harrival_bounds.
  pose proof (PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  unfold SightseeingInputsBounded in PreH20.
  destruct PreH20 as [_ [Hm _]].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_25_split_goal_3 : solve_entail_wit_25_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH23 (Znth i destinations 0 - 1) ltac:(lia))
    as Harrival_bounds.
  pose proof (PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  lia.
Qed.

Lemma proof_of_solve_entail_wit_25_split_goal_4 : solve_entail_wit_25_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH21 as Hoptimized.
  unfold OptimizedBusState in Hoptimized.
  destruct Hoptimized as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hoptimum]]]].
  pose proof Hfeasible as Hfeasible_fields.
  unfold FeasibleBoostedDistances in Hfeasible_fields.
  destruct Hfeasible_fields as [_ [Hdist_bounds _]].
  assert (Hdist_nonnegative : forall edge, 0 <= edge < n_pre - 1 ->
    0 <= Znth edge final_dist_2 0).
  {
    intros edge Hedge.
    specialize (Hdist_bounds edge Hedge).
    lia.
  }
  pose proof (arrival_dominates_passenger_time__travel_and_return
    n_pre m_pre dist times origins destinations
    final_dist_2 latest_2 arrivals_2 i
    PreH20 Hlatest (or_intror Hdist_nonnegative) Hschedule ltac:(lia))
    as Harrival_dominates.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_25 : solve_entail_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_25_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_25_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_25_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_25_split_goal_4.
Qed.

Lemma proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OptimizedBusState in PreH11.
  tauto.
Qed.

Lemma proof_of_solve_return_wit_1_split_goal_2 : solve_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = m_pre) by lia.
  subst i.
  pose proof (proj1 (travel_sum_prefix_complete__travel_and_return
    m_pre times destinations arrivals_2 ans ltac:(lia)) PreH15)
    as Hans_total.
  unfold OptimizedBusState in PreH11.
  destruct PreH11 as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [optimum [Hoptimum_total [Hminimum Hanswer_bounds]]]]]]].
  assert (Hans : ans = optimum).
  {
    unfold PassengerTravelTotal in Hans_total, Hoptimum_total.
    lia.
  }
  subst optimum.
  unfold SightseeingOptimalState.
  tauto.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solve_return_wit_1_split_goal_2.
Qed.
