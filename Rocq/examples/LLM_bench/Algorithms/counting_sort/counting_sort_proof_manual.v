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
From SimpleC.EE.LLM_bench.Algorithms.counting_sort Require Import counting_sort_goal.
From SimpleC.EE.LLM_bench.Algorithms.counting_sort Require Import counting_sort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib.
Local Open Scope sac.

Lemma proof_of_sort_entail_wit_1 : sort_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (repeat (@None Z) (Z.to_nat 100))
         (repeat (@None Z) (Z.to_nat 100)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full ( &( "output" ) ) 100).
    sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full ( &( "count" ) ) 100).
    cancel (IntArray.full a_pre n_pre input).
    cancel (IntArray.mixed_full ( &( "output" ) ) 100
      (repeat (@None Z) (Z.to_nat 100))).
    cancel (IntArray.mixed_full ( &( "count" ) ) 100
      (repeat (@None Z) (Z.to_nat 100))).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite !Zlength_correct, repeat_length; reflexivity).
    + intros k Hk.
      apply Znth_repeat_lt.
      lia.
    + unfold CountingZeroedPrefix.
      intros value Hvalue.
      lia.
Qed.

Lemma proof_of_sort_entail_wit_2_split_goal_1 : sort_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply counting_zeroed_prefix_replace__initial_zeroing; eauto.
Qed.

Lemma proof_of_sort_entail_wit_2_split_goal_2 : sort_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH6.
Qed.

Lemma proof_of_sort_entail_wit_2 : sort_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_3 : sort_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvalue : value_2 = 100) by lia.
  assert (Hmaterialized :
    count_mixed = map (@Some Z) (repeat 0 (Z.to_nat 100))).
  {
    apply counting_all_zero_materialization__initial_zeroing.
    - exact PreH6.
    - intros value Hvalue_bounds.
      apply PreH11.
      lia.
  }
  subst count_mixed.
  Exists (repeat 0 (Z.to_nat 100)) output_mixed_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre input).
    cancel (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2).
    sep_apply_l_atomic
      (IntArray.mixed_full_to_full ( &( "count" ) ) 100
        (repeat 0 (Z.to_nat 100))).
    cancel (IntArray.full ( &( "count" ) ) 100
      (repeat 0 (Z.to_nat 100))).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite !Zlength_correct, repeat_length; reflexivity).
    + intros value Hvalue_bounds.
      apply Znth_repeat.
    + apply counting_histogram_empty__initial_zeroing.
      intros value Hvalue_bounds.
      apply Znth_repeat.
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_1 : sort_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_2 : sort_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 by lia.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_3 : sort_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_4 : sort_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_sort_entail_wit_6_split_goal_1 : sort_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CountingHistogramPrefix in PreH18 |- *.
  intros bucket Hbucket.
  pose proof (counting_frequency_prefix_snoc__histogram_cumulative
    input i bucket ltac:(lia)) as Hfrequency.
  destruct (Z.eq_dec (Znth i input 0) bucket) as [Heq | Hneq].
  - subst bucket.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Hfrequency.
    rewrite PreH18 by lia.
    destruct (Z.eq_dec (Znth i input 0) (Znth i input 0)); lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite Hfrequency.
    rewrite PreH18 by lia.
    destruct (Z.eq_dec (Znth i input 0) bucket); [contradiction | lia].
Qed.

Lemma proof_of_sort_entail_wit_6_split_goal_2 : sort_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH12.
Qed.

Lemma proof_of_sort_entail_wit_6 : sort_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_1 : sort_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  unfold CountingCumulativeState.
  intros bucket Hbucket.
  unfold CountingHistogramPrefix in PreH12.
  pose proof (PreH12 bucket Hbucket) as Hhistogram.
  rewrite (sublist_self input n_pre) in Hhistogram by lia.
  rewrite Hhistogram.
  destruct (Z.ltb bucket 1) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    assert (bucket = 0) by lia.
    subst bucket.
    unfold CountingCumulativeEnd.
    simpl.
    lia.
  - reflexivity.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_2 : sort_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_3 : sort_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  unfold CountingHistogramPrefix in PreH12.
  pose proof (PreH12 0 ltac:(lia)) as Hzero.
  pose proof (PreH12 1 ltac:(lia)) as Hone.
  rewrite (sublist_self input n_pre) in Hzero by lia.
  rewrite (sublist_self input n_pre) in Hone by lia.
  replace (1 - 1) with 0 by lia.
  rewrite Hone, Hzero.
  pose proof (counting_frequency_range_sum_bound__histogram_cumulative
    (cons 1 (cons 0 nil)) input
    ltac:(repeat constructor; simpl; lia)) as Hbound.
  simpl in Hbound.
  rewrite PreH4 in Hbound.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_4 : sort_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  apply PreH10.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_5 : sort_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_sort_entail_wit_7 : sort_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_5.
Qed.

Lemma proof_of_sort_entail_wit_8_split_goal_1 : sort_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CountingCumulativeState in PreH13 |- *.
  intros bucket Hbucket.
  destruct (Z_lt_ge_dec bucket value) as [Hbelow | Hat_or_above].
  - rewrite Znth_replace_Znth_Diff by lia.
    pose proof (PreH13 bucket Hbucket) as Hold.
    assert (Hlt_old : Z.ltb bucket value = true) by
      (apply Z.ltb_lt; lia).
    assert (Hlt_new : Z.ltb bucket (value + 1) = true) by
      (apply Z.ltb_lt; lia).
    rewrite Hlt_old in Hold.
    rewrite Hlt_new.
    exact Hold.
  - destruct (Z.eq_dec bucket value) as [Hequal | Habove].
    + subst bucket.
      rewrite Znth_replace_Znth_Same by lia.
      pose proof (PreH13 value ltac:(lia)) as Hcurrent.
      pose proof (PreH13 (value - 1) ltac:(lia)) as Hprevious.
      assert (Hcurrent_raw : Z.ltb value value = false) by
        (apply Z.ltb_ge; lia).
      assert (Hprevious_done : Z.ltb (value - 1) value = true) by
        (apply Z.ltb_lt; lia).
      assert (Hcurrent_done : Z.ltb value (value + 1) = true) by
        (apply Z.ltb_lt; lia).
      rewrite Hcurrent_raw in Hcurrent.
      rewrite Hprevious_done in Hprevious.
      rewrite Hcurrent_done.
      rewrite Hcurrent, Hprevious.
      rewrite (counting_cumulative_end_step__histogram_cumulative
        input value) by lia.
      lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      pose proof (PreH13 bucket Hbucket) as Hold.
      assert (Hlt_old : Z.ltb bucket value = false) by
        (apply Z.ltb_ge; lia).
      assert (Hlt_new : Z.ltb bucket (value + 1) = false) by
        (apply Z.ltb_ge; lia).
      rewrite Hlt_old in Hold.
      rewrite Hlt_new.
      exact Hold.
Qed.

Lemma proof_of_sort_entail_wit_8_split_goal_2 : sort_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Diff by lia.
  replace (value + 1 - 1) with value by lia.
  rewrite Znth_replace_Znth_Same by lia.
  unfold CountingCumulativeState in PreH13.
  pose proof (PreH13 (value + 1) ltac:(lia)) as Hfollowing.
  pose proof (PreH13 value ltac:(lia)) as Hcurrent.
  pose proof (PreH13 (value - 1) ltac:(lia)) as Hprevious.
  assert (Hfollowing_raw : Z.ltb (value + 1) value = false) by
    (apply Z.ltb_ge; lia).
  assert (Hcurrent_raw : Z.ltb value value = false) by
    (apply Z.ltb_ge; lia).
  assert (Hprevious_done : Z.ltb (value - 1) value = true) by
    (apply Z.ltb_lt; lia).
  rewrite Hfollowing_raw in Hfollowing.
  rewrite Hcurrent_raw in Hcurrent.
  rewrite Hprevious_done in Hprevious.
  rewrite Hfollowing, Hcurrent, Hprevious.
  pose proof (counting_cumulative_end_bound__histogram_cumulative
    input (value + 1)) as Hbound.
  rewrite counting_cumulative_end_step__histogram_cumulative in Hbound by lia.
  rewrite counting_cumulative_end_step__histogram_cumulative in Hbound by lia.
  rewrite PreH4 in Hbound.
  replace (value + 1 - 1) with value in Hbound by lia.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_8_split_goal_3 : sort_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH6.
Qed.

Lemma proof_of_sort_entail_wit_8 : sort_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_sort_entail_wit_9 : sort_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvalue100 : value = 100) by lia.
  subst value.
  assert
    (Hinput_bounds :
      forall element, In element input -> 0 <= element < 100).
  { apply counting_index_bounds_to_In_bounds__placement_boundaries.
    intros index Hindex.
    apply PreH9.
    rewrite PreH4 in Hindex.
    exact Hindex. }
  destruct
    (counting_canonical_sorted_exists__placement_boundaries
      input Hinput_bounds)
    as [sorted [Hsorted_length [Hsorted_bounds Hsorted]]].
  assert
    (Hplacement :
      CountingPlacementProgress
        input positions_2 positions_2 output_mixed_2 sorted
        (Zlength input - 1)).
  { apply counting_placement_initial__placement_boundaries;
      assumption. }
  assert
    (Hpositive :
      Zlength input - 1 >= 0 ->
      1 <=
        Znth (Znth (Zlength input - 1) input 0) positions_2 0).
  { intros Hnonempty.
    assert
      (Hindex :
        0 <= Zlength input - 1 < Zlength input) by lia.
    assert
      (Helement_bounds :
        0 <= Znth (Zlength input - 1) input 0 < 100).
    { apply PreH9.
      lia. }
    assert
      (Helement_in :
        In (Znth (Zlength input - 1) input 0) input).
    { unfold Znth.
      apply nth_In.
      replace (length input) with (Z.to_nat (Zlength input)).
      - apply
          (proj1
            (Z2Nat.inj_lt
              (Zlength input - 1) (Zlength input)
              ltac:(lia) ltac:(lia))).
        lia.
      - rewrite Zlength_correct, Nat2Z.id.
        reflexivity. }
    pose proof
      (PreH13
        (Znth (Zlength input - 1) input 0) Helement_bounds)
      as Hposition.
    assert
      (Hltb :
        Z.ltb (Znth (Zlength input - 1) input 0) 100 = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hltb in Hposition.
    rewrite Hposition.
    apply counting_cumulative_positive_at_In__placement_boundaries;
      [lia | exact Helement_in]. }
  Exists output_mixed_2 positions_2 positions_2 sorted.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite <- PreH4; exact Hplacement).
    all: try (rewrite <- PreH4; exact Hpositive).
    all: try (intros index Hindex; apply PreH12; lia).
    all: try (intros index Hindex; apply Hsorted_bounds; lia).
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_1 : sort_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH17 i ltac:(lia)).
  specialize (PreH19 (Znth i input 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_2 : sort_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH17 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_3 : sort_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH17 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_10 : sort_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_3.
Qed.

Lemma proof_of_sort_entail_wit_11_split_goal_1 : sort_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same by lia.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_11_split_goal_2 : sort_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same by lia.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_11 : sort_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_11_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_12 : sort_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (new_positions :=
    replace_Znth (Znth i input 0)
      (Znth (Znth i input 0) positions_2 0 - 1) positions_2).
  set (new_write_index := Znth (Znth i input 0) new_positions 0).
  set (new_output :=
    replace_Znth new_write_index (Some (Znth i input 0)) output_mixed_2).
  pose proof
    (counting_placement_step__placement_transition
      n_pre input i output_mixed_2 bucket_ends_2 sorted_2 positions_2
      __default__App_option_Z ltac:(lia) PreH14 PreH15 PreH16 PreH18
      ltac:(lia) PreH21 PreH22 PreH23 PreH25 PreH7 PreH26) as Hstep.
  cbn zeta in Hstep.
  change
    ((forall bucket,
      0 <= bucket < 100 ->
      0 <= Znth bucket new_positions 0 <= n_pre) /\
    (i - 1 >= 0 ->
      1 <= Znth (Znth (i - 1) input 0) new_positions 0) /\
    (forall index,
      n_pre <= index < 100 ->
      Znth index new_output __default__App_option_Z = None) /\
    CountingPlacementProgress input new_positions bucket_ends_2 new_output
      sorted_2 (i - 1)) in Hstep.
  destruct Hstep as
    [Hnew_positions_bounds
      [Hnext_positive [Hnew_output_suffix Hnew_progress]]].
  Exists new_output bucket_ends_2 new_positions sorted_2.
  split_pure_spatial.
  - unfold new_output, new_write_index, new_positions.
    cancel (IntArray.full a_pre n_pre input).
    cancel (IntArray.mixed_full &( "output" ) 100
      (replace_Znth
        (Znth (Znth i input 0)
          (replace_Znth (Znth i input 0)
            (Znth (Znth i input 0) positions_2 0 - 1) positions_2) 0)
        (Some (Znth i input 0)) output_mixed_2)).
    cancel (IntArray.full &( "count" ) 100
      (replace_Znth (Znth i input 0)
        (Znth (Znth i input 0) positions_2 0 - 1) positions_2)).
  - split_pures.
    + dump_pre_spatial. exact PreH12.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial.
      unfold new_positions. rewrite Zlength_replace_Znth. exact PreH16.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial.
      unfold new_output. rewrite Zlength_replace_Znth. exact PreH18.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH21.
    + dump_pre_spatial. exact PreH22.
    + dump_pre_spatial. exact Hnew_positions_bounds.
    + dump_pre_spatial. exact Hnext_positive.
    + dump_pre_spatial. exact Hnew_output_suffix.
    + dump_pre_spatial. exact Hnew_progress.
Qed.

Lemma proof_of_sort_entail_wit_13 : sort_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = -1) by lia.
  subst i.
  assert
    (Hinput_bounds :
      forall element, In element input -> 0 <= element < 100).
  { apply counting_index_bounds_to_In_bounds__placement_boundaries.
    intros index Hindex.
    apply PreH11.
    rewrite PreH4 in Hindex.
    exact Hindex. }
  pose proof PreH16 as Hprogress.
  assert (Hsorted : CountingSorted input sorted_2).
  { unfold CountingPlacementProgress in Hprogress.
    exact (proj1 Hprogress). }
  assert
    (Hcomplete :
      forall index,
        0 <= index < Zlength input ->
        Znth index output_mixed None = Some (Znth index sorted_2 0)).
  { eapply counting_placement_complete__placement_boundaries;
      eassumption. }
  assert
    (Houtput_prefix :
      sublist 0 n_pre output_mixed = map (@Some Z) sorted_2).
  { apply counting_output_prefix__placement_boundaries.
    - rewrite PreH8.
      lia.
    - exact PreH5.
    - intros index Hindex.
      apply Hcomplete.
      lia. }
  Exists positions sorted_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_seg
        ( &( "output" ) ) n_pre 100 output_mixed).
    + dump_pre_spatial. lia.
    + rewrite Houtput_prefix.
      sep_apply_l_atomic
        (IntArray.mixed_seg_to_seg
          ( &( "output" ) ) 0 n_pre sorted_2).
      sep_apply_l_atomic
        (IntArray.mixed_seg_to_undef_seg
          ( &( "output" ) ) n_pre 100
          (sublist n_pre 100 output_mixed)).
      cancel (IntArray.full a_pre n_pre input).
      cancel (IntArray.full ( &( "count" ) ) 100 positions).
      cancel (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2).
      cancel (IntArray.undef_seg ( &( "output" ) ) n_pre 100).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_sort_entail_wit_14_split_goal_1 : sort_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply counting_copy_initial__copyback.
Qed.

Lemma proof_of_sort_entail_wit_14_split_goal_2 : sort_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_sort_entail_wit_14 : sort_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_14_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_15_split_goal_1 : sort_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  eapply counting_copy_step__copyback.
  - rewrite PreH4. lia.
  - rewrite PreH5, PreH4. reflexivity.
  - exact PreH12.
Qed.

Lemma proof_of_sort_entail_wit_15_split_goal_2 : sort_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH6.
Qed.

Lemma proof_of_sort_entail_wit_15 : sort_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_15_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_16_split_goal_1 : sort_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hlive : live = sorted_2).
  {
    eapply counting_copy_complete__copyback.
    - rewrite PreH5, PreH4. reflexivity.
    - rewrite PreH4. exact PreH12.
  }
  rewrite Hlive.
  dump_pre_spatial.
  exact PreH11.
Qed.

Lemma proof_of_sort_entail_wit_16_split_goal_spatial : sort_entail_wit_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (IntArray.seg_to_undef_seg (&( "output" )) 0 n_pre sorted_2).
  sep_apply_l_atomic
    (IntArray.undef_seg_merge_to_undef_full
       (&( "output" )) 0 n_pre 100 ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.full_to_undef_full (&( "count" )) 100 bucket_starts).
  simpl.
  cancel (IntArray.undef_full (&( "count" )) 100).
  replace ((&( "output" )) + 0) with (&( "output" )) by lia.
  cancel (IntArray.undef_full (&( "output" )) 100).
Qed.

Lemma proof_of_sort_entail_wit_16 : sort_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply
      (proof_of_sort_entail_wit_16_split_goal_spatial
         n_pre input i bucket_starts live sorted_2
         PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
         PreH7 PreH8 PreH9 PreH10 PreH11 PreH12).
  - Goal_apply
      ((ltac:(
          sep_apply
            (proof_of_sort_entail_wit_16_split_goal_1
               n_pre input i bucket_starts live sorted_2
               PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
               PreH7 PreH8 PreH9 PreH10 PreH11 PreH12);
          cancel)) :
        IntArray.seg (&( "output" )) 0 n_pre sorted_2 **
          (IntArray.undef_seg (&( "output" )) n_pre 100 **
           IntArray.full (&( "count" )) 100 bucket_starts)
        |-- “ CountingSorted input live ”).
Qed.

Lemma proof_of_sort_return_wit_1_split_goal_1 : sort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CountingSorted in PreH5.
  exact (proj2 PreH5).
Qed.

Lemma proof_of_sort_return_wit_1_split_goal_2 : sort_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CountingSorted in PreH5.
  exact (proj1 PreH5).
Qed.

Lemma proof_of_sort_return_wit_1 : sort_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_return_wit_1_split_goal_2.
Qed.
