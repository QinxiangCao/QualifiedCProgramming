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
From SimpleC.EE.LLM_bench.Algorithms.bucket_sort Require Import bucket_sort_goal.
From SimpleC.EE.LLM_bench.Algorithms.bucket_sort Require Import bucket_sort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib.
Local Open Scope sac.

Lemma proof_of_sort_safety_wit_17_split_goal_1 : sort_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize
    (PreH26 (Z.rem (Z.quot (Znth i current 0) exponent) 10) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_safety_wit_17_split_goal_2 : sort_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize
    (PreH26 (Z.rem (Z.quot (Znth i current 0) exponent) 10) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_safety_wit_17 : sort_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_sort_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_sort_safety_wit_21_split_goal_1 : sort_safety_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH18 digit ltac:(lia)) as Hcurrent_bound.
  pose proof (PreH18 (digit - 1) ltac:(lia)) as Hprevious_bound.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_safety_wit_21_split_goal_2 : sort_safety_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH18 digit ltac:(lia)) as Hcurrent_bound.
  pose proof (PreH18 (digit - 1) ltac:(lia)) as Hprevious_bound.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_safety_wit_21 : sort_safety_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_safety_wit_21_split_goal_1.
  - Goal_apply proof_of_sort_safety_wit_21_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_1_split_goal_1 : sort_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixMaximum.
  split.
  - exists 0.
    split; [lia | reflexivity].
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    lia.
Qed.

Lemma proof_of_sort_entail_wit_1_split_goal_2 : sort_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_1_split_goal_3 : sort_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH5 0 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_1_split_goal_4 : sort_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH5 0 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_1 : sort_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_sort_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_sort_entail_wit_2_1_split_goal_1 : sort_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply prefix_maximum_extend_greater__maximum_pass_entry;
    eauto; lia.
Qed.

Lemma proof_of_sort_entail_wit_2_1_split_goal_2 : sort_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_2_2_split_goal_1 : sort_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply prefix_maximum_extend_bounded__maximum_pass_entry; eauto.
Qed.

Lemma proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_sort_entail_wit_3_split_goal_1 : sort_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold RadixPassState, RadixLowerDigitsOrdered.
  split.
  - apply Permutation_refl.
  - intros left right Hbounds.
    rewrite !Z.mod_1_r.
    lia.
Qed.

Lemma proof_of_sort_entail_wit_3_split_goal_2 : sort_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DecimalExponent.
  exists 0.
  cbn.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_3_split_goal_3 : sort_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with n_pre in PreH10 by lia.
  exact PreH10.
Qed.

Lemma proof_of_sort_entail_wit_3_split_goal_4 : sort_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_3_split_goal_5 : sort_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_3 : sort_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_sort_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_sort_entail_wit_3_split_goal_5.
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_1 : sort_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_2 : sort_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH11.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_3 : sort_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_4 : sort_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply decimal_exponent_active_bound__maximum_pass_entry; eauto.
Qed.

Lemma proof_of_sort_entail_wit_4_split_goal_5 : sort_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_entail_wit_4 : sort_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_sort_entail_wit_4_split_goal_5.
Qed.

Lemma proof_of_sort_entail_wit_5_split_goal_1 : sort_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_5 : sort_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_sort_entail_wit_6 : sort_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (digit_2 = 10) by lia.
  subst digit_2.
  Exists zero_prefix current_2.
  split_pure_spatial.
  - rewrite H.
    rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full (&("count")) 0 10 zero_prefix).
    replace ((&("count")) + 0 * sizeof (INT)) with (&("count")) by lia.
    replace (10 - 0) with 10 by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | lia].
    all: apply
      (digit_histogram_prefix_zero__count_zero_init
         current_2 exponent zero_prefix).
    all: intros digit Hdigit.
    all: apply PreH16.
    all: lia.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_1 : sort_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hzero : forall d, _ -> Znth d ?counts 0 = 0
    |- context [Znth ?digit ?counts 0] =>
      rewrite (Hzero digit) by lia
  end.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_2 : sort_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hrange : forall k : Z, _ ->
      0 <= Znth k ?values 0 /\ Znth k ?values 0 <= _
    |- 0 <= Znth ?index ?values 0 /\ Znth ?index ?values 0 <= _ =>
      apply Hrange; lia
  end.
Qed.

Lemma proof_of_sort_entail_wit_7_split_goal_3 : sort_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hrange : forall k : Z, _ ->
      0 <= Znth k ?values 0 /\ Znth k ?values 0 <= _
    |- 0 <= Znth ?index ?values 0 /\ Znth ?index ?values 0 <= _ =>
      apply Hrange; lia
  end.
Qed.

Lemma proof_of_sort_entail_wit_7 : sort_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_sort_entail_wit_8_split_goal_1 : sort_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH25 i ltac:(lia)).
  assert (0 <= Z.quot (Znth i current 0) exponent) as Hquot
    by (apply Z.quot_pos; lia).
  pose proof
    (Z.rem_bound_pos_pos (Z.quot (Znth i current 0) exponent) 10
      ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_8_split_goal_2 : sort_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH25 i ltac:(lia)).
  assert (0 <= Z.quot (Znth i current 0) exponent) as Hquot
    by (apply Z.quot_pos; lia).
  pose proof
    (Z.rem_bound_pos_pos (Z.quot (Znth i current 0) exponent) 10
      ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_8 : sort_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_8_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_9_split_goal_1 : sort_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH25 i ltac:(lia)).
  assert
    (Hdigit :
      Z.rem (Z.quot (Znth i current_2 0) exponent) 10 =
      RadixDigit (Znth i current_2 0) exponent).
  {
    unfold RadixDigit.
    rewrite Z.quot_div_nonneg by lia.
    rewrite Z.rem_mod_nonneg by (try lia; apply Z.div_pos; lia).
    reflexivity.
  }
  rewrite Hdigit in PreH1, PreH2 |- *.
  eapply digit_histogram_prefix_step__histogram_update; eauto; lia.
Qed.

Lemma proof_of_sort_entail_wit_9_split_goal_2 : sort_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_9 : sort_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_1 : sort_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with n_pre in * by lia.
  assumption.
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_2 : sort_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH16 digit H).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_3 : sort_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH15 k_2 H).
Qed.

Lemma proof_of_sort_entail_wit_10_split_goal_4 : sort_entail_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH14 k H).
Qed.

Lemma proof_of_sort_entail_wit_10 : sort_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_sort_entail_wit_10_split_goal_4.
Qed.

Lemma proof_of_sort_entail_wit_11 : sort_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists histogram_2 histogram_2 current_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre current_2).
    cancel (IntArray.full ( &( "count" ) ) 10 histogram_2).
    cancel (IntArray.undef_full ( &( "output" ) ) 1000).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (apply digit_prefix_totals_init__prefix_totals; assumption).
Qed.

Lemma proof_of_sort_entail_wit_12 : sort_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (digit_prefix_totals_step__prefix_totals
      histogram_2 totals_2 digit PreH6 PreH7 ltac:(lia) PreH23)
    as Hprefix_step.
  pose proof
    (digit_histogram_prefix_mass_bound__prefix_totals
      current_2 exponent n_pre histogram_2 digit
      ltac:(lia) PreH6 PreH22 ltac:(lia))
    as Hprefix_mass.
  assert (Hupdated_bounds :
    forall index,
      0 <= index < 10 ->
      0 <=
        Znth index
          (replace_Znth digit
            (Znth digit totals_2 0 + Znth (digit - 1) totals_2 0)
            totals_2)
          0 <= n_pre).
  {
    intros index Hindex.
    destruct (Z.eq_dec index digit) as [Heq | Hneq].
    - subst index.
      pose proof (Hprefix_step digit ltac:(lia)) as Hupdated_prefix.
      pose proof (proj1 Hupdated_prefix ltac:(lia)) as Hupdated_value.
      rewrite Znth_replace_Znth_Same in Hupdated_value by lia.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite <- Hupdated_value in Hprefix_mass.
      exact Hprefix_mass.
    - rewrite Znth_replace_Znth_Diff by lia.
      apply PreH18.
      exact Hindex.
  }
  Exists
    (replace_Znth digit
      (Znth digit totals_2 0 + Znth (digit - 1) totals_2 0)
      totals_2)
    histogram_2 current_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre current_2).
    cancel
      (IntArray.full ( &( "count" ) ) 10
        (replace_Znth digit
          (Znth digit totals_2 0 + Znth (digit - 1) totals_2 0)
          totals_2)).
    cancel (IntArray.undef_full ( &( "output" ) ) 1000).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite Zlength_replace_Znth; assumption).
Qed.

Lemma proof_of_sort_entail_wit_13 : sort_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (digit_2 = 10) by lia.
  subst digit_2.
  Exists totals histogram_2 current_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre current_2).
    cancel (IntArray.full ( &( "count" ) ) 10 totals).
    cancel (IntArray.undef_full ( &( "output" ) ) 1000).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (intros index Hindex;
      pose proof (PreH17 index Hindex) as Hhistogram_bound;
      pose proof (PreH18 index Hindex) as Htotals_bound;
      tauto).
Qed.

Lemma proof_of_sort_entail_wit_14 : sort_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (mixed_output := repeat (None : option Z) (Z.to_nat 1000)).
  assert (DigitHistogramPrefix current_2 exponent (Zlength current_2)
            histogram_2) as Hhistogram_length.
  {
    rewrite PreH4. exact PreH18.
  }
  assert (BucketPlacementProgress current_2 exponent (Zlength current_2)
            histogram_2 endpoints mixed_output) as Hprogress_initial.
  {
    unfold mixed_output.
    eapply bucket_placement_initial__stable_placement;
      eassumption.
  }
  assert (Zlength mixed_output = 1000) as Hmixed_length.
  {
    unfold mixed_output. rewrite Zlength_correct, repeat_length. lia.
  }
  assert (forall k,
    0 <= k < n_pre ->
    ((0 <= Znth k current_2 0 <= 999999999 /\
      0 <= ((Znth k current_2 0 ÷ exponent) % 10)) /\
     ((Znth k current_2 0 ÷ exponent) % 10) < 10))
    as Hcurrent_digits.
  {
    intros k Hk.
    pose proof (PreH13 k Hk) as Hvalue.
    pose proof (c_radix_digit_range__stable_placement
      (Znth k current_2 0) exponent ltac:(lia) ltac:(lia)) as Hrange.
    lia.
  }
  assert (forall k,
    0 <= k <= n_pre - 1 ->
    1 <= Znth (((Znth k current_2 0 ÷ exponent) % 10)) endpoints 0 <=
      n_pre) as Hinitial_counters.
  {
    intros k Hk.
    pose proof (PreH13 k ltac:(lia)) as Hk_facts.
    assert (0 <= Znth k current_2 0) as Hk_nonneg by lia.
    assert (0 <= ((Znth k current_2 0 ÷ exponent) % 10) < 10)
      as Hk_c_digit.
    {
      pose proof (c_radix_digit_range__stable_placement
        (Znth k current_2 0) exponent Hk_nonneg ltac:(lia)) as Hrange.
      exact Hrange.
    }
    assert (RadixDigit (Znth k current_2 0) exponent =
            ((Znth k current_2 0 ÷ exponent) % 10)) as Hk_bridge.
    {
      apply radix_digit_c_bridge__stable_placement; lia.
    }
    split.
    - assert (1 <= Znth (RadixDigit (Znth k current_2 0) exponent)
                  endpoints 0) as Hpositive.
      {
        eapply bucket_progress_counter_for_index__stable_placement
          with (source := current_2) (exponent := exponent)
               (remaining := Zlength current_2)
               (histogram := histogram_2)
               (mixed_output := mixed_output).
        + exact PreH5.
        + exact Hhistogram_length.
        + exact Hprogress_initial.
        + rewrite PreH4. lia.
        + lia.
        + rewrite Hk_bridge. exact Hk_c_digit.
      }
      rewrite Hk_bridge in Hpositive. exact Hpositive.
    - pose proof (PreH14 ((Znth k current_2 0 ÷ exponent) % 10)
        Hk_c_digit) as Hcounter_bound.
      lia.
  }
  Exists mixed_output endpoints histogram_2 current_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.undef_full_to_mixed_full ( &( "output" ) ) 1000).
    cancel (IntArray.full a_pre n_pre current_2).
    cancel (IntArray.full ( &( "count" ) ) 10 endpoints).
    unfold mixed_output.
    cancel (IntArray.mixed_full ( &( "output" ) ) 1000
      (repeat (None : option Z) (Z.to_nat 1000))).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (replace ((n_pre - 1) + 1) with (Zlength current_2)
      by lia; assumption).
Qed.

Lemma proof_of_sort_entail_wit_15_split_goal_1 : sort_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH29 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_15_split_goal_2 : sort_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH29 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_15_split_goal_3 : sort_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH27 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_15_split_goal_4 : sort_entail_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH27 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_entail_wit_15 : sort_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_15_split_goal_3.
  - Goal_apply proof_of_sort_entail_wit_15_split_goal_4.
Qed.

Lemma proof_of_sort_entail_wit_16_split_goal_1 : sort_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same by lia.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_16_split_goal_2 : sort_entail_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same by lia.
  lia.
Qed.

Lemma proof_of_sort_entail_wit_16 : sort_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_16_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_16_split_goal_2.
Qed.

Lemma proof_of_sort_entail_wit_17 : sort_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (digit := ((Znth i current_2 0 / exponent) mod 10)).
  set (next_counters :=
    replace_Znth digit (Znth digit counters_2 0 - 1) counters_2).
  set (write_index := Znth digit next_counters 0).
  set (next_output :=
    replace_Znth write_index (Some (Znth i current_2 0)) mixed_output_2).
  assert (DigitHistogramPrefix current_2 exponent (Zlength current_2)
            histogram_2) as Hhistogram_length.
  {
    rewrite PreH19. exact PreH37.
  }
  assert (0 <= Znth i current_2 0) as Hcurrent_nonneg.
  {
    specialize (PreH31 i ltac:(lia)). lia.
  }
  assert (digit = ((Znth i current_2 0 ÷ exponent) % 10))
    as Hdigit_bridge.
  {
    unfold digit.
    apply radix_digit_c_bridge__stable_placement; lia.
  }
  assert (0 <= digit < 10) as Hdigit_range.
  {
    rewrite Hdigit_bridge. split; assumption.
  }
  assert (1 <= Znth digit counters_2 0) as Hcurrent_counter_positive.
  {
    rewrite Hdigit_bridge. exact PreH9.
  }
  assert (BucketPlacementProgress current_2 exponent i histogram_2
            next_counters next_output) as Hprogress_next.
  {
    unfold next_counters, next_output, write_index, digit.
    eapply bucket_placement_step__stable_placement.
    - exact PreH20.
    - exact PreH21.
    - rewrite PreH19. lia.
    - rewrite (radix_digit_c_bridge__stable_placement
        (Znth i current_2 0) exponent Hcurrent_nonneg ltac:(lia)).
      exact (conj PreH7 PreH8).
    - exact Hhistogram_length.
    - exact PreH38.
    - rewrite (radix_digit_c_bridge__stable_placement
        (Znth i current_2 0) exponent Hcurrent_nonneg ltac:(lia)).
      split; assumption.
  }
  assert (forall bucket,
    0 <= bucket < 10 ->
    0 <= Znth bucket next_counters 0 <= n_pre) as Hcounter_bounds_next.
  {
    intros bucket Hbucket.
    destruct (Z.eq_dec bucket digit) as [Heq | Hneq].
    - subst bucket.
      unfold next_counters.
      rewrite Znth_replace_Znth_Same by lia.
      specialize (PreH32 digit Hdigit_range).
      lia.
    - unfold next_counters.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite PreH21; lia).
      specialize (PreH32 bucket Hbucket).
      lia.
  }
  assert (forall k,
    0 <= k <= i - 1 ->
    1 <= Znth (((Znth k current_2 0 ÷ exponent) % 10))
            next_counters 0 <= n_pre) as Hremaining_counters.
  {
    intros k Hk.
    pose proof (PreH31 k ltac:(lia)) as Hk_facts.
    assert (0 <= Znth k current_2 0) as Hk_nonneg by lia.
    assert (0 <= ((Znth k current_2 0 ÷ exponent) % 10) < 10)
      as Hk_c_digit by lia.
    assert (RadixDigit (Znth k current_2 0) exponent =
            ((Znth k current_2 0 ÷ exponent) % 10)) as Hk_bridge.
    {
      apply radix_digit_c_bridge__stable_placement; lia.
    }
    split.
    - assert (1 <= Znth (RadixDigit (Znth k current_2 0) exponent)
                  next_counters 0) as Hpositive.
      {
        eapply bucket_progress_counter_for_index__stable_placement
          with (source := current_2) (exponent := exponent)
               (remaining := i) (histogram := histogram_2)
               (mixed_output := next_output).
        + exact PreH20.
        + exact Hhistogram_length.
        + exact Hprogress_next.
        + lia.
        + rewrite PreH19. lia.
        + rewrite Hk_bridge. exact Hk_c_digit.
      }
      rewrite Hk_bridge in Hpositive. exact Hpositive.
    - specialize (Hcounter_bounds_next
        ((Znth k current_2 0 ÷ exponent) % 10) Hk_c_digit).
      lia.
  }
  assert (Zlength next_counters = 10) as Hnext_counters_length.
  {
    unfold next_counters. rewrite Zlength_replace_Znth. exact PreH21.
  }
  assert (Zlength next_output = 1000) as Hnext_output_length.
  {
    unfold next_output. rewrite Zlength_replace_Znth. exact PreH22.
  }
  assert (forall bucket,
    0 <= bucket < 10 ->
    (0 <= Znth bucket histogram_2 0 <= n_pre /\
     0 <= Znth bucket next_counters 0) /\
    Znth bucket next_counters 0 <= n_pre) as Hhistogram_counter_bounds_next.
  {
    intros bucket Hbucket.
    pose proof (PreH32 bucket Hbucket) as Hold_bounds.
    pose proof (Hcounter_bounds_next bucket Hbucket) as Hnew_bounds.
    lia.
  }
  Exists next_output next_counters histogram_2 current_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre current_2).
    unfold next_output, write_index, next_counters.
    rewrite Hdigit_bridge.
    cancel (IntArray.full ( &( "count" ) ) 10
      (replace_Znth (((Znth i current_2 0 ÷ exponent) % 10))
        (Znth (((Znth i current_2 0 ÷ exponent) % 10)) counters_2 0 - 1)
        counters_2)).
    cancel (IntArray.mixed_full ( &( "output" ) ) 1000
      (replace_Znth
        (Znth (((Znth i current_2 0 ÷ exponent) % 10))
          (replace_Znth (((Znth i current_2 0 ÷ exponent) % 10))
            (Znth (((Znth i current_2 0 ÷ exponent) % 10)) counters_2 0 - 1)
            counters_2) 0)
        (Some (Znth i current_2 0)) mixed_output_2)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite Zlength_replace_Znth; assumption).
    all: try (replace ((i - 1) + 1) with i by lia; assumption).
Qed.

Lemma proof_of_sort_entail_wit_18 : sort_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = -1) as Hi_done by lia.
  assert (DigitHistogramPrefix current_2 exponent (Zlength current_2)
            histogram_2) as Hhistogram_length.
  {
    rewrite PreH5. exact PreH23.
  }
  assert (forall k,
    0 <= k < Zlength current_2 ->
    (0 <= Znth k current_2 0 <= 999999999 /\
     0 <= RadixDigit (Znth k current_2 0) exponent < 10))
    as Hcurrent_math.
  {
    intros k Hk.
    pose proof (PreH17 k ltac:(rewrite PreH5 in Hk; exact Hk)) as Hfacts.
    assert (RadixDigit (Znth k current_2 0) exponent =
            ((Znth k current_2 0 ÷ exponent) % 10)) as Hbridge.
    {
      apply radix_digit_c_bridge__stable_placement; lia.
    }
    rewrite Hbridge. lia.
  }
  assert (BucketPlacementProgress current_2 exponent 0 histogram_2 counters
            mixed_output) as Hprogress_done.
  {
    replace 0 with (i + 1) by lia. exact PreH24.
  }
  pose proof (bucket_placement_complete__stable_placement
    current_2 exponent histogram_2 counters mixed_output
    PreH6 ltac:(rewrite PreH5; lia) Hhistogram_length
    ltac:(intros k Hk; specialize (Hcurrent_math k Hk); tauto)
    Hprogress_done) as [Hbucket_starts Hmixed_prefix].
  pose proof (radix_stable_output_properties__stable_placement
    current_2 exponent 0 999999999 Hcurrent_math)
    as [Houtput_length [Houtput_permutation Houtput_bounds]].
  set (pass_output := RadixStableOutput current_2 exponent).
  assert (Zlength pass_output = n_pre) as Hpass_output_length.
  {
    unfold pass_output. rewrite Houtput_length. exact PreH5.
  }
  assert (forall k,
    0 <= k < n_pre ->
    ((0 <= Znth k current_2 0 <= 999999999 /\
      0 <= Znth k pass_output 0) /\
     Znth k pass_output 0 <= 999999999)) as Hcurrent_output_bounds.
  {
    intros k Hk.
    pose proof (PreH17 k Hk) as Hcurrent_bound.
    pose proof (Houtput_bounds k ltac:(rewrite PreH5; exact Hk))
      as Houtput_bound.
    destruct Hcurrent_bound as [[[Hcurrent_lo Hcurrent_hi] Hdigit_lo] Hdigit_hi].
    destruct Houtput_bound as [Houtput_lo Houtput_hi].
    unfold pass_output. repeat split; lia.
  }
  assert (StableDigitPass current_2 pass_output exponent)
    as Hstable_pass by (unfold StableDigitPass, pass_output; reflexivity).
  assert (sublist 0 n_pre mixed_output = map (@Some Z) pass_output)
    as Hmixed_prefix_n.
  {
    unfold pass_output. rewrite <- PreH5. exact Hmixed_prefix.
  }
  Exists pass_output counters histogram_2 current_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_seg
        ( &( "output" ) ) n_pre 1000 mixed_output).
    + dump_pre_spatial. lia.
    + rewrite Hmixed_prefix_n.
      sep_apply_l_atomic
        (IntArray.mixed_seg_to_seg
          ( &( "output" ) ) 0 n_pre pass_output).
      sep_apply_l_atomic
        (IntArray.mixed_seg_to_undef_seg
          ( &( "output" ) ) n_pre 1000
          (sublist n_pre 1000 mixed_output)).
      cancel (IntArray.full a_pre n_pre current_2).
      cancel (IntArray.full ( &( "count" ) ) 10 counters).
      cancel (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output).
      cancel (IntArray.undef_seg ( &( "output" ) ) n_pre 1000).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_sort_entail_wit_19 : sort_entail_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcopy :
    RadixCopyPrefix current_2 pass_output_2 current_2 0).
  { apply radix_copy_prefix_zero__copy_back. }
  assert (Hbounds : forall k,
    0 <= k < n_pre ->
    (((((0 <= Znth k current_2 0 /\
         Znth k current_2 0 <= 999999999) /\
        0 <= Znth k pass_output_2 0) /\
       Znth k pass_output_2 0 <= 999999999) /\
      0 <= Znth k current_2 0) /\
     Znth k current_2 0 <= 999999999)).
  {
    intros k Hk.
    specialize (PreH14 k Hk).
    tauto.
  }
  Exists current_2 pass_output_2 bucket_starts_2 current_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre current_2).
    cancel (IntArray.full (&( "count" )) 10 bucket_starts_2).
    cancel (IntArray.seg (&( "output" )) 0 n_pre pass_output_2).
    cancel (IntArray.undef_seg (&( "output" )) n_pre 1000).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_sort_entail_wit_20 : sort_entail_wit_20.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  set (working := replace_Znth i (Znth i pass_output_2 0) working_2).
  assert (Hworking_length : Zlength working = n_pre).
  {
    unfold working.
    rewrite Zlength_replace_Znth.
    exact PreH8.
  }
  assert (Hcopy :
    RadixCopyPrefix current_2 pass_output_2 working (i + 1)).
  {
    unfold working.
    apply radix_copy_prefix_step__copy_back.
    - lia.
    - lia.
    - exact PreH22.
  }
  assert (Hbounds : forall k,
    0 <= k < n_pre ->
    (((((0 <= Znth k current_2 0 /\
         Znth k current_2 0 <= 999999999) /\
        0 <= Znth k pass_output_2 0) /\
       Znth k pass_output_2 0 <= 999999999) /\
      0 <= Znth k working 0) /\
     Znth k working 0 <= 999999999)).
  {
    intros k Hk.
    specialize (PreH17 k Hk) as
      [[[[[Hcurrent_lower Hcurrent_upper]
           Hpass_lower] Hpass_upper]
         Hworking_lower] Hworking_upper].
    assert (Hupdated :
      0 <= Znth k working 0 /\
      Znth k working 0 <= 999999999).
    {
      unfold working.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      - subst k.
        rewrite Znth_replace_Znth_Same by lia.
        tauto.
      - rewrite Znth_replace_Znth_Diff by lia.
        tauto.
    }
    tauto.
  }
  Exists working pass_output_2 bucket_starts_2 current_2.
  split_pure_spatial.
  - unfold working.
    cancel (IntArray.full a_pre n_pre
      (replace_Znth i (Znth i pass_output_2 0) working_2)).
    cancel (IntArray.seg (&( "output" )) 0 n_pre pass_output_2).
    cancel (IntArray.full (&( "count" )) 10 bucket_starts_2).
    cancel (IntArray.undef_seg (&( "output" )) n_pre 1000).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_sort_entail_wit_21_split_goal_1 : sort_entail_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hworking : working = pass_output_2).
  {
    apply (proj2 (list_eq_ext working pass_output_2 0)).
    split.
    - lia.
    - intros index Hindex.
      apply (proj1 PreH22). lia.
  }
  subst working.
  unfold RadixPassState in *.
  destruct PreH20 as [Hpermutation Hordered].
  split.
  - eapply Permutation_trans.
    + exact Hpermutation.
    + exact
        (stable_digit_pass_permutation__pass_transition
           current pass_output_2 exponent PreH21).
  - eapply stable_digit_pass_next_order__pass_transition; eauto; lia.
Qed.

Lemma proof_of_sort_entail_wit_21_split_goal_2 : sort_entail_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply decimal_exponent_next__pass_transition; assumption.
Qed.

Lemma proof_of_sort_entail_wit_21_split_goal_3 : sort_entail_wit_21_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros index Hindex.
  specialize (PreH17 index Hindex).
  tauto.
Qed.

Lemma proof_of_sort_entail_wit_21_split_goal_4 : sort_entail_wit_21_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sort_entail_wit_21_split_goal_spatial : sort_entail_wit_21_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (IntArray.seg_to_undef_seg (&( "output" )) 0 n_pre pass_output_2).
  sep_apply_l_atomic
    (IntArray.undef_seg_merge_to_undef_full
       (&( "output" )) 0 n_pre 1000 ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.full_to_undef_full (&( "count" )) 10 bucket_starts).
  simpl.
  cancel (IntArray.undef_full (&( "count" )) 10).
  replace ((&( "output" )) + 0) with (&( "output" )) by lia.
  cancel (IntArray.undef_full (&( "output" )) 1000).
Qed.

Lemma proof_of_sort_entail_wit_21 : sort_entail_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_21_split_goal_spatial.
  - Goal_apply
      ((ltac:(
          sep_apply
            (proof_of_sort_entail_wit_21_split_goal_1
               n_pre input i exponent max_value working pass_output_2
               bucket_starts current
               PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
               PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
               PreH18 PreH19 PreH20 PreH21 PreH22);
          cancel)) :
        IntArray.full (&( "count" )) 10 bucket_starts **
          (IntArray.seg (&( "output" )) 0 n_pre pass_output_2 **
           IntArray.undef_seg (&( "output" )) n_pre 1000)
        |-- “ RadixPassState input working (exponent * 10) ”).
  - Goal_apply
      (proof_of_sort_entail_wit_21_split_goal_2
         n_pre input i exponent max_value working pass_output_2
         bucket_starts current
         PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
         PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
         PreH20 PreH21 PreH22).
  - Goal_apply
      (proof_of_sort_entail_wit_21_split_goal_3
         n_pre input i exponent max_value working pass_output_2
         bucket_starts current
         PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
         PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
         PreH20 PreH21 PreH22).
  - Goal_apply
      (proof_of_sort_entail_wit_21_split_goal_4
         n_pre input i exponent max_value working pass_output_2
         bucket_starts current
         PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
         PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
         PreH20 PreH21 PreH22).
Qed.

Lemma proof_of_sort_entail_wit_22_split_goal_1 : sort_entail_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13. assumption.
Qed.

Lemma proof_of_sort_entail_wit_22_split_goal_2 : sort_entail_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH12. assumption.
Qed.

Lemma proof_of_sort_entail_wit_22 : sort_entail_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply
      (proof_of_sort_entail_wit_22_split_goal_1
         n_pre input pass_output max_value exponent
         PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
         PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16).
  - Goal_apply
      (proof_of_sort_entail_wit_22_split_goal_2
         n_pre input pass_output max_value exponent
         PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
         PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16).
Qed.

Lemma proof_of_sort_entail_wit_23_split_goal_1 : sort_entail_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (radix_pass_state_final_increasing__final_result
    input current n_pre exponent max_value).
  - exact PreH4.
  - exact PreH5.
  - lia.
  - exact PreH6.
  - exact PreH1.
  - intros index Hindex.
    exact (proj1 (PreH11 index Hindex)).
  - exact PreH12.
  - exact PreH14.
Qed.

Lemma proof_of_sort_entail_wit_23_split_goal_2 : sort_entail_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold RadixPassState in PreH14.
  tauto.
Qed.

Lemma proof_of_sort_entail_wit_23_split_goal_3 : sort_entail_wit_23_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_sort_entail_wit_23 : sort_entail_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_entail_wit_23_split_goal_1.
  - Goal_apply proof_of_sort_entail_wit_23_split_goal_2.
  - Goal_apply proof_of_sort_entail_wit_23_split_goal_3.
Qed.

Lemma proof_of_sort_return_wit_1_split_goal_1 : sort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply increasing_short_list__final_result.
  lia.
Qed.

Lemma proof_of_sort_return_wit_1_split_goal_2 : sort_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(apply Permutation_refl).
Qed.

Lemma proof_of_sort_return_wit_1 : sort_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_return_wit_1_split_goal_2.
Qed.
