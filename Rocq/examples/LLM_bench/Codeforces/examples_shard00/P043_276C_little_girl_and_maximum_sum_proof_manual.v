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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P043_276C_little_girl_and_maximum_sum_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P043_276C_little_girl_and_maximum_sum_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P043_276C_little_girl_and_maximum_sum_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH25 (Znth i rights 0) ltac:(lia)) as Hbounds.
  destruct Hbounds as [Hlower Hupper].
  destruct (Z.eq_dec (Znth i rights 0) (Znth i lefts 0 - 1)) as [Heq | Hneq].
  - rewrite Heq.
    rewrite Heq in Hlower, Hupper.
    rewrite Znth_replace_Znth_Same by
      (unfold DifferencePrefix in PreH24; lia).
    dump_pre_spatial. int_auto.
  - rewrite Znth_replace_Znth_Diff by
      (unfold DifferencePrefix in PreH24; lia).
    dump_pre_spatial. int_auto.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH25 (Znth i rights 0) ltac:(lia)) as Hbounds.
  destruct Hbounds as [Hlower Hupper].
  destruct (Z.eq_dec (Znth i rights 0) (Znth i lefts 0 - 1)) as [Heq | Hneq].
  - rewrite Heq.
    rewrite Heq in Hlower, Hupper.
    rewrite Znth_replace_Znth_Same by
      (unfold DifferencePrefix in PreH24; lia).
    dump_pre_spatial. int_auto.
  - rewrite Znth_replace_Znth_Diff by
      (unfold DifferencePrefix in PreH24; lia).
    dump_pre_spatial. int_auto.
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_app_left__dot_product_accumulation by lia.
  pose proof (PreH24 i ltac:(lia)) as Hvalue.
  pose proof (PreH25 i ltac:(lia)) as Hfrequency.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_app_left__dot_product_accumulation by lia.
  pose proof (PreH24 i ltac:(lia)) as Hvalue.
  pose proof (PreH25 i ltac:(lia)) as Hfrequency.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_app_left__dot_product_accumulation by lia.
  pose proof (PreH24 i ltac:(lia)) as Hvalue.
  pose proof (PreH25 i ltac:(lia)) as Hfrequency.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_app_left__dot_product_accumulation by lia.
  pose proof (PreH24 i ltac:(lia)) as Hvalue.
  pose proof (PreH25 i ltac:(lia)) as Hfrequency.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold repeat_Z.
  rewrite Znth_repeat.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold repeat_Z.
  apply DifferencePrefix_zero__difference_initialization.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH12.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  specialize (PreH7 k_2 ltac:(lia)).
  rewrite <- PreH8 in PreH7.
  exact PreH7.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  specialize (PreH18 i ltac:(lia)).
  specialize (PreH19 i ltac:(lia)).
  destruct PreH18 as [[Hleft_nonneg Hleft_right] Hright_bound].
  destruct PreH19 as [Hleft_repr Hright_repr].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  specialize (PreH18 i ltac:(lia)).
  specialize (PreH19 i ltac:(lia)).
  destruct PreH18 as [[Hleft_nonneg Hleft_right] Hright_bound].
  destruct PreH19 as [Hleft_repr Hright_repr].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  specialize (PreH18 i ltac:(lia)).
  specialize (PreH19 i ltac:(lia)).
  destruct PreH18 as [[Hleft_nonneg Hleft_right] Hright_bound].
  destruct PreH19 as [Hleft_repr Hright_repr].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  specialize (PreH18 i ltac:(lia)).
  specialize (PreH19 i ltac:(lia)).
  destruct PreH18 as [[Hleft_nonneg Hleft_right] Hright_bound].
  destruct PreH19 as [Hleft_repr Hright_repr].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH21 i ltac:(lia)) as Hquery.
  destruct Hquery as [Hleft Hright].
  rewrite (Znth_indep queries i __default__Prod_Z_Z (0, 0)) in
    Hleft, Hright by lia.
  eapply DifferencePrefix_query_step__query_difference_update.
  - exact PreH24.
  - lia.
  - exact Hleft.
  - lia.
  - lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH17 k_4 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply DifferencePrefix_complete_to_CoveragePrefixState_one__coverage_prefix.
  - lia.
  - intros j Hj.
    rewrite <- (Znth_indep queries j __default__Prod_Z_Z (0, 0))
      by exact Hj.
    apply PreH12. rewrite PreH4. exact Hj.
  - replace i with q_pre in PreH16 by lia.
    rewrite PreH4 in PreH16.
    exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(eauto || lia || nia || int_auto).
  apply PreH13. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(eauto || lia || nia || int_auto).
  apply PreH12. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(eauto || lia || nia || int_auto).
  apply PreH11. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply CoveragePrefixState_step__coverage_prefix.
  - intros j Hj.
    rewrite <- (Znth_indep queries j __default__Prod_Z_Z (0, 0))
      by exact Hj.
    apply PreH12. rewrite PreH4. exact Hj.
  - lia.
  - exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  pose proof PreH16 as Hstate.
  pose proof Hstate as Hstate_parts.
  unfold CoveragePrefixState in Hstate_parts.
  destruct Hstate_parts as [Hdiff_len _].
  Exists (sublist n_pre (n_pre + 1) diff_data)
         (sublist 0 n_pre diff_data).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.full_split_to_full diff n_pre (n_pre + 1) diff_data).
    + dump_pre_spatial. lia.
    + replace (n_pre + 1 - n_pre) with 1 by lia.
      cancel.
  - repeat split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite Zlength_sublist by lia; lia).
    all: try (apply CoveragePrefixState_complete_to_CoverageProfile__coverage_prefix;
              exact Hstate).
    all: try (apply CoverageProfile_bounds__coverage_prefix with
                (queries := queries) (n := n_pre);
              [exact PreH4 |
               apply CoveragePrefixState_complete_to_CoverageProfile__coverage_prefix;
               exact Hstate]).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH18; exact H.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply Permutation_pointwise_bounds__sorting_setup
    with (input := values) (lo := 1) (hi := 200000).
  - intros i Hi.
    apply PreH13; lia.
  - exact PreH1.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH14; exact H.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH13; exact H.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  - Exists tail_2 sorted frequencies_2 values_sorted_2.
    split_pure_spatial.
    + sep_apply_r_atomic
        (Int64Array.full_merge_to_full diff n_pre (n_pre + 1)
          sorted tail_2).
      * dump_pre_spatial; lia.
      * replace (n_pre + 1 - n_pre) with 1 by lia.
        cancel (Int64Array.full diff n_pre sorted).
        cancel (Int64Array.full
          (diff + n_pre * sizeof(INT64)) 1 tail_2).
        cancel (Int64Array.full a_pre n_pre values_sorted_2).
        cancel (IntArray.full left_pre q_pre lefts).
        cancel (IntArray.full right_pre q_pre rights).
    + split_pures; dump_pre_spatial; try lia; try assumption.
      intros k Hk.
      eapply Permutation_pointwise_bounds__sorting_setup
        with (input := frequencies_2) (lo := 0) (hi := q_pre).
      * intros j Hj. apply PreH22; lia.
      * exact PreH1.
      * lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  - Exists tail_2 frequencies_sorted_2 frequencies_2 values_sorted_2.
    split_pure_spatial.
    + cancel (Int64Array.full a_pre n_pre values_sorted_2).
      cancel (IntArray.full left_pre q_pre lefts).
      cancel (IntArray.full right_pre q_pre rights).
      cancel (Int64Array.full diff (n_pre + 1)
        (frequencies_sorted_2 ++ tail_2)).
    + split_pures; dump_pre_spatial; try lia; try assumption.
      unfold DotProductPrefix, DotProduct.
      repeat split; try lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Happ :
    Znth i (frequencies_sorted_2 ++ tail_2) 0 =
    Znth i frequencies_sorted_2 0).
  {
    apply Znth_app_left__dot_product_accumulation.
    lia.
  }
  pose proof (PreH24 i ltac:(lia)) as Hvalue.
  pose proof (PreH25 i ltac:(lia)) as Hfrequency.
  pose proof
    (DotProductPrefix_step__dot_product_accumulation
      values_sorted_2 frequencies_sorted_2 i answer ltac:(lia) PreH28)
    as Hprefix.
  rewrite Happ.
  Exists tail_2 frequencies_sorted_2 frequencies_2 values_sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try nia; try assumption.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  assert (Hquery_bounds :
    forall j, 0 <= j < Zlength queries ->
      0 <= fst (Znth j queries (0, 0)) <=
           snd (Znth j queries (0, 0)) /\
      snd (Znth j queries (0, 0)) < n_pre).
  {
    intros j Hj.
    pose proof (PreH12 j ltac:(lia)) as Hq.
    rewrite (Znth_indep queries j __default__Prod_Z_Z (0, 0) Hj) in Hq.
    exact Hq.
  }
  pose proof
    (DotProductPrefix_complete__final_optimality
      values_sorted frequencies_sorted i answer PreH28 ltac:(lia)) as Hanswer.
  destruct
    (DotProduct_transport_permutation__final_optimality
      frequencies_sorted frequencies (Permutation_sym PreH22)
      values_sorted ltac:(lia))
    as [arranged [Harranged Hdot]].
  assert (Harranged_len : Zlength arranged = n_pre).
  {
    rewrite Zlength_correct.
    rewrite <- (Permutation_length Harranged).
    rewrite <- Zlength_correct. exact PreH15.
  }
  unfold Spec, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists arranged. split.
  - split.
    + eapply Permutation_trans; eauto.
    + intros candidate Hcandidate.
      assert (Hcandidate_len : Zlength candidate = n_pre).
      {
        rewrite Zlength_correct.
        rewrite <- (Permutation_length Hcandidate).
        rewrite <- Zlength_correct. symmetry. exact PreH3.
      }
      rewrite (QueryReplyTotal_as_DotProduct__final_optimality
        candidate queries frequencies n_pre
        Hcandidate_len PreH21 Hquery_bounds).
      rewrite (QueryReplyTotal_as_DotProduct__final_optimality
        arranged queries frequencies n_pre
        Harranged_len PreH21 Hquery_bounds).
      rewrite <- Hdot.
      eapply sorted_DotProduct_maximal__final_optimality.
      * lia.
      * exact PreH20.
      * exact PreH23.
      * eapply Permutation_trans.
        -- apply Permutation_sym. exact PreH19.
        -- exact Hcandidate.
      * apply Permutation_sym. exact PreH22.
  - rewrite (QueryReplyTotal_as_DotProduct__final_optimality
      arranged queries frequencies n_pre
      Harranged_len PreH21 Hquery_bounds).
    rewrite <- Hdot. symmetry. exact Hanswer.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
