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
From SimpleC.EE.LLM_bench.Algorithms.lucas_theorem Require Import lucas_theorem_goal.
From SimpleC.EE.LLM_bench.Algorithms.lucas_theorem Require Import lucas_theorem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib.
Local Open Scope sac.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_1 : binomial_digit_mod_prime_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DigitBinomialMachineSafe in PreH17.
  unfold DigitEffectiveLower in PreH17.
  rewrite Z.min_l in PreH17 by lia.
  destruct PreH17 as [Hloop _].
  specialize (Hloop i ltac:(lia)).
  destruct Hloop as [Hnumerator_bound _].
  unfold DigitProductProgress in PreH18.
  destruct PreH18 as [Hnumerator _].
  rewrite <- Hnumerator in Hnumerator_bound.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_2 : binomial_digit_mod_prime_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_14 : binomial_digit_mod_prime_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_1 : binomial_digit_mod_prime_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lower.
  unfold DigitBinomialMachineSafe in PreH18.
  unfold DigitEffectiveLower in PreH18.
  rewrite Z.min_r in PreH18 by lia.
  destruct PreH18 as [Hloop _].
  specialize (Hloop i ltac:(lia)).
  destruct Hloop as [Hnumerator_bound _].
  unfold DigitProductProgress in PreH19.
  destruct PreH19 as [Hnumerator _].
  rewrite <- Hnumerator in Hnumerator_bound.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_2 : binomial_digit_mod_prime_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_15 : binomial_digit_mod_prime_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_1 : binomial_digit_mod_prime_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DigitBinomialMachineSafe in PreH17.
  unfold DigitEffectiveLower in PreH17.
  rewrite Z.min_l in PreH17 by lia.
  destruct PreH17 as [Hloop _].
  specialize (Hloop i ltac:(lia)).
  destruct Hloop as [_ Hdenominator_bound].
  unfold DigitProductProgress in PreH18.
  destruct PreH18 as [_ Hdenominator].
  rewrite <- Hdenominator in Hdenominator_bound.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_2 : binomial_digit_mod_prime_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_16 : binomial_digit_mod_prime_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_1 : binomial_digit_mod_prime_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lower.
  unfold DigitBinomialMachineSafe in PreH18.
  unfold DigitEffectiveLower in PreH18.
  rewrite Z.min_r in PreH18 by lia.
  destruct PreH18 as [Hloop _].
  specialize (Hloop i ltac:(lia)).
  destruct Hloop as [_ Hdenominator_bound].
  unfold DigitProductProgress in PreH19.
  destruct PreH19 as [_ Hdenominator].
  rewrite <- Hdenominator in Hdenominator_bound.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_2 : binomial_digit_mod_prime_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_17 : binomial_digit_mod_prime_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_1 : binomial_digit_mod_prime_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lower.
  unfold DigitBinomialMachineSafe in PreH19.
  unfold DigitEffectiveLower in PreH19.
  rewrite Z.min_r in PreH19 by lia.
  destruct PreH19 as [_ Hanswer].
  unfold DigitProductProgress in PreH20.
  replace (upper_pre - lower_pre + 1 - 1)
    with (upper_pre - lower_pre) in PreH20 by lia.
  destruct PreH20 as [Hnumerator Hdenominator].
  rewrite Hdenominator in PreH3.
  specialize (Hanswer retval PreH3).
  rewrite <- Hnumerator in Hanswer.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_2 : binomial_digit_mod_prime_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_28 : binomial_digit_mod_prime_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_1 : binomial_digit_mod_prime_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DigitBinomialMachineSafe in PreH18.
  unfold DigitEffectiveLower in PreH18.
  rewrite Z.min_l in PreH18 by lia.
  destruct PreH18 as [_ Hanswer].
  unfold DigitProductProgress in PreH19.
  replace (lower_pre + 1 - 1) with lower_pre in PreH19 by lia.
  destruct PreH19 as [Hnumerator Hdenominator].
  rewrite Hdenominator in PreH3.
  specialize (Hanswer retval PreH3).
  rewrite <- Hnumerator in Hanswer.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_2 : binomial_digit_mod_prime_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_binomial_digit_mod_prime_safety_wit_29 : binomial_digit_mod_prime_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DigitProductProgress, DigitNumeratorPrefix,
    DigitDenominatorPrefix.
  rewrite !lucas_range_product_zero__digit_product_progress.
  split; rewrite Z.mod_small; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DigitProductProgress, DigitNumeratorPrefix,
    DigitDenominatorPrefix.
  rewrite !lucas_range_product_zero__digit_product_progress.
  split; rewrite Z.mod_small; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by nia.
  eapply digit_product_progress_step__digit_product_progress; eauto; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound (denominator * i) prime_pre ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound (denominator * i) prime_pre ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound
      (numerator * (upper_pre - lower_pre + i)) prime_pre ltac:(lia))
    as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 : binomial_digit_mod_prime_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound
      (numerator * (upper_pre - lower_pre + i)) prime_pre ltac:(lia))
    as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_1 : binomial_digit_mod_prime_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_1_split_goal_5.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lower.
  rewrite !Z.rem_mod_nonneg by nia.
  eapply digit_product_progress_step__digit_product_progress; eauto; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound (denominator * i) prime_pre ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound (denominator * i) prime_pre ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound
      (numerator * (upper_pre - (upper_pre - lower_pre) + i))
      prime_pre ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 : binomial_digit_mod_prime_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  pose proof
    (Z.mod_pos_bound
      (numerator * (upper_pre - (upper_pre - lower_pre) + i))
      prime_pre ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_2 : binomial_digit_mod_prime_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_2_split_goal_5.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (lower_pre + 1) with i by lia.
  exact PreH18.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_3_1 : binomial_digit_mod_prime_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst lower_2.
  replace (upper_pre - lower_pre + 1) with i by lia.
  exact PreH19.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_3_2 : binomial_digit_mod_prime_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1 : binomial_digit_mod_prime_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BinomialDigitResidue.
  rewrite Z.rem_mod_nonneg by nia.
  transitivity (LucasBinomialCoefficient upper_pre lower mod prime_pre).
  - eapply digit_multiplicative_residue__digit_final_residue;
      eauto; lia.
  - assert
      (Hsym :
        LucasBinomialCoefficient upper_pre lower =
        LucasBinomialCoefficient upper_pre lower_pre).
    { rewrite lucas_binomial_symmetry_z__digit_final_residue by lia.
      f_equal. lia. }
    now rewrite Hsym.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_2 : binomial_digit_mod_prime_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_3 : binomial_digit_mod_prime_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_2.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_1 : binomial_digit_mod_prime_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BinomialDigitResidue.
  rewrite Z.rem_mod_nonneg by nia.
  eapply digit_multiplicative_residue__digit_final_residue;
    eauto; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_2 : binomial_digit_mod_prime_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_3 : binomial_digit_mod_prime_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_2 : binomial_digit_mod_prime_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_2.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_lucas_theorem_safety_wit_9_split_goal_1 : lucas_theorem_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LucasProgress in PreH25.
  destruct PreH25 as [processed [Hupper [Hlower [Hresult Hresidue]]]].
  unfold LucasMachineSafe in PreH11.
  specialize (PreH11 processed).
  rewrite Z.rem_mod_nonneg in PreH17 by lia.
  rewrite Z.rem_mod_nonneg in PreH18 by lia.
  assert (Hupper_digit : LucasDigit (n_pre + m_pre) prime_pre processed = upper_digit).
  { unfold LucasDigit.
    rewrite <- Hupper.
    symmetry.
    exact PreH17. }
  assert (Hlower_digit : LucasDigit n_pre prime_pre processed = lower_digit).
  { unfold LucasDigit.
    rewrite <- Hlower.
    symmetry.
    exact PreH18. }
  rewrite Hupper_digit, Hlower_digit in PreH11.
  specialize (PreH11 PreH20).
  destruct PreH11 as [_ Hproduct].
  unfold BinomialDigitResidue in PreH3.
  rewrite <- Hresult, <- PreH3 in Hproduct.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_lucas_theorem_safety_wit_9_split_goal_2 : lucas_theorem_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_lucas_theorem_safety_wit_9 : lucas_theorem_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_lucas_theorem_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_1_split_goal_1 : lucas_theorem_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LucasProgress.
  exists O.
  repeat split.
  - cbn. rewrite Z.div_1_r. reflexivity.
  - cbn. rewrite Z.div_1_r. reflexivity.
  - unfold LucasPrefixProduct.
    cbn.
    symmetry.
    apply Z.mod_small.
    lia.
  - rewrite Z.mul_1_l.
    reflexivity.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lucas_theorem_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_1 : lucas_theorem_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite !Z.rem_mod_nonneg in PreH1 by lia.
  unfold LucasProgress in PreH17.
  destruct PreH17 as [processed [Hupper [Hlower [Hresult Hresidue]]]].
  unfold LucasMachineSafe in PreH10.
  specialize (PreH10 processed).
  assert (Hupper_digit : LucasDigit (n_pre + m_pre) prime_pre processed = upper mod prime_pre).
  { unfold LucasDigit.
    rewrite <- Hupper.
    reflexivity. }
  assert (Hlower_digit : LucasDigit n_pre prime_pre processed = lower mod prime_pre).
  { unfold LucasDigit.
    rewrite <- Hlower.
    reflexivity. }
  rewrite Hupper_digit, Hlower_digit in PreH10.
  exact (proj1 (PreH10 PreH1)).
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_2 : lucas_theorem_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos upper prime_pre ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_3 : lucas_theorem_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_pos lower prime_pre ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3_split_goal_1 : lucas_theorem_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst upper_digit lower_digit.
  eapply lucas_progress_advance__lucas_digit_transition; eauto; lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3_split_goal_2 : lucas_theorem_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (proj2 (Z.rem_bound_pos (result * retval) prime_pre ltac:(nia) ltac:(lia))).
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3_split_goal_3 : lucas_theorem_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (proj1 (Z.rem_bound_pos (result * retval) prime_pre ltac:(nia) ltac:(lia))).
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3_split_goal_4 : lucas_theorem_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_le_upper_bound; nia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3_split_goal_5 : lucas_theorem_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_le_mono; lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3_split_goal_6 : lucas_theorem_entail_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_pos; lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_3 : lucas_theorem_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_lucas_theorem_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_lucas_theorem_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_lucas_theorem_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_lucas_theorem_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_lucas_theorem_entail_wit_3_split_goal_6.
Qed.

Lemma proof_of_lucas_theorem_return_wit_1_split_goal_1 : lucas_theorem_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlower_zero : lower = 0) by lia.
  assert (Hupper_zero : upper = 0) by lia.
  subst lower upper.
  unfold LucasBinomialResidue.
  eapply lucas_progress_terminal_residue__lucas_terminal_return; eauto; lia.
Qed.

Lemma proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lucas_theorem_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_lucas_theorem_return_wit_2_split_goal_1 : lucas_theorem_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LucasBinomialResidue.
  destruct PreH17 as [processed [Hupper [Hlower [Hresult Hresidue]]]].
  rewrite Hresidue.
  pose proof (lucas_binomial_zero_from_low_digit__lucas_digit_transition
    upper lower prime_pre ltac:(lia) ltac:(lia) PreH9 ltac:(lia)) as Hzero.
  rewrite Zmult_mod, Hzero, Z.mul_0_r, Zmod_0_l.
  reflexivity.
Qed.

Lemma proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_return_wit_2_split_goal_1.
Qed.
