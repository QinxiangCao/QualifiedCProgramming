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

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 : binomial_digit_mod_prime_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  unfold DigitProductProgress, DigitNumeratorPrefix, DigitDenominatorPrefix.
  rewrite !lucas_range_product_zero__digit_product_progress.
  split; rewrite Z.mod_small; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_2 : binomial_digit_mod_prime_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_1_1_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  unfold DigitProductProgress, DigitNumeratorPrefix, DigitDenominatorPrefix.
  rewrite !lucas_range_product_zero__digit_product_progress.
  split; rewrite Z.mod_small; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_2 : binomial_digit_mod_prime_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_1_2_split_goal_2.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_1 : binomial_digit_mod_prime_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by (first [lia | apply Z.mul_nonneg_nonneg; lia]).
  eapply digit_product_progress_step__digit_product_progress; eauto; lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_2 : binomial_digit_mod_prime_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite Z.rem_mod_nonneg by (first [lia | apply Z.mul_nonneg_nonneg; lia]).
  pose proof (Z.mod_pos_bound (denominator * i) prime_pre ltac:(lia)). lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_3 : binomial_digit_mod_prime_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite Z.rem_mod_nonneg by (first [lia | apply Z.mul_nonneg_nonneg; lia]).
  pose proof (Z.mod_pos_bound (denominator * i) prime_pre ltac:(lia)). lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_4 : binomial_digit_mod_prime_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite Z.rem_mod_nonneg by (first [lia | apply Z.mul_nonneg_nonneg; lia]).
  pose proof (Z.mod_pos_bound (numerator * (upper_pre - lower + i)) prime_pre ltac:(lia)). lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_5 : binomial_digit_mod_prime_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite Z.rem_mod_nonneg by (first [lia | apply Z.mul_nonneg_nonneg; lia]).
  pose proof (Z.mod_pos_bound (numerator * (upper_pre - lower + i)) prime_pre ltac:(lia)). lia.
Qed.

Lemma proof_of_binomial_digit_mod_prime_entail_wit_2 : binomial_digit_mod_prime_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_binomial_digit_mod_prime_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1 : binomial_digit_mod_prime_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  assert (Hretval : 0 <= retval < prime_pre).
  { unfold ModularPower in PreH1. rewrite PreH1.
    apply Z.mod_pos_bound. lia. }

  assert (Hi : i = lower + 1) by lia.
  rewrite Hi in PreH18.
  unfold BinomialDigitResidue.
  rewrite Z.rem_mod_nonneg by (first [lia | apply Z.mul_nonneg_nonneg; lia]).
  transitivity (LucasBinomialCoefficient upper_pre lower mod prime_pre).
  - eapply digit_multiplicative_residue__digit_final_residue; eauto; lia.
  - rewrite PreH9.
    destruct (Z_le_dec lower_pre (upper_pre - lower_pre)).
    + rewrite Z.min_l by lia. reflexivity.
    + rewrite Z.min_r by lia.
      rewrite <- lucas_binomial_symmetry_z__digit_final_residue by lia.
      reflexivity.
Qed.

Lemma proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_binomial_digit_mod_prime_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_1_split_goal_1 : lucas_theorem_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  unfold LucasProgress. exists 0.
  repeat split.
  - lia.
  - cbn. rewrite Z.div_1_r. reflexivity.
  - cbn. rewrite Z.div_1_r. reflexivity.
  - unfold LucasPrefixProduct. cbn. symmetry. apply Z.mod_small. lia.
  - rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_1 : lucas_theorem_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  assert (Hretval : 0 <= retval < prime_pre).
  { unfold BinomialDigitResidue in PreH1. rewrite PreH1.
    apply Z.mod_pos_bound. lia. }

  eapply lucas_progress_advance__lucas_digit_transition; eauto; lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_2 : lucas_theorem_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  assert (Hretval : 0 <= retval < prime_pre).
  { unfold BinomialDigitResidue in PreH1. rewrite PreH1.
    apply Z.mod_pos_bound. lia. }

  pose proof (Z.rem_bound_pos (result * retval) prime_pre ltac:(apply Z.mul_nonneg_nonneg; lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_3 : lucas_theorem_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  assert (Hretval : 0 <= retval < prime_pre).
  { unfold BinomialDigitResidue in PreH1. rewrite PreH1.
    apply Z.mod_pos_bound. lia. }

  pose proof (Z.rem_bound_pos (result * retval) prime_pre ltac:(apply Z.mul_nonneg_nonneg; lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_4 : lucas_theorem_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  apply Z.quot_le_mono; lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2_split_goal_5 : lucas_theorem_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  apply Z.quot_pos; lia.
Qed.

Lemma proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_lucas_theorem_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_lucas_theorem_return_wit_1_split_goal_1 : lucas_theorem_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  assert (Hlower_zero : lower = 0) by lia.
  assert (Hupper_zero : upper = 0) by lia.
  subst lower upper. unfold LucasBinomialResidue.
  eapply lucas_progress_terminal_residue__lucas_terminal_return; eauto; lia.
Qed.

Lemma proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_lucas_theorem_return_wit_2_split_goal_1 : lucas_theorem_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  unfold LucasBinomialResidue.
  destruct PreH12 as [processed [Hprocessed [Hupper [Hlower [Hresult Hresidue]]]]].
  rewrite Hresidue.
  pose proof (lucas_binomial_zero_from_low_digit__lucas_digit_transition
    upper lower prime_pre ltac:(lia) ltac:(lia) PreH7 ltac:(lia)) as Hzero.
  rewrite Zmult_mod, Hzero, Z.mul_0_r, Zmod_0_l. reflexivity.
Qed.

Lemma proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_lucas_theorem_partial_solve_wit_1_pure_split_goal_1 : lucas_theorem_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  pose proof (Z.rem_bound_pos lower prime_pre ltac:(lia) ltac:(lia)).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_lucas_theorem_partial_solve_wit_1_pure_split_goal_2 : lucas_theorem_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  pose proof (Z.rem_bound_pos upper prime_pre ltac:(lia) ltac:(lia)).
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_lucas_theorem_partial_solve_wit_1_pure : lucas_theorem_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lucas_theorem_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_lucas_theorem_partial_solve_wit_1_pure_split_goal_2.
Qed.
