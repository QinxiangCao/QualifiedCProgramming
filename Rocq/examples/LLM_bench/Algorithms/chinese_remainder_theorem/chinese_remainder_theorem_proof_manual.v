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
From SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem Require Import chinese_remainder_theorem_goal.
From SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem Require Import chinese_remainder_theorem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib.
Require Import AUXLib.MonotonicList.
Local Open Scope sac.

Lemma proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1 : chinese_remainder_theorem_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  pose proof
    (crt_prefix_product_bounds__product_progress
       remainders_l moduli_l (i + 1) PreH3 ltac:(lia)) as Hbounds.
  pose proof (crt_prefix_product_step__product_progress moduli_l i ltac:(lia))
    as Hstep.
  destruct Hbounds as [[_ Hbound] _].
  rewrite PreH7, <- Hstep.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2 : chinese_remainder_theorem_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  destruct PreH3 as [_ [_ [Hvalues _]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [Hmodulus _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_3 : chinese_remainder_theorem_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1 : chinese_remainder_theorem_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2 : chinese_remainder_theorem_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH19) as PreH12.
  assert (PreH13 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH20) as Hzero.
    intros k Hk. apply Hzero. lia. }
  unfold CRTInputValid in PreH3.
  destruct PreH3 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_7 : chinese_remainder_theorem_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1 : chinese_remainder_theorem_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  assert (PreH5 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH10. tauto. }
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH21) as PreH14.
  assert (PreH15 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH22) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (CRTInputValid_modulus_upper_bound__machine_safety
       remainders_l moduli_l i PreH5 ltac:(lia)) as Hmodulus_upper.
  unfold CRTInputValid in PreH5.
  destruct PreH5 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus Hremainder].
  pose proof
    (crt_c_rem_mul_int_bounds__machine_safety
       (x_callee_v * (product ÷ Znth i moduli_l 0)) product
       (Znth i remainders_l 0) PreH8 PreH9
       ltac:(lia) ltac:(lia)) as Hbound.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2 : chinese_remainder_theorem_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  assert (PreH5 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH10. tauto. }
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH21) as PreH14.
  assert (PreH15 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH22) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (CRTInputValid_modulus_upper_bound__machine_safety
       remainders_l moduli_l i PreH5 ltac:(lia)) as Hmodulus_upper.
  unfold CRTInputValid in PreH5.
  destruct PreH5 as [_ [_ [Hentries _]]].
  pose proof (Hentries i ltac:(lia)) as [Hmodulus Hremainder].
  pose proof
    (crt_c_rem_mul_int_bounds__machine_safety
       (x_callee_v * (product ÷ Znth i moduli_l 0)) product
       (Znth i remainders_l 0) PreH8 PreH9
       ltac:(lia) ltac:(lia)) as Hbound.
  dump_pre_spatial.
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_11 : chinese_remainder_theorem_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1 : chinese_remainder_theorem_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (Z.rem_bound_abs
       ((Z.rem
           (x_callee_v * (product ÷ Znth i moduli_l 0)) product) *
        Znth i remainders_l 0)
       product ltac:(lia)) as Hterm.
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2 : chinese_remainder_theorem_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
Qed.

Lemma proof_of_chinese_remainder_theorem_safety_wit_17 : chinese_remainder_theorem_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 : chinese_remainder_theorem_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 : chinese_remainder_theorem_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  all: match goal with H : forall x : Z, _ |- _ => solve [eapply H; eassumption] end.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_1 : chinese_remainder_theorem_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 : chinese_remainder_theorem_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  pose proof
    (crt_prefix_product_bounds__product_progress
       remainders_l moduli_l (i + 1) PreH3 ltac:(lia)) as Hbounds.
  pose proof (crt_prefix_product_step__product_progress moduli_l i ltac:(lia))
    as Hstep.
  destruct Hbounds as [[_ Hbound] _].
  rewrite PreH7, <- Hstep.
  exact Hbound.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 : chinese_remainder_theorem_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  destruct PreH3 as [_ [_ [Hvalues _]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [Hmodulus _].
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 : chinese_remainder_theorem_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  rewrite PreH7.
  symmetry.
  apply crt_prefix_product_step__product_progress.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_2 : chinese_remainder_theorem_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 : chinese_remainder_theorem_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  unfold CRTUnprocessedZero. apply Forall_forall. intros modulus Hmodulus. reflexivity.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 : chinese_remainder_theorem_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  match goal with |- CRTConsistentPrefix ?rs ?ms ?k ?r => apply (proj2 (crt_prefix_indexed rs ms k r ltac:(lia) ltac:(lia))) end.
  unfold CRTProcessedCongruences.
  intros k Hk.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 : chinese_remainder_theorem_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH10 as PreH10.
  assert (i = n_pre) as Hi by lia.
  subst i.
  rewrite PreH2 in PreH7.
  rewrite sublist_self in PreH7 by reflexivity.
  exact PreH7.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_4 : chinese_remainder_theorem_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  all: match goal with H : forall x : Z, _ |- _ => solve [eapply H; eassumption] end.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_3 : chinese_remainder_theorem_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : chinese_remainder_theorem_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  match goal with |- CRTUnprocessedZero _ _ (Z.rem ?sum product) =>
    replace sum with
      (result + Z.rem (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product + 1 * product) by ring
  end.
  eapply crt_update_unprocessed_rem; try eassumption; lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : chinese_remainder_theorem_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  match goal with |- CRTConsistentPrefix ?rs ?ms ?k ?r => apply (proj2 (crt_prefix_indexed rs ms k r ltac:(lia) ltac:(lia))) end.
  assert (Hupdate :
    CRTProcessedCongruences remainders_l moduli_l (i + 1)
      ((result +
        ((((x_callee_v * (product / Znth i moduli_l 0)) mod product) *
          Znth i remainders_l 0) mod product)) mod product)).
  {
    eapply
      (crt_update_processed__crt_transition
        remainders_l moduli_l result i product x_callee_v y_callee_v).
    - exact PreH6.
    - lia.
    - exact PreH8.
    - lia.
    - exact PreH15.
    - intros k Hk.
      pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds k ltac:(lia)) as [Hmodulus _].
      rewrite <- Z.rem_mod_nonneg by lia.
      apply PreH16. lia.
    - pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
      rewrite <-
        (crt_quot_div_pos__crt_transition
          product (Znth i moduli_l 0)) by lia.
      exact PreH3.
  }
  unfold CRTProcessedCongruences in Hupdate |-.
  intros j Hj.
  specialize (Hupdate j Hj).
  pose proof PreH6 as [_ [_ [Hbounds _]]].
  pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    in PreH1 by lia.
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    by lia.
  assert (Hterm_mod :
    (Z.rem
      (Z.rem
        (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) product) mod product =
    (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
      Znth i remainders_l 0) mod product)).
  {
    rewrite crt_rem_mod__crt_transition by lia.
    apply crt_rem_mul_mod__crt_transition. lia.
  }
  pose proof
    (Z.rem_bound_abs
      (Z.rem (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) product) as Hterm_bound.
  rewrite
    (Z.abs_neq
      (Z.rem
        (Z.rem (x_callee_v * (product / Znth i moduli_l 0)) product *
          Znth i remainders_l 0) product))
    in Hterm_bound by lia.
  rewrite (Z.abs_eq product) in Hterm_bound by lia.
  assert (Houter_nonnegative :
    0 <= result +
      (Z.rem
        (Z.rem
          (x_callee_v * (product / Znth i moduli_l 0)) product *
          Znth i remainders_l 0) product + product)) by lia.
  assert (Hupdate_eq :
    Z.rem
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product + product)) product =
    (result +
      (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
        Znth i remainders_l 0) mod product)) mod product).
  {
    rewrite crt_rem_eq_mod_of_nonnegative_dividend__crt_transition by lia.
    replace
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product + product))
      with
      ((result +
        Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product) + 1 * product)
      by ring.
    rewrite Z.mod_add by lia.
    transitivity
      ((result mod product +
        (Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product) mod product) mod product).
    - apply Zplus_mod.
    - rewrite Hterm_mod.
      symmetry.
      rewrite Zplus_mod, Zmod_mod.
      reflexivity.
  }
  rewrite Hupdate_eq.
  exact Hupdate.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : chinese_remainder_theorem_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (Z.rem_bound_abs
      (Z.rem
        (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
        Znth i remainders_l 0) product) as Hterm_bound.
  rewrite
    (Z.abs_neq
      (Z.rem
        (Z.rem
          (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
          Znth i remainders_l 0) product))
    in Hterm_bound by lia.
  rewrite (Z.abs_eq product) in Hterm_bound by lia.
  pose proof
    (Z.rem_bound_pos
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product + product))
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 : chinese_remainder_theorem_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (Z.rem_bound_abs
      (Z.rem
        (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
        Znth i remainders_l 0) product) as Hterm_bound.
  rewrite
    (Z.abs_neq
      (Z.rem
        (Z.rem
          (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
          Znth i remainders_l 0) product))
    in Hterm_bound by lia.
  rewrite (Z.abs_eq product) in Hterm_bound by lia.
  pose proof
    (Z.rem_bound_pos
      (result +
        (Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product + product))
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_1 : chinese_remainder_theorem_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_4.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : chinese_remainder_theorem_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  match goal with |- CRTUnprocessedZero _ _ (Z.rem ?sum product) =>
    replace sum with
      (result + Z.rem (Z.rem (x_callee_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product + 0 * product) by ring
  end.
  eapply crt_update_unprocessed_rem; try eassumption; lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : chinese_remainder_theorem_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  match goal with |- CRTConsistentPrefix ?rs ?ms ?k ?r => apply (proj2 (crt_prefix_indexed rs ms k r ltac:(lia) ltac:(lia))) end.
  assert (Hupdate :
    CRTProcessedCongruences remainders_l moduli_l (i + 1)
      ((result +
        ((((x_callee_v * (product / Znth i moduli_l 0)) mod product) *
          Znth i remainders_l 0) mod product)) mod product)).
  {
    eapply
      (crt_update_processed__crt_transition
        remainders_l moduli_l result i product x_callee_v y_callee_v).
    - exact PreH6.
    - lia.
    - exact PreH8.
    - lia.
    - exact PreH15.
    - intros k Hk.
      pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds k ltac:(lia)) as [Hmodulus _].
      rewrite <- Z.rem_mod_nonneg by lia.
      apply PreH16. lia.
    - pose proof PreH6 as [_ [_ [Hbounds _]]].
      pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
      rewrite <-
        (crt_quot_div_pos__crt_transition
          product (Znth i moduli_l 0)) by lia.
      exact PreH3.
  }
  unfold CRTProcessedCongruences in Hupdate |-.
  intros j Hj.
  specialize (Hupdate j Hj).
  pose proof PreH6 as [_ [_ [Hbounds _]]].
  pose proof (Hbounds i ltac:(lia)) as [Hmodulus _].
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    in PreH1 by lia.
  rewrite
    (crt_quot_div_pos__crt_transition product (Znth i moduli_l 0))
    by lia.
  assert (Hterm_eq :
    Z.rem
      (Z.rem
        (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) product =
    (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
      Znth i remainders_l 0) mod product)).
  {
    transitivity
      ((Z.rem
        (x_callee_v * (product / Znth i moduli_l 0)) product *
        Znth i remainders_l 0) mod product).
    - apply crt_nonnegative_rem_eq_mod__crt_transition; lia.
    - apply crt_rem_mul_mod__crt_transition. lia.
  }
  assert (Hupdate_eq :
    Z.rem
      (result +
        Z.rem
          (Z.rem
            (x_callee_v * (product / Znth i moduli_l 0)) product *
            Znth i remainders_l 0) product) product =
    (result +
      (((x_callee_v * (product / Znth i moduli_l 0)) mod product *
        Znth i remainders_l 0) mod product)) mod product).
  {
    rewrite crt_rem_eq_mod_of_nonnegative_dividend__crt_transition by lia.
    rewrite Hterm_eq. reflexivity.
  }
  rewrite Hupdate_eq.
  exact Hupdate.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : chinese_remainder_theorem_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (Z.rem_bound_pos
      (result +
        Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product)
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 : chinese_remainder_theorem_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  rename PreH20 into NewPreH21.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  assert (PreH6 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH11. tauto. }
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof NewPreH19 as PreH12.
  pose proof NewPreH20 as PreH13.
  pose proof NewPreH21 as PreH14.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH22) as PreH15.
  assert (PreH16 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH23) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (Z.rem_bound_pos
      (result +
        Z.rem
          (Z.rem
            (x_callee_v * (Z.quot product (Znth i moduli_l 0))) product *
            Znth i remainders_l 0) product)
      product ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_entail_wit_4_2 : chinese_remainder_theorem_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_4.
Qed.

Lemma proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 : chinese_remainder_theorem_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH12.
  rename PreH12 into NewPreH13.
  rename PreH13 into NewPreH14.
  rename PreH14 into NewPreH15.
  rename PreH15 into NewPreH16.
  rename PreH16 into NewPreH17.
  rename PreH17 into NewPreH18.
  rename PreH18 into NewPreH19.
  rename PreH19 into NewPreH20.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  assert (PreH3 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH8. tauto. }
  pose proof NewPreH12 as PreH5.
  pose proof NewPreH13 as PreH6.
  pose proof NewPreH14 as PreH7.
  pose proof NewPreH15 as PreH8.
  pose proof NewPreH16 as PreH9.
  pose proof NewPreH17 as PreH10.
  pose proof NewPreH18 as PreH11.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH19) as PreH12.
  assert (PreH13 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH20) as Hzero.
    intros k Hk. apply Hzero. lia. }
  unfold CanonicalCRTSolution.
  split.
  - rewrite <- PreH5.
    lia.
  - apply (proj2 (crt_Forall2_Znth _ remainders_l moduli_l ltac:(lia))).
    intros k Hk.
    apply PreH12.
    lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_return_wit_1 : chinese_remainder_theorem_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH14.
  rename PreH15 into NewPreH15.
  rename PreH16 into NewPreH16.
  rename PreH17 into NewPreH17.
  rename PreH18 into NewPreH18.
  rename PreH19 into NewPreH19.
  rename PreH20 into NewPreH20.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  rename PreH23 into NewPreH24.
  rename PreH24 into NewPreH25.
  rename PreH25 into NewPreH26.
  rename PreH26 into NewPreH27.
  rename PreH27 into NewPreH28.
  rename PreH28 into NewPreH29.
  rename PreH29 into NewPreH30.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  pose proof NewPreH6 as PreH6.
  pose proof NewPreH7 as PreH7.
  pose proof NewPreH8 as PreH8.
  pose proof NewPreH9 as PreH9.
  pose proof NewPreH10 as PreH10.
  pose proof NewPreH11 as PreH11.
  pose proof NewPreH12 as PreH12.
  assert (PreH13 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH18. tauto. }
  pose proof NewPreH22 as PreH15.
  pose proof NewPreH23 as PreH16.
  pose proof NewPreH24 as PreH17.
  pose proof NewPreH25 as PreH18.
  pose proof NewPreH26 as PreH19.
  pose proof NewPreH27 as PreH20.
  pose proof NewPreH28 as PreH21.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH29) as PreH22.
  assert (PreH23 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH30) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (crt_factor_quotient_bounds__product_progress
       remainders_l moduli_l i PreH13 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[Hmodulus _] [Hquotient _]].
  dump_pre_spatial.
  rewrite PreH15.
  rewrite Z.quot_div_nonneg by lia.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH14.
  rename PreH15 into NewPreH15.
  rename PreH16 into NewPreH16.
  rename PreH17 into NewPreH17.
  rename PreH18 into NewPreH18.
  rename PreH19 into NewPreH19.
  rename PreH20 into NewPreH20.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  rename PreH23 into NewPreH24.
  rename PreH24 into NewPreH25.
  rename PreH25 into NewPreH26.
  rename PreH26 into NewPreH27.
  rename PreH27 into NewPreH28.
  rename PreH28 into NewPreH29.
  rename PreH29 into NewPreH30.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  pose proof NewPreH6 as PreH6.
  pose proof NewPreH7 as PreH7.
  pose proof NewPreH8 as PreH8.
  pose proof NewPreH9 as PreH9.
  pose proof NewPreH10 as PreH10.
  pose proof NewPreH11 as PreH11.
  pose proof NewPreH12 as PreH12.
  assert (PreH13 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH18. tauto. }
  pose proof NewPreH22 as PreH15.
  pose proof NewPreH23 as PreH16.
  pose proof NewPreH24 as PreH17.
  pose proof NewPreH25 as PreH18.
  pose proof NewPreH26 as PreH19.
  pose proof NewPreH27 as PreH20.
  pose proof NewPreH28 as PreH21.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH29) as PreH22.
  assert (PreH23 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH30) as Hzero.
    intros k Hk. apply Hzero. lia. }
  destruct PreH13 as [_ [_ [Hvalues _]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [Hmodulus _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite crt_reduced_int_cast in * by lia).
  rename PreH1 into NewPreH1.
  rename PreH2 into NewPreH2.
  rename PreH3 into NewPreH3.
  rename PreH4 into NewPreH4.
  rename PreH5 into NewPreH5.
  rename PreH6 into NewPreH6.
  rename PreH7 into NewPreH7.
  rename PreH8 into NewPreH8.
  rename PreH9 into NewPreH9.
  rename PreH10 into NewPreH10.
  rename PreH11 into NewPreH11.
  rename PreH12 into NewPreH12.
  rename PreH13 into NewPreH13.
  rename PreH14 into NewPreH14.
  rename PreH15 into NewPreH15.
  rename PreH16 into NewPreH16.
  rename PreH17 into NewPreH17.
  rename PreH18 into NewPreH18.
  rename PreH19 into NewPreH19.
  rename PreH20 into NewPreH20.
  rename PreH21 into NewPreH22.
  rename PreH22 into NewPreH23.
  rename PreH23 into NewPreH24.
  rename PreH24 into NewPreH25.
  rename PreH25 into NewPreH26.
  rename PreH26 into NewPreH27.
  rename PreH27 into NewPreH28.
  rename PreH28 into NewPreH29.
  rename PreH29 into NewPreH30.
  pose proof NewPreH1 as PreH1.
  pose proof NewPreH2 as PreH2.
  pose proof NewPreH3 as PreH3.
  pose proof NewPreH4 as PreH4.
  pose proof NewPreH5 as PreH5.
  pose proof NewPreH6 as PreH6.
  pose proof NewPreH7 as PreH7.
  pose proof NewPreH8 as PreH8.
  pose proof NewPreH9 as PreH9.
  pose proof NewPreH10 as PreH10.
  pose proof NewPreH11 as PreH11.
  pose proof NewPreH12 as PreH12.
  assert (PreH13 : (CRTInputValid remainders_l moduli_l )).
  { apply crt_input_from_explicit; try assumption.
    intros j k Hj. apply NewPreH18. tauto. }
  pose proof NewPreH22 as PreH15.
  pose proof NewPreH23 as PreH16.
  pose proof NewPreH24 as PreH17.
  pose proof NewPreH25 as PreH18.
  pose proof NewPreH26 as PreH19.
  pose proof NewPreH27 as PreH20.
  pose proof NewPreH28 as PreH21.
  pose proof (proj1 (crt_prefix_indexed remainders_l moduli_l i result ltac:(lia) ltac:(lia)) NewPreH29) as PreH22.
  assert (PreH23 : forall (k: Z) , (((i <= k) /\ (k < n_pre)) -> ((result % ( (Znth (k) (moduli_l) (0)) ) ) = 0))).
  { pose proof (proj1 (crt_unprocessed_zero_indexed moduli_l i result ltac:(lia)) NewPreH30) as Hzero.
    intros k Hk. apply Hzero. lia. }
  pose proof
    (crt_factor_quotient_bounds__product_progress
       remainders_l moduli_l i PreH13 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[_ Hmodulus] _].
  dump_pre_spatial.
  rewrite <- PreH15 in Hmodulus.
  lia.
Qed.

Lemma proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure : chinese_remainder_theorem_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3.
Qed.
