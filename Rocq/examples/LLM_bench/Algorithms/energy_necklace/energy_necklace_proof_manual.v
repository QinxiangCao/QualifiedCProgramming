From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.energy_necklace Require Import energy_necklace_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg IntArray.mixed_full IntArray.mixed_seg.

Require Import AUXLib.MonotonicList.

Ltac energy_math :=
  try solve [assumption | reflexivity | eapply energy_bounds_reuse; (eassumption || lia)];
  repeat match goal with
  | H : Forall2 eq (sublist ?lo ?hi ?xs) (sublist ?olo ?ohi ?ys) |- _ =>
    let K := fresh "SegmentAgreement" in
    pose proof ((proj1 (energy_segments_agree xs ys lo hi olo ohi ltac:(lia) ltac:(lia) ltac:(lia))) H) as K; clear H
  | |- Forall2 eq (sublist ?lo ?hi ?xs) (sublist ?olo ?ohi ?ys) =>
    apply (proj2 (energy_segments_agree xs ys lo hi olo ohi ltac:(lia) ltac:(lia) ltac:(lia)))
  end;
  repeat match goal with
  | H : EnergyComputationBounded ?beads ?n 2100000000 |- _ =>
    let K := fresh "ExpandedBounds" in
    pose proof (energy_bounds_expand beads n H) as K; clear H; destruct K as [? [? ?]]
  end;
  unfold EnergyComputationBounded, EnergySplitArithmeticBounded, EnergySplitBest, EnergyLeftComplete,
    EnergyLengthsComplete, EnergyUpdatedCell, EnergyAnswerBest, EnergyCellIndex in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  repeat match goal with
    | H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H
    | |- Forall ?P ?l => apply (proj2 (Forall_Znth P 0 l))
  end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end]; try lia;
  try solve [intros; repeat split; eauto 3; lia];
  try solve [intuition lia];
  try solve [intros; match goal with H : forall j : Z, _ -> _ |- _ => apply H; lia end];
  try solve [intros; match goal with |- context[Znth ?i ?xs 0] =>
    repeat match goal with H : forall j : Z, _ -> _ |- _ =>
      let K := fresh "AtIndex" in
      pose proof (H i ltac:(lia)) as K; clear H
    end; lia
  end].

(* Current generated split goals; the witnesses below use the whole-goal route. *)
Lemma proof_of_energyNecklace_safety_wit_25_split_goal_1 : energyNecklace_safety_wit_25_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_25_split_goal_2 : energyNecklace_safety_wit_25_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_27_split_goal_1 : energyNecklace_safety_wit_27_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_27_split_goal_2 : energyNecklace_safety_wit_27_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_31_split_goal_1 : energyNecklace_safety_wit_31_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_31_split_goal_2 : energyNecklace_safety_wit_31_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_32_split_goal_1 : energyNecklace_safety_wit_32_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_32_split_goal_2 : energyNecklace_safety_wit_32_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_1_split_goal_1 : energyNecklace_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_1_split_goal_2 : energyNecklace_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_1_split_goal_3 : energyNecklace_entail_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_1_split_goal_spatial : energyNecklace_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_2_split_goal_1 : energyNecklace_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_2_split_goal_2 : energyNecklace_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_6_split_goal_1 : energyNecklace_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_6_split_goal_2 : energyNecklace_entail_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_8_split_goal_1 : energyNecklace_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_8_split_goal_2 : energyNecklace_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_9_split_goal_1 : energyNecklace_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_9_split_goal_2 : energyNecklace_entail_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_10_split_goal_1 : energyNecklace_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_10_split_goal_2 : energyNecklace_entail_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_10_split_goal_3 : energyNecklace_entail_wit_10_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_11_split_goal_1 : energyNecklace_entail_wit_11_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_11_split_goal_2 : energyNecklace_entail_wit_11_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_11_split_goal_3 : energyNecklace_entail_wit_11_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_12_1_split_goal_1 : energyNecklace_entail_wit_12_1_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_12_1_split_goal_2 : energyNecklace_entail_wit_12_1_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_12_2_split_goal_1 : energyNecklace_entail_wit_12_2_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_12_2_split_goal_2 : energyNecklace_entail_wit_12_2_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_13_split_goal_1 : energyNecklace_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_14_split_goal_1 : energyNecklace_entail_wit_14_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_14_split_goal_2 : energyNecklace_entail_wit_14_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_14_split_goal_3 : energyNecklace_entail_wit_14_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_14_split_goal_4 : energyNecklace_entail_wit_14_split_goal_4.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_15_split_goal_1 : energyNecklace_entail_wit_15_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_15_split_goal_2 : energyNecklace_entail_wit_15_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_15_split_goal_3 : energyNecklace_entail_wit_15_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_15_split_goal_4 : energyNecklace_entail_wit_15_split_goal_4.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_15_split_goal_5 : energyNecklace_entail_wit_15_split_goal_5.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_16_split_goal_1 : energyNecklace_entail_wit_16_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_16_split_goal_2 : energyNecklace_entail_wit_16_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_17_split_goal_1 : energyNecklace_entail_wit_17_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_17_split_goal_2 : energyNecklace_entail_wit_17_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_17_split_goal_3 : energyNecklace_entail_wit_17_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_18_split_goal_1 : energyNecklace_entail_wit_18_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_18_split_goal_2 : energyNecklace_entail_wit_18_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_18_split_goal_3 : energyNecklace_entail_wit_18_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_19_split_goal_1 : energyNecklace_entail_wit_19_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_19_split_goal_2 : energyNecklace_entail_wit_19_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_19_split_goal_3 : energyNecklace_entail_wit_19_split_goal_3.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_20_1_split_goal_1 : energyNecklace_entail_wit_20_1_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_20_1_split_goal_2 : energyNecklace_entail_wit_20_1_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_20_2_split_goal_1 : energyNecklace_entail_wit_20_2_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_20_2_split_goal_2 : energyNecklace_entail_wit_20_2_split_goal_2.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_21_split_goal_1 : energyNecklace_entail_wit_21_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_22_split_goal_1 : energyNecklace_entail_wit_22_split_goal_1.
Proof. Abort.

Lemma proof_of_energyNecklace_entail_wit_22_split_goal_spatial : energyNecklace_entail_wit_22_split_goal_spatial.
Proof. Abort.

Lemma proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext30 : ((((0 <= total /\ width = total /\ Zlength vals_l = total /\ Zlength dp_l = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l dp_l width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l dp_l width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\ (left +
    len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l dp_l width len left split best) )) by energy_math.
  assert (Hcontext31 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.

  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       Hcontext32 PreH29 PreH1 PreH2 (conj PreH7 PreH8) (conj PreH9 PreH10)
       PreH11 (conj PreH12 PreH13) PreH28 Hcontext30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [Hgain _]]].
  split_pures; dump_pre_spatial; lia.

Qed.

Lemma proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext30 : ((((0 <= total /\ width = total /\ Zlength vals_l = total /\ Zlength dp_l = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l dp_l width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l dp_l width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\ (left +
    len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l dp_l width len left split best) )) by energy_math.
  assert (Hcontext31 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.

  pose proof
    (EnergyValsDuplicated_label_bound__arithmetic_safety_bounds
       beads_l vals_l n_pre left PreH29 Hcontext31) as Hleft_bound.
  pose proof
    (EnergyValsDuplicated_label_bound__arithmetic_safety_bounds
       beads_l vals_l n_pre (split + 1) PreH29 Hcontext31) as Hsplit_bound.
  specialize (Hleft_bound ltac:(lia)).
  specialize (Hsplit_bound ltac:(lia)).
  split_pures; dump_pre_spatial; nia.

Qed.

Lemma proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext30 : ((((0 <= total /\ width = total /\ Zlength vals_l = total /\ Zlength dp_l = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l dp_l width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l dp_l width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\ (left +
    len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l dp_l width len left split best) )) by energy_math.
  assert (Hcontext31 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.

  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       Hcontext32 PreH29 PreH1 PreH2 (conj PreH7 PreH8) (conj PreH9 PreH10)
       PreH11 (conj PreH12 PreH13) PreH28 Hcontext30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [_ [_ Hcandidate]]]].
  split_pures; dump_pre_spatial; lia.

Qed.

Lemma proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext30 : ((((0 <= total /\ width = total /\ Zlength vals_l = total /\ Zlength dp_l = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l dp_l width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l dp_l width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\ (left +
    len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l dp_l width len left split best) )) by energy_math.
  assert (Hcontext31 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.

  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       Hcontext32 PreH29 PreH1 PreH2 (conj PreH7 PreH8) (conj PreH9 PreH10)
       PreH11 (conj PreH12 PreH13) PreH28 Hcontext30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [_ [Hsum _]]]].
  split_pures; dump_pre_spatial; lia.

Qed.

Lemma proof_of_energyNecklace_entail_wit_1 : energyNecklace_entail_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  sep_apply (scratch_undef_full_split (&("vals")) (2*n_pre) 200 ltac:(nia)).
  sep_apply (scratch_undef_full_split (&("dp")) ((2*n_pre)*(2*n_pre)) 40000 ltac:(nia)).
  sep_apply (IntArray.undef_full_to_undef_seg (&("vals")) (2*n_pre)).
  Exists (@nil Z). rewrite IntArray.seg_empty.
  split_pure_spatial; [repeat cancel; try reflexivity |].
  split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0))))
    by energy_math.
  assert (Hcontext13 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hcopy : forall j, 0 <= j < i + 1 ->
    Znth j (vals_l_2 ++ Znth i beads_l 0 :: nil) 0 = Znth j beads_l 0).
  { intros j Hj. destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
    - rewrite app_Znth1 by lia. apply Hcontext12; lia.
    - assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia. rewrite PreH9.
      replace (i - i) with 0 by lia. reflexivity. }
  assert (Hlength : Zlength (vals_l_2 ++ Znth i beads_l 0 :: nil) = i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  Exists (vals_l_2 ++ Znth i beads_l 0 :: nil).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 vals_l_2 0) = (Znth k_2
    beads_l 0)))) by energy_math.
  assert (Hcontext13 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  replace i with n_pre in * by lia.
  replace (n_pre + 0) with n_pre by lia.
  Exists vals_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l
    0)))) by energy_math.
  assert (Hcontext13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) =
    (Znth k_2 beads_l 0)))) by energy_math.
  assert (Hcontext14 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hcopy_low : forall j, 0 <= j < n_pre ->
    Znth j (vals_l_2 ++ Znth i beads_l 0 :: nil) 0 = Znth j beads_l 0).
  { intros j Hj. rewrite app_Znth1 by lia. apply Hcontext12; lia. }
  assert (Hcopy_high : forall j, 0 <= j < i + 1 ->
    Znth (n_pre + j) (vals_l_2 ++ Znth i beads_l 0 :: nil) 0 = Znth j beads_l 0).
  { intros j Hj. destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
    - rewrite app_Znth1 by lia. apply Hcontext13; lia.
    - assert (j = i) by lia. subst j.
      rewrite app_Znth2 by lia. rewrite PreH9.
      replace (n_pre + i - (n_pre + i)) with 0 by lia. reflexivity. }
  assert (Hlength : Zlength (vals_l_2 ++ Znth i beads_l 0 :: nil) = n_pre + (i + 1)).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  replace (n_pre + (i + 1)) with ((n_pre + i) + 1) by lia.
  Exists (vals_l_2 ++ Znth i beads_l 0 :: nil).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hwork_nonnegative : 0 <= total * width) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hcontext12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l
    0)))) by energy_math.
  assert (Hcontext13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) =
    (Znth k_2 beads_l 0)))) by energy_math.
  assert (Hcontext14 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hduplicated : EnergyValsDuplicated beads_l vals_l_2 n_pre).
  { unfold EnergyValsDuplicated. repeat split; try lia;
      intros j Hj; [apply Hcontext12 | apply Hcontext13]; lia. }
  replace i with n_pre in * by lia.
  replace (n_pre + n_pre) with total by lia.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full (&("vals")) 0 total vals_l_2).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  sep_apply (IntArray.undef_full_to_undef_seg (&("dp")) (total * width)).
  Exists vals_l_2 (@nil Z).
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) by energy_math.
  assert (Hcontext14 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hzero : Forall (eq 0) (dp_l_2 ++ 0 :: nil)).
  { apply Forall_app. split; [assumption | repeat constructor]. }
  assert (Hlength : Zlength (dp_l_2 ++ 0 :: nil) = i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  Exists vals_l_2 (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) by energy_math.
  assert (Hcontext14 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hzero : (0 <= total /\ width = total /\ Zlength dp_l_2 = total * width /\ Forall (eq 0) dp_l_2)).
  { apply EnergyZeroTable_from_prefix__prefix_table_bootstrap with (i := total * width);
      try lia; auto.
    intros j Hj. apply Hcontext12; lia. }
  assert (Hdone : (0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total * width
    /\ 1 <= 2 /\ EnergyLengthsComplete vals_l_2 dp_l_2 width 2)).
  { apply EnergyZeroTable_len_done_2__prefix_table_bootstrap; [| exact Hzero].
    unfold EnergyValsDuplicated in PreH13. intuition lia. }
  replace i with (total * width) in * by lia.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full (&("dp")) 0 (total * width) dp_l_2).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext13 : ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) )) by energy_math.
  assert (Hcontext14 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext15 : (((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) )) by energy_math.
  assert (Hcontext16 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext24 : ((((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\
    (left + len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l_2 dp_l_2 width len left split best) )) by energy_math.
  assert (Hcontext25 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_11 : energyNecklace_entail_wit_11.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext30 : ((((0 <= total /\ width = total /\ Zlength vals_l = total /\ Zlength dp_l = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l dp_l width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l dp_l width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\ (left +
    len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l dp_l width len left split best) )) by energy_math.
  assert (Hcontext31 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hdone : (0 <= total /\ width = total /\ Zlength vals_l = total /\ Zlength dp_l = total * width /\ 1
    <= len /\ EnergyLengthsComplete vals_l dp_l width len))
    by (unfold EnergySplitBest, EnergyLeftComplete in Hcontext30; tauto).
  pose proof Hcontext32 as Hcomp_bound.
  destruct Hcomp_bound as [_ [Hsplit_bound [_ _]]].
  specialize (Hsplit_bound vals_l dp_l total width len left right split
                PreH29 PreH1 PreH2 ltac:(lia) ltac:(lia) PreH11
                ltac:(lia) PreH28 Hdone).
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hsplit_bound.
  destruct Hsplit_bound as [_ [_ [_ [_ Hcandidate_bound]]]].
  Exists vals_l dp_l.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_12_1 : energyNecklace_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext27 : ((((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\
    (left + len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l_2 dp_l_2 width len left split best) )) by energy_math.
  assert (Hcontext28 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hzvals : Zlength vals_l_2 = total)
    by (unfold EnergySplitBest, EnergyLeftComplete, EnergyLengthsComplete in Hcontext27; tauto).
  assert (Hcand : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate).
  {
    unfold EnergySplitCandidate, EnergyCellIndex.
    repeat split; try lia.
  }
  pose proof (EnergySplitProgress_step_take__dp_interval_progress
                vals_l_2 dp_l_2 total width len left right split best candidate
                PreH12 ltac:(lia) Hcontext27 Hcand ltac:(lia) ltac:(lia)) as Hstep.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_12_2 : energyNecklace_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext27 : ((((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\
    (left + len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l_2 dp_l_2 width len left split best) )) by energy_math.
  assert (Hcontext28 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hzvals : Zlength vals_l_2 = total)
    by (unfold EnergySplitBest, EnergyLeftComplete, EnergyLengthsComplete in Hcontext27; tauto).
  assert (Hcand : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate).
  {
    unfold EnergySplitCandidate, EnergyCellIndex.
    repeat split; try lia.
  }
  pose proof (EnergySplitProgress_step_keep__dp_interval_progress
                vals_l_2 dp_l_2 total width len left right split best candidate
                PreH12 ltac:(lia) Hcontext27 Hcand PreH22 PreH1) as Hstep.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13.
Proof.
  LLM_pre_process ltac:(assumption).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext24 : ((((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\
    (left + len - 1) = left + len - 1 /\ left <= split <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l_2 dp_l_2 width len left split best) )) by energy_math.
  assert (Hcontext25 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hvals_len : Zlength vals_l_2 = total)
    by (unfold EnergySplitBest, EnergyLeftComplete, EnergyLengthsComplete in Hcontext24; tauto).
  assert (Hinterval : EnergyIntervalBest vals_l_2 left right best).
  {
    eapply EnergySplitProgress_finish_interval_best__dp_interval_progress.
    - exact PreH12.
    - exact PreH1.
    - rewrite Hvals_len; exact PreH16.
    - exact Hcontext24.
  }
  assert (Hsplit_right : (((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total
    * width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\
    (left + len - 1) = left + len - 1 /\ left <= right <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l_2 dp_l_2 width len left right best)).
  {
    replace right with split by lia.
    exact Hcontext24.
  }
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext20 : ((((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) /\ 2 <= len /\ 0 <= left /\ left + len <= total /\
    (left + len - 1) = left + len - 1 /\ left <= right <= (left + len - 1) /\ 0 <= best <= 2100000000 /\
    EnergySplitBest vals_l_2 dp_l_2 width len left right best) )) by energy_math.
  assert (Hcontext22 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hupdated :
            EnergyUpdatedCell vals_l_2 dp_l_2
              (replace_Znth ((left * width) + right) best dp_l_2)
              width left right best).
  {
    unfold EnergyUpdatedCell.
    split.
    - rewrite PreH18.
      unfold EnergyCellIndex; lia.
    - split.
      + unfold EnergyCellIndex; reflexivity.
      + exact PreH35.
  }
  assert (Hleft_progress :
            ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength (replace_Znth ((left * width)
              + right) best dp_l_2) = total * width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2
              (replace_Znth ((left * width) + right) best dp_l_2) width len) /\ 2 <= len /\ 0 <= (left + 1) /\
              EnergyLeftComplete vals_l_2 (replace_Znth ((left * width) + right) best dp_l_2) width len (left
              + 1))).
  {
    change (replace_Znth ((left * width) + right) best dp_l_2) with
      (replace_Znth (EnergyCellIndex width left right) best dp_l_2).
    apply EnergyLeftProgress_step_update__dp_interval_progress with (right := right);
      try assumption; try lia.
  }
  Exists vals_l_2 (replace_Znth ((left * width) + right) best dp_l_2).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext15 : (((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) /\ 2 <= len /\ 0 <= left /\
    EnergyLeftComplete vals_l_2 dp_l_2 width len left) )) by energy_math.
  assert (Hcontext16 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hdone_next :
            (0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total * width /\ 1 <=
              (len + 1) /\ EnergyLengthsComplete vals_l_2 dp_l_2 width (len + 1))).
  {
    apply EnergyLeftProgress_finish_len__dp_interval_progress with (left := left);
      try assumption; try lia.
  }
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_17 : energyNecklace_entail_wit_17.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext13 : ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= len /\ EnergyLengthsComplete vals_l_2 dp_l_2 width len) )) by energy_math.
  assert (Hcontext14 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  assert (Hdone_next : (0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= (n_pre + 1) /\ EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))).
  { replace (n_pre + 1) with len by lia. exact Hcontext13. }
  assert (Hanswer : (EnergyValsDuplicated beads_l vals_l_2 n_pre /\ Zlength dp_l_2 = total * width /\ width =
    total /\ 0 <= 0 <= n_pre /\ 0 <= 0 <= 2100000000 /\ EnergyAnswerBest vals_l_2 n_pre 0 0)).
  { unfold EnergyAnswerBest.
    repeat split; try assumption; try lia.
    all: try solve
      [ unfold EnergyValsDuplicated in PreH12;
        destruct PreH12 as [_ [_ [Hvals [Hcopy_low Hcopy_high]]]];
        try lia; eauto
      | left; split; lia ]. }
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext15 : ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= (n_pre + 1 ) /\ EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 )) )) by energy_math.
  assert (Hcontext16 : ((EnergyValsDuplicated beads_l vals_l_2 n_pre /\ Zlength dp_l_2 = total * width /\
    width = total /\ 0 <= start <= n_pre /\ 0 <= answer <= 2100000000 /\ EnergyAnswerBest vals_l_2 n_pre start
    answer) )) by energy_math.
  assert (Hcontext17 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (EnergyLenDone_rotation_cell_best__answer_loop
    vals_l_2 dp_l_2 total width n_pre start
    PreH4 PreH2 PreH3 ltac:(lia) Hcontext15) as Hbest.
  unfold EnergyCellIndex in Hbest.
  replace (start * width + (start + n_pre - 1))
    with ((((start * width) + start) + n_pre) - 1) in Hbest by lia.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext14 : ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l = total *
    width /\ 1 <= (n_pre + 1 ) /\ EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1 )) )) by energy_math.
  assert (Hcontext15 : ((EnergyValsDuplicated beads_l vals_l_2 n_pre /\ Zlength dp_l = total * width /\ width
    = total /\ 0 <= start <= n_pre /\ 0 <= answer <= 2100000000 /\ EnergyAnswerBest vals_l_2 n_pre start
    answer) )) by energy_math.
  assert (Hcontext17 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (EnergyAnswerCellBounded__answer_loop
    beads_l vals_l_2 dp_l n_pre total width start
    Hcontext18 PreH13 PreH1 PreH2 ltac:(lia) PreH12 Hcontext14) as Hbounds.
  unfold EnergyCellIndex in Hbounds.
  replace (start * width + (start + n_pre - 1))
    with ((((start * width) + start) + n_pre) - 1) in Hbounds by lia.
  Exists vals_l_2 dp_l.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_20_1 : energyNecklace_entail_wit_20_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext16 : ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= (n_pre + 1 ) /\ EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 )) )) by energy_math.
  assert (Hcontext17 : ((EnergyValsDuplicated beads_l vals_l_2 n_pre /\ Zlength dp_l_2 = total * width /\
    width = total /\ 0 <= start <= n_pre /\ 0 <= answer <= 2100000000 /\ EnergyAnswerBest vals_l_2 n_pre start
    answer) )) by energy_math.
  assert (Hcontext19 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (EnergyAnswerProgress_step_update__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer value
    Hcontext17 ltac:(lia) PreH30 ltac:(lia) ltac:(lia)) as Hprogress_next.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_20_2 : energyNecklace_entail_wit_20_2.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext16 : ((0 <= total /\ width = total /\ Zlength vals_l_2 = total /\ Zlength dp_l_2 = total *
    width /\ 1 <= (n_pre + 1 ) /\ EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 )) )) by energy_math.
  assert (Hcontext17 : ((EnergyValsDuplicated beads_l vals_l_2 n_pre /\ Zlength dp_l_2 = total * width /\
    width = total /\ 0 <= start <= n_pre /\ 0 <= answer <= 2100000000 /\ EnergyAnswerBest vals_l_2 n_pre start
    answer) )) by energy_math.
  assert (Hcontext19 : ((Zlength beads_l = n_pre /\ Forall (fun value : Z => 1 <= value <= 1000) beads_l) ))
    by energy_math.
  assert (Hcontext20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (EnergyAnswerProgress_answer_bounds__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer Hcontext17) as Hanswer_bounds.
  pose proof (EnergyAnswerProgress_step_keep__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer value
    Hcontext17 ltac:(lia) PreH30 PreH11 PreH1) as Hprogress_next.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try nia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21.
Proof.
  LLM_pre_process ltac:(assumption).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hprogress : (EnergyValsDuplicated beads_l vals_l n_pre /\ Zlength dp_l = total * width /\ width =
    total /\ 0 <= start_2 <= n_pre /\ 0 <= answer <= 2100000000 /\ EnergyAnswerBest vals_l n_pre start_2
    answer)) by energy_math.
  pose proof (EnergyAnswerProgress_finish__answer_loop beads_l vals_l dp_l n_pre total width start_2 answer ltac:(lia) Hprogress ltac:(lia) ltac:(lia)) as Hanswer.
  subst width total.
  sep_apply (scratch_full_tail_undef (&("vals")) (2*n_pre) 200 vals_l ltac:(nia)).
  sep_apply (scratch_full_tail_undef (&("dp")) ((2*n_pre)*(2*n_pre)) 40000 dp_l ltac:(nia)).
  sep_apply_l_atomic (store_int_undef_store_int (&("total")) (2 * n_pre)).
  sep_apply_l_atomic (store_int_undef_store_int (&("width")) (2 * n_pre)).
  sep_apply_l_atomic (store_int_undef_store_int (&("answer")) answer).
  split_pure_spatial; [repeat cancel; try reflexivity |].
  split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math; try lia.
Qed.
