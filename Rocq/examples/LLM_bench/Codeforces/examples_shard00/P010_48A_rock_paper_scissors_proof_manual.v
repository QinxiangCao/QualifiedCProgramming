From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P010_48A_rock_paper_scissors_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P010_48A_rock_paper_scissors_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors_lib.
Local Open Scope sac.

Lemma proof_of_beats_return_wit_1_split_goal_1 : beats_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall row : Z, _ |- _ =>
    pose proof (H ia_pre ltac:(lia)) as Ha;
    pose proof (H ib_pre ltac:(lia)) as Hb
  end.
  destruct Ha as [[[Ha_len Ha_mem] Ha_cells] Ha_zero].
  destruct Hb as [[[Hb_len Hb_mem] Hb_cells] Hb_zero].
  pose proof (Ha_cells 0 ltac:(lia)) as Hac.
  pose proof (Hb_cells 0 ltac:(lia)) as Hbc.
  assert (R : forall i v, 0 <= i < Zlength game_mem ->
    Znth 0 (Znth i game_mem nil) None = Some v ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 = v /\
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
      (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i v Hi Hv.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    unfold Array2.mixed_val. rewrite Hv. split; [reflexivity|].
    rewrite <- Hv. rewrite replace_Znth_Znth.
    unfold Array2.replace_mixed_row. apply replace_Znth_Znth. }
  destruct (R ia_pre _ ltac:(lia) Hac) as [Ea Ua].
  destruct (R ib_pre _ ltac:(lia) Hbc) as [Eb Ub].
  clear R.
  rewrite Ua in *.
  rewrite Ea, Eb in *.
  dump_pre_spatial. intros.
  assert (G : forall i, 0 <= i < 3 -> Gesture (Znth i players nil)).
  { intros i Hi. assert (i=0 \/ i=1 \/ i=2) as Hcases by lia.
    destruct Hcases as [-> | [-> | ->]]; unfold Pre in *; tauto. }
  pose proof (G ia_pre ltac:(lia)) as Ga.
  pose proof (G ib_pre ltac:(lia)) as Gb.
  unfold Gesture in Ga, Gb.
  destruct Ga as [Ga | [Ga | Ga]]; destruct Gb as [Gb | [Gb | Gb]];
    rewrite Ga, Gb in *; unfold rock, paper, scissors, Znth in *; simpl in *;
    unfold Beats; intuition congruence.
Qed.

Lemma proof_of_beats_return_wit_1_split_goal_spatial : beats_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall row : Z, _ |- _ =>
    pose proof (H ia_pre ltac:(lia)) as Ha;
    pose proof (H ib_pre ltac:(lia)) as Hb
  end.
  destruct Ha as [[[Ha_len Ha_mem] Ha_cells] Ha_zero].
  destruct Hb as [[[Hb_len Hb_mem] Hb_cells] Hb_zero].
  pose proof (Ha_cells 0 ltac:(lia)) as Hac.
  pose proof (Hb_cells 0 ltac:(lia)) as Hbc.
  assert (R : forall i v, 0 <= i < Zlength game_mem ->
    Znth 0 (Znth i game_mem nil) None = Some v ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 = v /\
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
      (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i v Hi Hv.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    unfold Array2.mixed_val. rewrite Hv. split; [reflexivity|].
    rewrite <- Hv. rewrite replace_Znth_Znth.
    unfold Array2.replace_mixed_row. apply replace_Znth_Znth. }
  destruct (R ia_pre _ ltac:(lia) Hac) as [Ea Ua].
  destruct (R ib_pre _ ltac:(lia) Hbc) as [Eb Ub].
  clear R.
  rewrite Ua in *.
  rewrite Ub. cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_1 : beats_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_beats_return_wit_2_split_goal_1 : beats_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall row : Z, _ |- _ =>
    pose proof (H ia_pre ltac:(lia)) as Ha;
    pose proof (H ib_pre ltac:(lia)) as Hb
  end.
  destruct Ha as [[[Ha_len Ha_mem] Ha_cells] Ha_zero].
  destruct Hb as [[[Hb_len Hb_mem] Hb_cells] Hb_zero].
  pose proof (Ha_cells 0 ltac:(lia)) as Hac.
  pose proof (Hb_cells 0 ltac:(lia)) as Hbc.
  assert (R : forall i v, 0 <= i < Zlength game_mem ->
    Znth 0 (Znth i game_mem nil) None = Some v ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 = v /\
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
      (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i v Hi Hv.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    unfold Array2.mixed_val. rewrite Hv. split; [reflexivity|].
    rewrite <- Hv. rewrite replace_Znth_Znth.
    unfold Array2.replace_mixed_row. apply replace_Znth_Znth. }
  destruct (R ia_pre _ ltac:(lia) Hac) as [Ea Ua].
  destruct (R ib_pre _ ltac:(lia) Hbc) as [Eb Ub].
  clear R.
  rewrite Ua in *.
  rewrite Ea, Eb in *.
  dump_pre_spatial. intros.
  assert (G : forall i, 0 <= i < 3 -> Gesture (Znth i players nil)).
  { intros i Hi. assert (i=0 \/ i=1 \/ i=2) as Hcases by lia.
    destruct Hcases as [-> | [-> | ->]]; unfold Pre in *; tauto. }
  pose proof (G ia_pre ltac:(lia)) as Ga.
  pose proof (G ib_pre ltac:(lia)) as Gb.
  unfold Gesture in Ga, Gb.
  destruct Ga as [Ga | [Ga | Ga]]; destruct Gb as [Gb | [Gb | Gb]];
    rewrite Ga, Gb in *; unfold rock, paper, scissors, Znth in *; simpl in *;
    unfold Beats; intuition congruence.
Qed.

Lemma proof_of_beats_return_wit_2_split_goal_spatial : beats_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall row : Z, _ |- _ =>
    pose proof (H ia_pre ltac:(lia)) as Ha;
    pose proof (H ib_pre ltac:(lia)) as Hb
  end.
  destruct Ha as [[[Ha_len Ha_mem] Ha_cells] Ha_zero].
  destruct Hb as [[[Hb_len Hb_mem] Hb_cells] Hb_zero].
  pose proof (Ha_cells 0 ltac:(lia)) as Hac.
  pose proof (Hb_cells 0 ltac:(lia)) as Hbc.
  assert (R : forall i v, 0 <= i < Zlength game_mem ->
    Znth 0 (Znth i game_mem nil) None = Some v ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 = v /\
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
      (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i v Hi Hv.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    unfold Array2.mixed_val. rewrite Hv. split; [reflexivity|].
    rewrite <- Hv. rewrite replace_Znth_Znth.
    unfold Array2.replace_mixed_row. apply replace_Znth_Znth. }
  destruct (R ia_pre _ ltac:(lia) Hac) as [Ea Ua].
  destruct (R ib_pre _ ltac:(lia) Hbc) as [Eb Ub].
  clear R.
  rewrite Ua in *.
  rewrite Ub. cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_2 : beats_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_beats_return_wit_3_split_goal_1 : beats_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  pose proof (Hread ia_pre ltac:(lia)) as Ha_read.
  pose proof (Hread ib_pre ltac:(lia)) as Hb_read.
  dump_pre_spatial. intros _ HB. unfold Beats in HB.
  destruct HB as [[Ha Hb] | [[Ha Hb] | [Ha Hb]]];
    rewrite Ha, Hb in *; unfold rock, paper, scissors in Ha_read, Hb_read; rewrite Znth0_cons in Ha_read, Hb_read; lia.
Qed.

Lemma proof_of_beats_return_wit_3_split_goal_spatial : beats_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_3 : beats_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_beats_return_wit_4_split_goal_1 : beats_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall row : Z, _ |- _ =>
    pose proof (H ia_pre ltac:(lia)) as Ha;
    pose proof (H ib_pre ltac:(lia)) as Hb
  end.
  destruct Ha as [[[Ha_len Ha_mem] Ha_cells] Ha_zero].
  destruct Hb as [[[Hb_len Hb_mem] Hb_cells] Hb_zero].
  pose proof (Ha_cells 0 ltac:(lia)) as Hac.
  pose proof (Hb_cells 0 ltac:(lia)) as Hbc.
  assert (R : forall i v, 0 <= i < Zlength game_mem ->
    Znth 0 (Znth i game_mem nil) None = Some v ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 = v /\
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
      (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i v Hi Hv.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    unfold Array2.mixed_val. rewrite Hv. split; [reflexivity|].
    rewrite <- Hv. rewrite replace_Znth_Znth.
    unfold Array2.replace_mixed_row. apply replace_Znth_Znth. }
  destruct (R ia_pre _ ltac:(lia) Hac) as [Ea Ua].
  destruct (R ib_pre _ ltac:(lia) Hbc) as [Eb Ub].
  clear R.
  rewrite Ua in *.
  rewrite Ea, Eb in *.
  dump_pre_spatial. intros.
  assert (G : forall i, 0 <= i < 3 -> Gesture (Znth i players nil)).
  { intros i Hi. assert (i=0 \/ i=1 \/ i=2) as Hcases by lia.
    destruct Hcases as [-> | [-> | ->]]; unfold Pre in *; tauto. }
  pose proof (G ia_pre ltac:(lia)) as Ga.
  pose proof (G ib_pre ltac:(lia)) as Gb.
  unfold Gesture in Ga, Gb.
  destruct Ga as [Ga | [Ga | Ga]]; destruct Gb as [Gb | [Gb | Gb]];
    rewrite Ga, Gb in *; unfold rock, paper, scissors, Znth in *; simpl in *;
    unfold Beats; intuition congruence.
Qed.

Lemma proof_of_beats_return_wit_4_split_goal_spatial : beats_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall row : Z, _ |- _ =>
    pose proof (H ia_pre ltac:(lia)) as Ha;
    pose proof (H ib_pre ltac:(lia)) as Hb
  end.
  destruct Ha as [[[Ha_len Ha_mem] Ha_cells] Ha_zero].
  destruct Hb as [[[Hb_len Hb_mem] Hb_cells] Hb_zero].
  pose proof (Ha_cells 0 ltac:(lia)) as Hac.
  pose proof (Hb_cells 0 ltac:(lia)) as Hbc.
  assert (R : forall i v, 0 <= i < Zlength game_mem ->
    Znth 0 (Znth i game_mem nil) None = Some v ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 = v /\
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
      (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i v Hi Hv.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    unfold Array2.mixed_val. rewrite Hv. split; [reflexivity|].
    rewrite <- Hv. rewrite replace_Znth_Znth.
    unfold Array2.replace_mixed_row. apply replace_Znth_Znth. }
  destruct (R ia_pre _ ltac:(lia) Hac) as [Ea Ua].
  destruct (R ib_pre _ ltac:(lia) Hbc) as [Eb Ub].
  clear R.
  rewrite Ua in *.
  rewrite Ub. cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_4 : beats_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_4_split_goal_1.
Qed. 

Lemma proof_of_beats_return_wit_5_split_goal_1 : beats_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  pose proof (Hread ia_pre ltac:(lia)) as Ha_read.
  pose proof (Hread ib_pre ltac:(lia)) as Hb_read.
  dump_pre_spatial. intros _ HB. unfold Beats in HB.
  destruct HB as [[Ha Hb] | [[Ha Hb] | [Ha Hb]]];
    rewrite Ha, Hb in *; unfold rock, paper, scissors in Ha_read, Hb_read; rewrite Znth0_cons in Ha_read, Hb_read; lia.
Qed.

Lemma proof_of_beats_return_wit_5_split_goal_spatial : beats_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_5 : beats_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_5_split_goal_1.
Qed. 

Lemma proof_of_beats_return_wit_6_split_goal_1 : beats_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  pose proof (Hread ia_pre ltac:(lia)) as Ha_read.
  pose proof (Hread ib_pre ltac:(lia)) as Hb_read.
  dump_pre_spatial. intros _ HB. unfold Beats in HB.
  destruct HB as [[Ha Hb] | [[Ha Hb] | [Ha Hb]]];
    rewrite Ha, Hb in *; unfold rock, paper, scissors in Ha_read, Hb_read; rewrite Znth0_cons in Ha_read, Hb_read; lia.
Qed.

Lemma proof_of_beats_return_wit_6_split_goal_spatial : beats_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_6 : beats_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_6_split_goal_1.
Qed. 

Lemma proof_of_beats_return_wit_7_split_goal_1 : beats_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  pose proof (Hread ia_pre ltac:(lia)) as Ha_read.
  pose proof (Hread ib_pre ltac:(lia)) as Hb_read.
  dump_pre_spatial. intros _ HB. unfold Beats in HB.
  destruct HB as [[Ha Hb] | [[Ha Hb] | [Ha Hb]]];
    rewrite Ha, Hb in *; unfold rock, paper, scissors in Ha_read, Hb_read; rewrite Znth0_cons in Ha_read, Hb_read; lia.
Qed.

Lemma proof_of_beats_return_wit_7_split_goal_spatial : beats_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall i, 0 <= i < 3 ->
    Znth 0 (Znth i game_mem __default__List__App_option_Z) None =
    Some (Znth 0 (Znth i players nil) 0)).
  { intros i Hi.
    rewrite (Znth_indep game_mem i __default__List__App_option_Z nil) by lia.
    match goal with
    | H : forall row : Z, _ |- _ =>
      specialize (H i Hi); destruct H as [[[Hlen Hrow] Hvals] Hnul];
      apply Hvals; lia
    end. }
  assert (Hread : forall i, 0 <= i < 3 ->
    Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0 =
    Znth 0 (Znth i players nil) 0).
  { intros i Hi. unfold Array2.mixed_val. rewrite (Hcell i Hi). reflexivity. }
  assert (Hback : forall i, 0 <= i < 3 ->
    Array2.replace_mixed_row i
      (replace_Znth 0 (Some (Array2.mixed_val (Znth i game_mem __default__List__App_option_Z) 0))
        (Znth i game_mem __default__List__App_option_Z)) game_mem = game_mem).
  { intros i Hi. rewrite (Hread i Hi), <- (Hcell i Hi).
    apply Array2.replace_mixed_row_roundtrip. }
  rewrite (Hback ia_pre ltac:(lia)) in *.
  try rewrite (Hback ib_pre ltac:(lia)) in *.
  cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
Qed.

Lemma proof_of_beats_return_wit_7 : beats_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_beats_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_beats_return_wit_7_split_goal_1.
Qed. 

Lemma proof_of_beats_partial_solve_wit_1_pure_split_goal_1 : beats_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_indep game_mem ia_pre _ nil) by lia.
  unfold Array2.mixed_def.
  match goal with
  | H : forall row : Z, _ |- _ =>
    let Hr := fresh "Hr" in
    pose proof (H ia_pre ltac:(lia)) as Hr;
    destruct Hr as [[[Hpositive Hlen] Hcells] Hnul];
    exists (Znth 0 (Znth ia_pre players nil) 0);
    apply Hcells; lia
  end.
Qed.

Lemma proof_of_beats_partial_solve_wit_1_pure : beats_partial_solve_wit_1_pure.
Proof. aggressive_pre_process. Goal_apply proof_of_beats_partial_solve_wit_1_pure_split_goal_1. Qed. 

Lemma proof_of_beats_partial_solve_wit_2_pure_split_goal_1 : beats_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold Array2.replace_mixed_row.
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite (Znth_indep game_mem ib_pre _ nil) by lia.
  unfold Array2.mixed_def.
  match goal with
  | H : forall row : Z, _ |- _ =>
    let Hr := fresh "Hr" in
    pose proof (H ib_pre ltac:(lia)) as Hr;
    destruct Hr as [[[Hpositive Hlen] Hcells] Hnul];
    exists (Znth 0 (Znth ib_pre players nil) 0);
    apply Hcells; lia
  end.
Qed.

Lemma proof_of_beats_partial_solve_wit_2_pure : beats_partial_solve_wit_2_pure.
Proof. aggressive_pre_process. Goal_apply proof_of_beats_partial_solve_wit_2_pure_split_goal_1. Qed. 

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (63 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      assert (H0 := PreH8 0 ltac:(lia)).
      assert (H1 := PreH8 1 ltac:(lia)).
      assert (H2 := PreH8 2 ltac:(lia)).
      cbn in H0, H1, H2.
      unfold Spec.
      right; right; right.
      split; [reflexivity |].
      split; [exact H0 |].
      split.
      * intros [H10 H12].
        apply H1.
        split; assumption.
      * exact H2.
    + dump_pre_spatial.
      reflexivity.
Qed. 

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  pose proof (PreH5 PreH2) as H2.
  pose proof (PreH10 PreH7) as H1.
  cbn in H1, H2.
  Exists (70 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      left.
      split; [reflexivity |].
      split; [exact H1 | exact H2].
    + dump_pre_spatial.
      reflexivity.
Qed. 

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  pose proof (PreH6 PreH3) as H2.
  pose proof (PreH11 PreH8) as H1.
  cbn in H1, H2.
  Exists (77 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      right; left.
      split; [reflexivity |].
      split; [exact H2 | exact H1].
    + dump_pre_spatial.
      reflexivity.
Qed. 

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = 2) by lia.
  subst i.
  pose proof (PreH6 PreH3) as H2.
  pose proof (PreH11 PreH8) as H1.
  cbn in H1, H2.
  Exists (83 :: nil).
  split_pure_spatial.
  - cancel (CharArray2.mixed_full g_pre 3 16 game_mem).
  - split_pures.
    + dump_pre_spatial.
      unfold Spec.
      right; right; left.
      split; [reflexivity |].
      split; [exact H1 | exact H2].
    + dump_pre_spatial.
      reflexivity.
Qed. 

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
  destruct Hi as [-> | [-> | ->]]; vm_compute; congruence.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_2 : solver_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
  destruct Hi as [-> | [-> | ->]]; vm_compute; congruence.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_3 : solver_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
  destruct Hi as [-> | [-> | ->]]; vm_compute; discriminate.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_4 : solver_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros row Hr.
  match goal with H : forall r : Z, 0 <= r /\ r < 3 -> _ |- _ =>
    pose proof (H row Hr) as Hrow
  end.
  assert (0 < Zlength (Znth row players nil)) as Hpositive.
  { assert (row = 0 \/ row = 1 \/ row = 2) as Hcases by lia.
    destruct Hcases as [-> | [-> | ->]];
      match goal with H : Pre _ _ _ |- _ => unfold Pre in H end;
      match goal with |- 0 < Zlength ?g => assert (Gesture g) as HG by tauto end;
      unfold Gesture in HG; destruct HG as [HG | [HG | HG]];
      rewrite HG; vm_compute; reflexivity. }
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_4.
Qed. 

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
  destruct Hi as [-> | [-> | ->]]; vm_compute; congruence.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
  destruct Hi as [-> | [-> | ->]]; vm_compute; congruence.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_3 : solver_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
  destruct Hi as [-> | [-> | ->]]; vm_compute; discriminate.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_4 : solver_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros row Hr.
  match goal with H : forall r : Z, 0 <= r /\ r < 3 -> _ |- _ =>
    pose proof (H row Hr) as Hrow
  end.
  assert (0 < Zlength (Znth row players nil)) as Hpositive.
  { assert (row = 0 \/ row = 1 \/ row = 2) as Hcases by lia.
    destruct Hcases as [-> | [-> | ->]];
      match goal with H : Pre _ _ _ |- _ => unfold Pre in H end;
      match goal with |- 0 < Zlength ?g => assert (Gesture g) as HG by tauto end;
      unfold Gesture in HG; destruct HG as [HG | [HG | HG]];
      rewrite HG; vm_compute; reflexivity. }
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_4.
Qed. 
