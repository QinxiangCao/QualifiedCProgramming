From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P062_1492D_geniuss_gambit_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P062_1492D_geniuss_gambit_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P062_1492D_geniuss_gambit_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold repeat_Z; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  unfold repeat_Z.
  apply repeat_Z_succ_app__initialization.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = b_pre) by lia.
  subst i.
  replace (b_pre - b_pre) with 0 by lia.
  replace (repeat_Z 48 0) with (@nil Z) by
    (unfold repeat_Z; reflexivity).
  rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i + 1 - b_pre) with ((i - b_pre) + 1) by lia.
  unfold repeat_Z.
  rewrite repeat_Z_succ_app__initialization by lia.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite !Zlength_app, !Zlength_cons, Zlength_nil.
  unfold repeat_Z.
  rewrite !Zlength_correct, !repeat_length.
  rewrite !Z2Nat.id by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold all_ascii.
  intros j Hj.
  assert (Hb : Zlength (repeat_Z 49 b_pre) = b_pre).
  {
    unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    reflexivity.
  }
  assert (Ha : Zlength (repeat_Z 48 a_pre) = a_pre).
  {
    unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    reflexivity.
  }
  destruct (Z_lt_ge_dec j b_pre) as [Hjb | Hjb].
  - rewrite app_Znth1 by (rewrite Hb; lia).
    unfold repeat_Z.
    rewrite Znth_repeat_lt by (rewrite Z2Nat.id; lia).
    lia.
  - rewrite app_Znth2 by (rewrite Hb; lia).
    rewrite Hb.
    destruct (Z_lt_ge_dec (j - b_pre) a_pre) as [Hja | Hja].
    + rewrite app_Znth1 by (rewrite Ha; lia).
      unfold repeat_Z.
      rewrite Znth_repeat_lt by (rewrite Z2Nat.id; lia).
      lia.
    + rewrite app_Znth2 by (rewrite Ha; lia).
      rewrite Ha.
      replace (j - b_pre - a_pre) with 0.
      * rewrite Znth0_cons.
        simpl. lia.
      * rewrite !Zlength_app, Hb, Ha, !Zlength_cons, Zlength_nil in Hj.
        lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n) by lia.
  subst i.
  replace (n - b_pre) with a_pre by lia.
  rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanonicalGambit, GambitY.
  rewrite Z.eqb_refl.
  apply gambit_pair_zero__canonical_construction; lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia.
    apply gambit_impossible_single_one__impossibility; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia.
    apply gambit_impossible_all_ones__impossibility; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_1 : solver_entail_wit_7_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (gambit_impossible_span__impossibility a_pre b_pre k_pre n); lia.
Qed.

Lemma proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply gambit_pair_le__canonical_construction; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply gambit_pair_gt__canonical_construction; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n. subst j. subst i_2.
  destruct (encode_gambit_x__successful_returns a_pre b_pre) as
      [HX [HLX HPX]]; try lia.
  pose proof (Zlength_gambit_y__successful_returns
    a_pre b_pre k_pre ltac:(lia) ltac:(lia)) as HLY.
  assert (HLGX : Zlength (GambitX a_pre b_pre) = a_pre + b_pre).
  {
    unfold GambitX. rewrite Zlength_app.
    rewrite !Zlength_correct, !repeat_length. lia.
  }
  assert (HLEY : Zlength (EncodeDigits (GambitY a_pre b_pre k_pre)) =
      a_pre + b_pre).
  { unfold EncodeDigits. rewrite Zlength_map__successful_returns. exact HLY. }
  assert (HPY : forall i, 0 <= i < a_pre + b_pre ->
      Znth i (EncodeDigits (GambitY a_pre b_pre k_pre)) 0 =
      Znth i (GambitY a_pre b_pre k_pre) 0 + 48).
  {
    intros i Hi. unfold EncodeDigits.
    rewrite (Znth_map__successful_returns (fun d : Z => d + 48)
      (GambitY a_pre b_pre k_pre) 0 0 i); [reflexivity|lia].
  }
  pose proof (encode_gambit_y_gt__successful_returns
    a_pre b_pre k_pre ltac:(lia) ltac:(lia) ltac:(lia)) as HY.
  unfold repeat_Z in HX.
  unfold repeat_Z.
  assert (HXT : EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil) =
      repeat 49 (Z.to_nat b_pre) ++
        (repeat 48 (Z.to_nat a_pre) ++ (0 :: nil))).
  { rewrite HX, app_assoc. reflexivity. }
  rewrite <- HXT, <- HY.
  Exists (EncodeDigits (GambitY a_pre b_pre k_pre))
    (EncodeDigits (GambitX a_pre b_pre))
    (GambitX a_pre b_pre) (GambitY a_pre b_pre k_pre)
    (Some (pair (GambitX a_pre b_pre) (GambitY a_pre b_pre k_pre))).
  split_pure_spatial.
  - cancel (CharArray.full x_pre (a_pre + b_pre + 1)
      (EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil))).
    cancel (CharArray.full y_pre (a_pre + b_pre + 1)
      (EncodeDigits (GambitY a_pre b_pre k_pre) ++ (0 :: nil))).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try reflexivity.
    all: try exact HLGX.
    all: try exact HLX.
    all: try exact HLY.
    all: try exact HLEY.
    all: try (unfold Spec; right;
      exists (GambitX a_pre b_pre, GambitY a_pre b_pre k_pre);
      split; [reflexivity|exact PreH18]).
    all: intros i Hi; split; [apply HPX | apply HPY]; lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n. subst i_2. subst j.
  destruct (encode_gambit_x__successful_returns a_pre b_pre) as
      [HX [HLX HPX]]; try lia.
  pose proof (Zlength_gambit_y__successful_returns
    a_pre b_pre k_pre ltac:(lia) ltac:(lia)) as HLY.
  assert (HLGX : Zlength (GambitX a_pre b_pre) = a_pre + b_pre).
  {
    unfold GambitX. rewrite Zlength_app.
    rewrite !Zlength_correct, !repeat_length. lia.
  }
  assert (HLEY : Zlength (EncodeDigits (GambitY a_pre b_pre k_pre)) =
      a_pre + b_pre).
  { unfold EncodeDigits. rewrite Zlength_map__successful_returns. exact HLY. }
  assert (HPY : forall i, 0 <= i < a_pre + b_pre ->
      Znth i (EncodeDigits (GambitY a_pre b_pre k_pre)) 0 =
      Znth i (GambitY a_pre b_pre k_pre) 0 + 48).
  {
    intros i Hi. unfold EncodeDigits.
    rewrite (Znth_map__successful_returns (fun d : Z => d + 48)
      (GambitY a_pre b_pre k_pre) 0 0 i); [reflexivity|lia].
  }
  pose proof (encode_gambit_y_le__successful_returns
    a_pre b_pre k_pre ltac:(lia) ltac:(lia)) as HY.
  unfold repeat_Z in HX.
  unfold repeat_Z.
  assert (HXT : EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil) =
      repeat 49 (Z.to_nat b_pre) ++
        (repeat 48 (Z.to_nat a_pre) ++ (0 :: nil))).
  { rewrite HX, app_assoc. reflexivity. }
  rewrite <- HXT, <- HY.
  Exists (EncodeDigits (GambitY a_pre b_pre k_pre))
    (EncodeDigits (GambitX a_pre b_pre))
    (GambitX a_pre b_pre) (GambitY a_pre b_pre k_pre)
    (Some (pair (GambitX a_pre b_pre) (GambitY a_pre b_pre k_pre))).
  split_pure_spatial.
  - cancel (CharArray.full x_pre (a_pre + b_pre + 1)
      (EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil))).
    cancel (CharArray.full y_pre (a_pre + b_pre + 1)
      (EncodeDigits (GambitY a_pre b_pre k_pre) ++ (0 :: nil))).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try reflexivity.
    all: try exact HLGX.
    all: try exact HLX.
    all: try exact HLY.
    all: try exact HLEY.
    all: try (unfold Spec; right;
      exists (GambitX a_pre b_pre, GambitY a_pre b_pre k_pre);
      split; [reflexivity|exact PreH18]).
    all: intros i Hi; split; [apply HPX | apply HPY]; lia.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply spec_none_of_impossible__impossible_returns.
  auto.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_spatial : solver_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  sep_apply_l_atomic
    (CharArray.full_to_full_shape x_pre (a_pre + b_pre + 1)
      (app (repeat_Z 49 b_pre) (app (repeat_Z 48 a_pre) (cons 0 nil)))).
  sep_apply_l_atomic
    (CharArray.full_to_full_shape y_pre (a_pre + b_pre + 1)
      (app (repeat_Z 49 b_pre) (app (repeat_Z 48 a_pre) (cons 0 nil)))).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply spec_none_of_impossible__impossible_returns.
  auto.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_spatial : solver_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  sep_apply_l_atomic
    (CharArray.full_to_full_shape x_pre (a_pre + b_pre + 1)
      (app (repeat_Z 49 b_pre) (app (repeat_Z 48 a_pre) (cons 0 nil)))).
  sep_apply_l_atomic
    (CharArray.full_to_full_shape y_pre (a_pre + b_pre + 1)
      (app (repeat_Z 49 b_pre) (app (repeat_Z 48 a_pre) (cons 0 nil)))).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_5_split_goal_1 : solver_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst a_pre.
  dump_pre_spatial.
  apply spec_none_of_impossible__impossible_returns.
  auto.
Qed.

Lemma proof_of_solver_return_wit_5_split_goal_spatial : solver_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  sep_apply_l_atomic
    (CharArray.full_to_full_shape x_pre (a_pre + b_pre + 1)
      (app (repeat_Z 49 b_pre) (app (repeat_Z 48 a_pre) (cons 0 nil)))).
  sep_apply_l_atomic
    (CharArray.full_to_full_shape y_pre (a_pre + b_pre + 1)
      (app (repeat_Z 49 b_pre) (app (repeat_Z 48 a_pre) (cons 0 nil)))).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_5 : solver_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_6 : solver_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n. subst k_pre.
  destruct (encode_gambit_x__successful_returns a_pre b_pre) as
      [HX [HLX HPX]]; try lia.
  assert (HLGX : Zlength (GambitX a_pre b_pre) = a_pre + b_pre).
  {
    unfold GambitX. rewrite Zlength_app.
    rewrite !Zlength_correct, !repeat_length. lia.
  }
  assert (HG : GambitY a_pre b_pre 0 = GambitX a_pre b_pre).
  { unfold GambitY. reflexivity. }
  unfold repeat_Z in HX.
  unfold repeat_Z.
  assert (HXT : EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil) =
      repeat 49 (Z.to_nat b_pre) ++
        (repeat 48 (Z.to_nat a_pre) ++ (0 :: nil))).
  { rewrite HX, app_assoc. reflexivity. }
  rewrite <- HXT.
  Exists (EncodeDigits (GambitX a_pre b_pre))
    (EncodeDigits (GambitX a_pre b_pre))
    (GambitX a_pre b_pre) (GambitX a_pre b_pre)
    (Some (pair (GambitX a_pre b_pre) (GambitX a_pre b_pre))).
  split_pure_spatial.
  - cancel (CharArray.full x_pre (a_pre + b_pre + 1)
      (EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil))).
    cancel (CharArray.full y_pre (a_pre + b_pre + 1)
      (EncodeDigits (GambitX a_pre b_pre) ++ (0 :: nil))).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try reflexivity.
    all: try exact HLGX.
    all: try exact HLX.
    all: try (unfold Spec; right;
      exists (GambitX a_pre b_pre, GambitX a_pre b_pre);
      split; [reflexivity|rewrite <- HG; exact PreH8]).
    all: intros i Hi; split; apply HPX; lia.
Qed.
