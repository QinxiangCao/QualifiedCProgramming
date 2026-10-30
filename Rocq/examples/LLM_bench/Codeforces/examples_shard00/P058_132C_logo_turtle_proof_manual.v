From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P058_132C_logo_turtle_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P058_132C_logo_turtle_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  unfold repeat_Z.
  change (TurtleLayerMeaning commands 0 n
    (replace_Znth (Zlength commands) 1
      (repeat 0 (Z.to_nat ((n + 1) * 2 * TurtleWidth commands))))).
  eapply turtle_layer_zero_table__init_layer; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length, Z2Nat.id.
  - reflexivity.
  - nia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length, Z2Nat.id.
  - reflexivity.
  - nia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply turtle_next_zero_table__init_layer.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length, Z2Nat.id.
  - reflexivity.
  - nia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst O.
  subst n.
  replace (2 * ((c * 2 + 0) * (2 * len + 1))) with (4 * c * W) by lia.
  exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst O.
  subst n.
  replace (2 * (((c * 2 + dir) * (2 * len + 1)) + 0))
    with (2 * ((c * 2 + dir) * W)) by lia.
  exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  subst O.
  subst n.
  replace (2 * (((c * 2 + dir) * (2 * len + 1) + pos)) + 0)
    with (2 * (((c * 2 + dir) * W) + pos)) by lia.
  exact PreH35.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite binary_lxor_one__direction_bit by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite binary_lxor_one__direction_bit by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite binary_lxor_one__direction_bit by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite binary_lxor_one__direction_bit by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply binary_destination_bound__direction_bit; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply binary_destination_bound__direction_bit; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_3_split_goal_1 : solver_entail_wit_8_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_4_split_goal_1 : solver_entail_wit_8_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_5_split_goal_1 : solver_entail_wit_8_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_6_split_goal_1 : solver_entail_wit_8_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_8_6 : solver_entail_wit_8_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst O W len.
  rewrite app_Znth1 in PreH25 by lia.
  specialize (PreH36 i ltac:(lia)).
  assert (Hcommand : Znth i commands 0 = 70) by tauto.
  assert (Hflip : flip = 1) by lia.
  assert (Hxor : Z.lxor dir 1 = 1 - dir).
  { assert (dir = 0 \/ dir = 1) as [-> | ->] by lia; reflexivity. }
  assert (Hreachable : PrefixReachable commands i c dir pos).
  { specialize (PreH53 c dir pos ltac:(lia) ltac:(lia)).
    specialize (PreH53 ltac:(unfold TurtleWidth; lia)).
    unfold TurtleCellIndex, TurtleWidth in PreH53.
    cbn beta in PreH53.
    destruct PreH53 as [[Hzero | Hone] Hmeaning].
    - exfalso. apply PreH47. exact Hzero.
    - apply Hmeaning. exact Hone. }
  subst flip.
  subst n.
  replace
    (2 * ((c * 2 + dir) * (2 * Zlength commands + 1) + pos) + (1 + 1))
    with ((2 * ((c * 2 + dir) * (2 * Zlength commands + 1) + pos) + 1) + 1)
    by lia.
  change (TurtleNextPrefix commands i changes_pre
    ((2 * TurtleCellIndex commands c dir pos + 1) + 1)
    (replace_Znth
      (TurtleCellIndex commands (c + 1) (Z.lxor dir 1) pos)
      1 next_table_2)).
  assert (Hone_bounds : (0 <= (1 : Z) < 2)) by (split; lia).
  eapply (turtle_next_prefix_write_one__next_update_core
    commands i changes_pre
    (2 * TurtleCellIndex commands c dir pos + 1)
    next_table_2 (c + 1) (Z.lxor dir 1) pos).
  - exact PreH54.
  - exact PreH52.
  - split; [lia|exact PreH26].
  - exact (conj PreH5 PreH6).
  - unfold TurtleWidth. exact (conj PreH43 PreH44).
  - unfold TurtleNextReachable.
    exists c, dir, pos, 1, 84.
    refine (conj (conj PreH39 PreH40) _).
    refine (conj (conj PreH41 PreH42) _).
    refine (conj (conj PreH43 ltac:(unfold TurtleWidth; exact PreH44)) _).
    refine (conj Hone_bounds _).
    refine (conj ltac:(unfold TurtleTransitionRank; apply Z.lt_succ_diag_r) _).
    refine (conj Hreachable _).
    refine (conj (eq_refl (c + 1)) _).
    refine (conj PreH26 _).
    split.
    + unfold FlippedCommand. right. split; [reflexivity|]. left. tauto.
    + unfold TurtleEncodedStep. left.
      split; [reflexivity|]. split; [exact Hxor|reflexivity].
  - eapply (turtle_transition_new_cell_unique__next_update_core
      commands i changes_pre
      (2 * TurtleCellIndex commands c dir pos + 1)
      c dir pos 1 84 (c + 1) (Z.lxor dir 1) pos).
    + exact (conj PreH39 PreH40).
    + exact (conj PreH41 PreH42).
    + unfold TurtleWidth. exact (conj PreH43 PreH44).
    + exact Hone_bounds.
    + reflexivity.
    + exact Hreachable.
    + reflexivity.
    + exact PreH26.
    + unfold FlippedCommand. right. split; [reflexivity|]. left. tauto.
    + unfold TurtleEncodedStep. left.
      split; [reflexivity|]. split; [exact Hxor|reflexivity].
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_2 : solver_entail_wit_9_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst O W len.
  rewrite app_Znth1 in PreH25 by lia.
  assert (Hcommand : Znth i commands 0 = 84) by exact PreH25.
  assert (Hflip : flip = 0) by exact PreH55.
  assert (Hxor : Z.lxor dir 1 = 1 - dir).
  { assert (dir = 0 \/ dir = 1) as [-> | ->] by lia; reflexivity. }
  assert (Hreachable : PrefixReachable commands i c dir pos).
  { specialize (PreH53 c dir pos ltac:(lia) ltac:(lia)).
    specialize (PreH53 ltac:(unfold TurtleWidth; lia)).
    unfold TurtleCellIndex, TurtleWidth in PreH53.
    cbn beta in PreH53.
    destruct PreH53 as [[Hzero | Hone] Hmeaning].
    - exfalso. apply PreH47. exact Hzero.
    - apply Hmeaning. exact Hone. }
  subst flip.
  subst n.
  replace (c + 0) with c by lia.
  replace
    (2 * ((c * 2 + dir) * (2 * Zlength commands + 1) + pos) + (0 + 1))
    with
    ((2 * ((c * 2 + dir) * (2 * Zlength commands + 1) + pos) + 0) + 1)
    by lia.
  eapply (turtle_next_prefix_write_transition__next_update_core
    commands i changes_pre
    (2 * TurtleCellIndex commands c dir pos + 0)
    next_table_2 c dir pos 0 84 c (Z.lxor dir 1) pos).
  - exact PreH54.
  - exact PreH52.
  - exact (conj PreH39 PreH40).
  - exact (conj PreH41 PreH42).
  - unfold TurtleWidth. exact (conj PreH43 PreH44).
  - split; lia.
  - unfold TurtleTransitionRank. reflexivity.
  - exact Hreachable.
  - lia.
  - lia.
  - unfold FlippedCommand. left.
    split; [reflexivity|symmetry; exact Hcommand].
  - unfold TurtleEncodedStep. left.
    split; [reflexivity|]. split; [exact Hxor|reflexivity].
  - exact (conj PreH39 PreH40).
  - exact (conj PreH5 PreH6).
  - unfold TurtleWidth. exact (conj PreH43 PreH44).
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_2 : solver_entail_wit_9_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_3_split_goal_1 : solver_entail_wit_9_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst O W len.
  rewrite app_Znth1 in PreH28 by lia.
  assert (Hcommand : Znth i commands 0 = 84) by exact PreH28.
  assert (Hdir : dir = 1) by lia.
  assert (Hflip : flip = 1) by lia.
  subst dir flip.
  subst n.
  assert (Hreachable : PrefixReachable commands i c 1 pos).
  { specialize (PreH56 c 1 pos ltac:(lia) ltac:(lia)).
    specialize (PreH56 ltac:(unfold TurtleWidth; lia)).
    unfold TurtleCellIndex, TurtleWidth in PreH56.
    cbn beta in PreH56.
    destruct PreH56 as [[Hzero | Hone] Hmeaning].
    - exfalso. apply PreH50. exact Hzero.
    - apply Hmeaning. exact Hone. }
  replace
    (2 * ((c * 2 + 1) * (2 * Zlength commands + 1) + pos) + (1 + 1))
    with
    ((2 * ((c * 2 + 1) * (2 * Zlength commands + 1) + pos) + 1) + 1)
    by lia.
  change (TurtleNextPrefix commands i changes_pre
    ((2 * TurtleCellIndex commands c 1 pos + 1) + 1)
    (replace_Znth
      (TurtleCellIndex commands (c + 1) 1 (pos - 1))
      1 next_table_2)).
  eapply (turtle_next_prefix_write_transition__next_update_core
    commands i changes_pre
    (2 * TurtleCellIndex commands c 1 pos + 1)
    next_table_2 c 1 pos 1 70 (c + 1) 1 (pos - 1)).
  - exact PreH57.
  - exact PreH55.
  - exact (conj PreH42 PreH43).
  - split; lia.
  - unfold TurtleWidth. exact (conj PreH46 PreH47).
  - split; lia.
  - unfold TurtleTransitionRank. reflexivity.
  - exact Hreachable.
  - reflexivity.
  - exact PreH29.
  - unfold FlippedCommand. right.
    split; [reflexivity|]. right. split; [exact Hcommand|reflexivity].
  - unfold TurtleEncodedStep. right.
    split; [reflexivity|]. split; [reflexivity|].
    right. split; [reflexivity|reflexivity].
  - split; lia.
  - split; lia.
  - unfold TurtleWidth. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_3_split_goal_2 : solver_entail_wit_9_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_4_split_goal_1 : solver_entail_wit_9_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst O W len.
  rewrite app_Znth1 in PreH28 by lia.
  assert (Hcommand : Znth i commands 0 = 84) by exact PreH28.
  assert (Hdir : dir = 0) by lia.
  assert (Hflip : flip = 1) by lia.
  subst dir flip.
  subst n.
  assert (Hreachable : PrefixReachable commands i c 0 pos).
  { specialize (PreH56 c 0 pos ltac:(lia) ltac:(lia)).
    specialize (PreH56 ltac:(unfold TurtleWidth; lia)).
    unfold TurtleCellIndex, TurtleWidth in PreH56.
    cbn beta in PreH56.
    destruct PreH56 as [[Hzero | Hone] Hmeaning].
    - exfalso. apply PreH50. exact Hzero.
    - apply Hmeaning. exact Hone. }
  replace
    (2 * ((c * 2 + 0) * (2 * Zlength commands + 1) + pos) + (1 + 1))
    with
    ((2 * ((c * 2 + 0) * (2 * Zlength commands + 1) + pos) + 1) + 1)
    by lia.
  change (TurtleNextPrefix commands i changes_pre
    ((2 * TurtleCellIndex commands c 0 pos + 1) + 1)
    (replace_Znth
      (TurtleCellIndex commands (c + 1) 0 (pos + 1))
      1 next_table_2)).
  eapply (turtle_next_prefix_write_transition__next_update_core
    commands i changes_pre
    (2 * TurtleCellIndex commands c 0 pos + 1)
    next_table_2 c 0 pos 1 70 (c + 1) 0 (pos + 1)).
  - exact PreH57.
  - exact PreH55.
  - exact (conj PreH42 PreH43).
  - split; lia.
  - unfold TurtleWidth. exact (conj PreH46 PreH47).
  - split; lia.
  - unfold TurtleTransitionRank. reflexivity.
  - exact Hreachable.
  - reflexivity.
  - exact PreH29.
  - unfold FlippedCommand. right.
    split; [reflexivity|]. right. split; [exact Hcommand|reflexivity].
  - unfold TurtleEncodedStep. right.
    split; [reflexivity|]. split; [reflexivity|].
    left. split; [reflexivity|reflexivity].
  - split; lia.
  - split; lia.
  - unfold TurtleWidth. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_4_split_goal_2 : solver_entail_wit_9_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_5_split_goal_1 : solver_entail_wit_9_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst O W len.
  rewrite app_Znth1 in PreH28 by lia.
  specialize (PreH39 i ltac:(lia)).
  assert (Hcommand : Znth i commands 0 = 70) by tauto.
  assert (Hdir : dir = 1) by lia.
  assert (Hflip : flip = 0) by lia.
  subst dir flip.
  subst n.
  assert (Hreachable : PrefixReachable commands i c 1 pos).
  { specialize (PreH56 c 1 pos ltac:(lia) ltac:(lia)).
    specialize (PreH56 ltac:(unfold TurtleWidth; lia)).
    unfold TurtleCellIndex, TurtleWidth in PreH56.
    cbn beta in PreH56.
    destruct PreH56 as [[Hzero | Hone] Hmeaning].
    - exfalso. apply PreH50. exact Hzero.
    - apply Hmeaning. exact Hone. }
  replace (c + 0) with c by lia.
  replace
    (2 * ((c * 2 + 1) * (2 * Zlength commands + 1) + pos) + (0 + 1))
    with
    ((2 * ((c * 2 + 1) * (2 * Zlength commands + 1) + pos) + 0) + 1)
    by lia.
  change (TurtleNextPrefix commands i changes_pre
    ((2 * TurtleCellIndex commands c 1 pos + 0) + 1)
    (replace_Znth
      (TurtleCellIndex commands c 1 (pos - 1))
      1 next_table_2)).
  eapply (turtle_next_prefix_write_transition__next_update_core
    commands i changes_pre
    (2 * TurtleCellIndex commands c 1 pos + 0)
    next_table_2 c 1 pos 0 70 c 1 (pos - 1)).
  - exact PreH57.
  - exact PreH55.
  - exact (conj PreH42 PreH43).
  - split; lia.
  - unfold TurtleWidth. exact (conj PreH46 PreH47).
  - split; lia.
  - unfold TurtleTransitionRank. reflexivity.
  - exact Hreachable.
  - lia.
  - lia.
  - unfold FlippedCommand. left.
    split; [reflexivity|symmetry; exact Hcommand].
  - unfold TurtleEncodedStep. right.
    split; [reflexivity|]. split; [reflexivity|].
    right. split; [reflexivity|reflexivity].
  - split; lia.
  - split; lia.
  - unfold TurtleWidth. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_5_split_goal_2 : solver_entail_wit_9_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_5 : solver_entail_wit_9_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_6_split_goal_1 : solver_entail_wit_9_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst O W len.
  rewrite app_Znth1 in PreH28 by lia.
  specialize (PreH39 i ltac:(lia)).
  assert (Hcommand : Znth i commands 0 = 70) by tauto.
  assert (Hdir : dir = 0) by lia.
  assert (Hflip : flip = 0) by lia.
  subst dir flip.
  subst n.
  assert (Hreachable : PrefixReachable commands i c 0 pos).
  { specialize (PreH56 c 0 pos ltac:(lia) ltac:(lia)).
    specialize (PreH56 ltac:(unfold TurtleWidth; lia)).
    unfold TurtleCellIndex, TurtleWidth in PreH56.
    cbn beta in PreH56.
    destruct PreH56 as [[Hzero | Hone] Hmeaning].
    - exfalso. apply PreH50. exact Hzero.
    - apply Hmeaning. exact Hone. }
  replace (c + 0) with c by lia.
  replace
    (2 * ((c * 2 + 0) * (2 * Zlength commands + 1) + pos) + (0 + 1))
    with
    ((2 * ((c * 2 + 0) * (2 * Zlength commands + 1) + pos) + 0) + 1)
    by lia.
  change (TurtleNextPrefix commands i changes_pre
    ((2 * TurtleCellIndex commands c 0 pos + 0) + 1)
    (replace_Znth
      (TurtleCellIndex commands c 0 (pos + 1))
      1 next_table_2)).
  eapply (turtle_next_prefix_write_transition__next_update_core
    commands i changes_pre
    (2 * TurtleCellIndex commands c 0 pos + 0)
    next_table_2 c 0 pos 0 70 c 0 (pos + 1)).
  - exact PreH57.
  - exact PreH55.
  - exact (conj PreH42 PreH43).
  - split; lia.
  - unfold TurtleWidth. exact (conj PreH46 PreH47).
  - split; lia.
  - unfold TurtleTransitionRank. reflexivity.
  - exact Hreachable.
  - lia.
  - lia.
  - unfold FlippedCommand. left.
    split; [reflexivity|symmetry; exact Hcommand].
  - unfold TurtleEncodedStep. right.
    split; [reflexivity|]. split; [reflexivity|].
    left. split; [reflexivity|reflexivity].
  - split; lia.
  - split; lia.
  - unfold TurtleWidth. split; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_6_split_goal_2 : solver_entail_wit_9_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_6 : solver_entail_wit_9_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_7_split_goal_1 : solver_entail_wit_9_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst W O flip.
  subst n.
  assert (dir = 1) by lia.
  assert (pos = 0) by lia.
  subst dir pos.
  eapply turtle_next_prefix_skip_rank__next_noop.
  - replace (2 * ((c * 2 + 1) * (2 * len + 1) + 0))
      with (2 * ((c * 2 + 1) * (2 * len + 1) + 0) + 0) by lia.
    auto.
  - intros flips0 direction0 slot0 flip0 effective
      next_flips next_direction next_slot
      Hflips0 Hdirection0 Hslot0 Hflip0 Hrank Hreachable
      Hnext_flips Hnext_limit Hcommand Hstep.
    rewrite PreH29 in Hrank.
    assert (Hrank_current :
      TurtleTransitionRank commands flips0 direction0 slot0 flip0 =
      TurtleTransitionRank commands c 1 0 0).
    { unfold TurtleTransitionRank, TurtleCellIndex, TurtleWidth in Hrank |- *.
      nia. }
    destruct (turtle_transition_rank_injective__next_noop commands
      flips0 direction0 slot0 flip0 c 1 0 0
      Hdirection0 Hslot0 Hflip0 ltac:(lia)
      ltac:(unfold TurtleWidth; rewrite <- PreH29; lia)
      ltac:(lia) Hrank_current)
      as [Hflips [Hdirection [Hslot Hflip]]].
    subst flips0 direction0 slot0 flip0.
    rewrite (Znth_app_left__next_noop commands (0 :: nil) i 0) in PreH25
      by (rewrite <- PreH29; lia).
    unfold FlippedCommand in Hcommand.
    unfold TurtleEncodedStep in Hstep.
    destruct Hcommand as [[? ?] | [? [[? ?] | [? ?]]]];
      destruct Hstep as [[? [? ?]] | [? [? [[? ?] | [? ?]]]]];
      subst; nia.
Qed.

Lemma proof_of_solver_entail_wit_9_7 : solver_entail_wit_9_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_8_split_goal_1 : solver_entail_wit_9_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst W O.
  assert (flip = 1) by lia.
  assert (dir = 1) by lia.
  assert (pos = 0) by lia.
  subst flip dir pos.
  subst n.
  replace (2 * ((c * 2 + 1) * (2 * len + 1) + 0) + (1 + 1))
    with ((2 * ((c * 2 + 1) * (2 * len + 1) + 0) + 1) + 1) by lia.
  eapply turtle_next_prefix_skip_rank__next_noop.
  - auto.
  - intros flips0 direction0 slot0 flip0 effective
      next_flips next_direction next_slot
      Hflips0 Hdirection0 Hslot0 Hflip0 Hrank Hreachable
      Hnext_flips Hnext_limit Hcommand Hstep.
    rewrite PreH29 in Hrank.
    assert (Hrank_current :
      TurtleTransitionRank commands flips0 direction0 slot0 flip0 =
      TurtleTransitionRank commands c 1 0 1).
    { unfold TurtleTransitionRank, TurtleCellIndex, TurtleWidth in Hrank |- *.
      nia. }
    destruct (turtle_transition_rank_injective__next_noop commands
      flips0 direction0 slot0 flip0 c 1 0 1
      Hdirection0 Hslot0 Hflip0 ltac:(lia)
      ltac:(unfold TurtleWidth; rewrite <- PreH29; lia)
      ltac:(lia) Hrank_current)
      as [Hflips [Hdirection [Hslot Hflip]]].
    subst flips0 direction0 slot0 flip0.
    rewrite (Znth_app_left__next_noop commands (0 :: nil) i 0) in PreH25
      by (rewrite <- PreH29; lia).
    unfold FlippedCommand in Hcommand.
    unfold TurtleEncodedStep in Hstep.
    destruct Hcommand as [[? ?] | [? [[? ?] | [? ?]]]];
      destruct Hstep as [[? [? ?]] | [? [? [[? ?] | [? ?]]]]];
      subst; nia.
Qed.

Lemma proof_of_solver_entail_wit_9_8 : solver_entail_wit_9_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_8_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_9_split_goal_1 : solver_entail_wit_9_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst W O.
  assert (flip = 1) by lia.
  assert (dir = 0) by lia.
  assert (pos = 2 * len) by lia.
  subst flip dir pos.
  subst n.
  replace (2 * ((c * 2 + 0) * (2 * len + 1) + 2 * len) + (1 + 1))
    with ((2 * ((c * 2 + 0) * (2 * len + 1) + 2 * len) + 1) + 1) by lia.
  eapply turtle_next_prefix_skip_rank__next_noop.
  - auto.
  - intros flips0 direction0 slot0 flip0 effective
      next_flips next_direction next_slot
      Hflips0 Hdirection0 Hslot0 Hflip0 Hrank Hreachable
      Hnext_flips Hnext_limit Hcommand Hstep.
    rewrite PreH30 in Hrank.
    assert (Hrank_current :
      TurtleTransitionRank commands flips0 direction0 slot0 flip0 =
      TurtleTransitionRank commands c 0 (2 * Zlength commands) 1).
    { unfold TurtleTransitionRank, TurtleCellIndex, TurtleWidth in Hrank |- *.
      nia. }
    destruct (turtle_transition_rank_injective__next_noop commands
      flips0 direction0 slot0 flip0 c 0 (2 * Zlength commands) 1
      Hdirection0 Hslot0 Hflip0 ltac:(lia)
      ltac:(unfold TurtleWidth; pose proof (Zlength_nonneg commands); lia)
      ltac:(lia) Hrank_current)
      as [Hflips [Hdirection [Hslot Hflip]]].
    subst flips0 direction0 slot0 flip0.
    rewrite (Znth_app_left__next_noop commands (0 :: nil) i 0) in PreH26
      by (rewrite <- PreH30; lia).
    unfold FlippedCommand in Hcommand.
    unfold TurtleEncodedStep in Hstep.
    destruct Hcommand as [[? ?] | [? [[? ?] | [? ?]]]];
      destruct Hstep as [[? [? ?]] | [? [? [[? ?] | [? ?]]]]];
      subst; unfold TurtleWidth; nia.
Qed.

Lemma proof_of_solver_entail_wit_9_9 : solver_entail_wit_9_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_10_split_goal_1 : solver_entail_wit_9_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst W O flip.
  assert (dir = 0) by lia.
  assert (pos = 2 * len) by lia.
  subst dir pos.
  subst n.
  replace (2 * ((c * 2 + 0) * (2 * len + 1) + 2 * len) + (0 + 1))
    with ((2 * ((c * 2 + 0) * (2 * len + 1) + 2 * len) + 0) + 1) by lia.
  eapply turtle_next_prefix_skip_rank__next_noop.
  - auto.
  - intros flips0 direction0 slot0 flip0 effective
      next_flips next_direction next_slot
      Hflips0 Hdirection0 Hslot0 Hflip0 Hrank Hreachable
      Hnext_flips Hnext_limit Hcommand Hstep.
    rewrite PreH30 in Hrank.
    assert (Hrank_current :
      TurtleTransitionRank commands flips0 direction0 slot0 flip0 =
      TurtleTransitionRank commands c 0 (2 * Zlength commands) 0).
    { unfold TurtleTransitionRank, TurtleCellIndex, TurtleWidth in Hrank |- *.
      nia. }
    destruct (turtle_transition_rank_injective__next_noop commands
      flips0 direction0 slot0 flip0 c 0 (2 * Zlength commands) 0
      Hdirection0 Hslot0 Hflip0 ltac:(lia)
      ltac:(unfold TurtleWidth; pose proof (Zlength_nonneg commands); lia)
      ltac:(lia) Hrank_current)
      as [Hflips [Hdirection [Hslot Hflip]]].
    subst flips0 direction0 slot0 flip0.
    rewrite (Znth_app_left__next_noop commands (0 :: nil) i 0) in PreH26
      by (rewrite <- PreH30; lia).
    unfold FlippedCommand in Hcommand.
    unfold TurtleEncodedStep in Hstep.
    destruct Hcommand as [[? ?] | [? [[? ?] | [? ?]]]];
      destruct Hstep as [[? [? ?]] | [? [? [[? ?] | [? ?]]]]];
      subst; unfold TurtleWidth; nia.
Qed.

Lemma proof_of_solver_entail_wit_9_10 : solver_entail_wit_9_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_10_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_11_split_goal_1 : solver_entail_wit_9_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst W O.
  subst n.
  replace (2 * ((c * 2 + dir) * (2 * len + 1) + pos) + (flip + 1))
    with ((2 * ((c * 2 + dir) * (2 * len + 1) + pos) + flip) + 1) by lia.
  eapply turtle_next_prefix_skip_rank__next_noop.
  - auto.
  - intros flips0 direction0 slot0 flip0 effective
      next_flips next_direction next_slot
      Hflips0 Hdirection0 Hslot0 Hflip0 Hrank Hreachable
      Hnext_flips Hnext_limit Hcommand Hstep.
    rewrite PreH4 in Hrank.
    assert (Hrank_current :
      TurtleTransitionRank commands flips0 direction0 slot0 flip0 =
      TurtleTransitionRank commands c dir pos flip).
    { unfold TurtleTransitionRank, TurtleCellIndex, TurtleWidth in Hrank |- *.
      nia. }
    destruct (turtle_transition_rank_injective__next_noop commands
      flips0 direction0 slot0 flip0 c dir pos flip
      Hdirection0 Hslot0 Hflip0 ltac:(lia)
      ltac:(unfold TurtleWidth; rewrite <- PreH4; lia)
      ltac:(lia) Hrank_current)
      as [Hflips [Hdirection [Hslot Hflip]]].
    subst flips0 direction0 slot0 flip0.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_9_11 : solver_entail_wit_9_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
  subst n W O.
  assert (flip = 2) by lia.
  subst flip.
  replace (2 * ((c * 2 + dir) * (2 * len + 1) + (pos + 1)))
    with (2 * ((c * 2 + dir) * (2 * len + 1) + pos) + 2) by nia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst n.
  assert (HW : W = TurtleWidth commands).
  { unfold TurtleWidth. lia. }
  assert (HO : 2 * O + 1 = TurtleWidth commands).
  { unfold TurtleWidth. lia. }
  assert (Hslot : 0 <= pos < TurtleWidth commands) by lia.
  assert (Hzero :
      Znth (TurtleCellIndex commands c dir pos) current_table_2 0 = 0).
  {
    unfold TurtleCellIndex.
    rewrite <- HW.
    assumption.
  }
  assert (Hprefix : TurtleNextPrefix commands i changes_pre
      (2 * TurtleCellIndex commands c dir pos) next_table_2).
  {
    unfold TurtleCellIndex.
    rewrite <- HW.
    assumption.
  }
  assert (Hfirst : TurtleNextPrefix commands i changes_pre
      (2 * TurtleCellIndex commands c dir pos + 1) next_table_2).
  {
    apply turtle_next_prefix_skip_rank__next_noop.
    - exact Hprefix.
    - intros source_flips source_direction source_slot flip effective
        next_flips next_direction next_slot
        Hsource_flips Hsource_direction Hsource_slot Hflip Hrank Hreachable
        Hnext_flips Hchange Heffective Hstep.
      intro Hnext_bounds.
      match goal with
      | Hlayer : TurtleLayerMeaning commands i changes_pre current_table_2 |- _ =>
          specialize (Hlayer source_flips source_direction source_slot
            Hsource_flips Hsource_direction Hsource_slot);
          simpl in Hlayer;
          destruct Hlayer as [_ Hmeaning]
      end.
      assert (Hone :
        Znth (TurtleCellIndex commands source_flips source_direction source_slot)
          current_table_2 0 = 1).
      { apply Hmeaning. exact Hreachable. }
      unfold TurtleTransitionRank in Hrank.
      set (source_index :=
        TurtleCellIndex commands source_flips source_direction source_slot) in *.
      set (target_index := TurtleCellIndex commands c dir pos) in *.
      assert (Hflip_zero : flip = 0) by lia.
      assert (Hindex : source_index = target_index) by lia.
      rewrite Hindex in Hone.
      lia.
  }
  rewrite HO.
  replace
    (2 * ((c * 2 + dir) * TurtleWidth commands + (pos + 1)))
    with ((2 * TurtleCellIndex commands c dir pos + 1) + 1).
  2: unfold TurtleCellIndex; ring.
  apply turtle_next_prefix_skip_rank__next_noop.
  - exact Hfirst.
  - intros source_flips source_direction source_slot flip effective
      next_flips next_direction next_slot
      Hsource_flips Hsource_direction Hsource_slot Hflip Hrank Hreachable
      Hnext_flips Hchange Heffective Hstep.
    intro Hnext_bounds.
    match goal with
    | Hlayer : TurtleLayerMeaning commands i changes_pre current_table_2 |- _ =>
        specialize (Hlayer source_flips source_direction source_slot
          Hsource_flips Hsource_direction Hsource_slot);
        simpl in Hlayer;
        destruct Hlayer as [_ Hmeaning]
    end.
    assert (Hone :
      Znth (TurtleCellIndex commands source_flips source_direction source_slot)
        current_table_2 0 = 1).
    { apply Hmeaning. exact Hreachable. }
    unfold TurtleTransitionRank in Hrank.
    set (source_index :=
      TurtleCellIndex commands source_flips source_direction source_slot) in *.
    set (target_index := TurtleCellIndex commands c dir pos) in *.
    assert (Hflip_one : flip = 1) by lia.
    assert (Hindex : source_index = target_index) by lia.
    rewrite Hindex in Hone.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst n W O.
  assert (Hpos : pos = 2 * len + 1) by lia.
  subst pos.
  replace (2 * ((c * 2 + (dir + 1)) * (2 * len + 1)))
    with (2 * ((c * 2 + dir) * (2 * len + 1) + (2 * len + 1))) by ring.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst n W O.
  assert (Hdir : dir = 2) by lia.
  subst dir.
  replace (4 * (c + 1) * (2 * len + 1))
    with (2 * ((c * 2 + 2) * (2 * len + 1))) by ring.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst n W O.
  assert (Hc : c = changes_pre + 1) by lia.
  subst c.
  replace ((changes_pre + 1) * 2 * (2 * len + 1) * 2)
    with (4 * (changes_pre + 1) * (2 * len + 1)) by ring.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  eapply turtle_next_complete_layer__layer_swap.
  - lia.
  - lia.
  - intros k Hk. apply PreH9. lia.
  - replace (TurtleWidth commands) with W.
    + auto.
    + unfold TurtleWidth. lia.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  replace O with i by lia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_1 : solver_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply turtle_answer_prefix_zero__answer_init.
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_2 : solver_entail_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_16_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_1 : solver_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  replace (((c * 2) + 0) * ((2 * O) + 1)) with ((c * 2) * W) by lia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_17_split_goal_2 : solver_entail_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_1 : solver_entail_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  replace ((((c * 2) + d) * ((2 * O) + 1)) + 0)
    with (((c * 2) + d) * W) by lia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_2 : solver_entail_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_18_split_goal_3 : solver_entail_wit_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_18 : solver_entail_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_18_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_19_split_goal_1 : solver_entail_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  rewrite PreH21.
  assert (Hwidth : 0 < W) by (rewrite PreH20; lia).
  assert (Hnext :
    (c * 2 + d) * W + p <
      (c * 2 + d + 1) * W).
  { replace ((c * 2 + d + 1) * W)
      with ((c * 2 + d) * W + W) by ring.
    lia. }
  assert (Hcoefficient : c * 2 + d + 1 <= (changes_pre + 1) * 2)
    by lia.
  assert (Hproduct :
    (c * 2 + d + 1) * W <=
      ((changes_pre + 1) * 2) * W).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  rewrite <- PreH20.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_19 : solver_entail_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_19_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_20_1_split_goal_1 : solver_entail_wit_20_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  subst n.
  rewrite PreH16.
  rewrite <- PreH15.
  replace ((((c * 2 + d) * W) + (p + 1)))
    with ((((c * 2 + d) * W) + p) + 1) by ring.
  eapply turtle_answer_prefix_consume_cell__answer_position.
  - exact PreH38.
  - lia.
  - intros flips direction slot Heligible Hindex.
    pose proof Heligible as Heligible_bounds.
    unfold TurtleTerminalEligible in Heligible_bounds.
    destruct Heligible_bounds as
      [Hflips [Hdirection [Hslot [_ Hreachable]]]].
    assert (Hslot_eq : slot = p).
    { eapply turtle_cell_index_same_slot__answer_position
        with (commands := commands)
             (flips1 := flips) (direction1 := direction)
             (flips2 := c) (direction2 := d).
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - exact Hslot.
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - unfold TurtleCellIndex, TurtleWidth in Hindex |- *.
        rewrite <- PreH14, <- PreH15 in Hindex |- *. exact Hindex. }
    subst slot.
    rewrite Z.abs_eq by (rewrite <- PreH14; lia).
    rewrite <- PreH14.
    reflexivity.
  - right.
    exists c, d, p.
    assert (Heligible : TurtleTerminalEligible commands changes_pre c d p).
    { eapply turtle_layer_nonzero_terminal__answer_position.
      - rewrite <- PreH14. exact PreH37.
      - lia.
      - lia.
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - apply land_one_zero_even__answer_position. exact PreH28.
      - unfold TurtleCellIndex, TurtleWidth.
        rewrite <- PreH14, <- PreH15. exact PreH39. }
    split; [exact Heligible|].
    split.
    + unfold TurtleCellIndex, TurtleWidth.
      rewrite <- PreH14, <- PreH15. reflexivity.
    + rewrite Z.abs_eq by (rewrite <- PreH14; lia).
      rewrite <- PreH14. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_20_1 : solver_entail_wit_20_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_20_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_20_2_split_goal_1 : solver_entail_wit_20_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  subst n.
  rewrite PreH16.
  rewrite <- PreH15.
  replace ((((c * 2 + d) * W) + (p + 1)))
    with ((((c * 2 + d) * W) + p) + 1) by ring.
  eapply turtle_answer_prefix_consume_cell__answer_position.
  - exact PreH38.
  - lia.
  - intros flips direction slot Heligible Hindex.
    pose proof Heligible as Heligible_bounds.
    unfold TurtleTerminalEligible in Heligible_bounds.
    destruct Heligible_bounds as
      [Hflips [Hdirection [Hslot [_ Hreachable]]]].
    assert (Hslot_eq : slot = p).
    { eapply turtle_cell_index_same_slot__answer_position
        with (commands := commands)
             (flips1 := flips) (direction1 := direction)
             (flips2 := c) (direction2 := d).
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - exact Hslot.
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - unfold TurtleCellIndex, TurtleWidth in Hindex |- *.
        rewrite <- PreH14, <- PreH15 in Hindex |- *. exact Hindex. }
    subst slot.
    rewrite Z.abs_neq by (rewrite <- PreH14; lia).
    rewrite <- PreH14.
    reflexivity.
  - right.
    exists c, d, p.
    assert (Heligible : TurtleTerminalEligible commands changes_pre c d p).
    { eapply turtle_layer_nonzero_terminal__answer_position.
      - rewrite <- PreH14. exact PreH37.
      - lia.
      - lia.
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - apply land_one_zero_even__answer_position. exact PreH28.
      - unfold TurtleCellIndex, TurtleWidth.
        rewrite <- PreH14, <- PreH15. exact PreH39. }
    split; [exact Heligible|].
    split.
    + unfold TurtleCellIndex, TurtleWidth.
      rewrite <- PreH14, <- PreH15. reflexivity.
    + rewrite Z.abs_neq by (rewrite <- PreH14; lia).
      rewrite <- PreH14. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_20_2 : solver_entail_wit_20_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_20_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_20_3_split_goal_1 : solver_entail_wit_20_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  subst n.
  rewrite PreH16.
  rewrite <- PreH15.
  replace ((((c * 2 + d) * W) + (p + 1)))
    with ((((c * 2 + d) * W) + p) + 1) by ring.
  eapply turtle_answer_prefix_consume_cell__answer_position.
  - exact PreH38.
  - reflexivity.
  - intros flips direction slot Heligible Hindex.
    pose proof Heligible as Heligible_bounds.
    unfold TurtleTerminalEligible in Heligible_bounds.
    destruct Heligible_bounds as
      [Hflips [Hdirection [Hslot [_ Hreachable]]]].
    assert (Hslot_eq : slot = p).
    { eapply turtle_cell_index_same_slot__answer_position
        with (commands := commands)
             (flips1 := flips) (direction1 := direction)
             (flips2 := c) (direction2 := d).
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - exact Hslot.
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - unfold TurtleCellIndex, TurtleWidth in Hindex |- *.
        rewrite <- PreH14, <- PreH15 in Hindex |- *. exact Hindex. }
    subst slot.
    rewrite Z.abs_eq by (rewrite <- PreH14; lia).
    rewrite <- PreH14.
    lia.
  - left. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_20_3 : solver_entail_wit_20_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_20_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_20_4_split_goal_1 : solver_entail_wit_20_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  subst n.
  rewrite PreH16.
  rewrite <- PreH15.
  replace ((((c * 2 + d) * W) + (p + 1)))
    with ((((c * 2 + d) * W) + p) + 1) by ring.
  eapply turtle_answer_prefix_consume_cell__answer_position.
  - exact PreH38.
  - reflexivity.
  - intros flips direction slot Heligible Hindex.
    pose proof Heligible as Heligible_bounds.
    unfold TurtleTerminalEligible in Heligible_bounds.
    destruct Heligible_bounds as
      [Hflips [Hdirection [Hslot [_ Hreachable]]]].
    assert (Hslot_eq : slot = p).
    { eapply turtle_cell_index_same_slot__answer_position
        with (commands := commands)
             (flips1 := flips) (direction1 := direction)
             (flips2 := c) (direction2 := d).
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - exact Hslot.
      - unfold TurtleWidth. rewrite <- PreH14. lia.
      - unfold TurtleCellIndex, TurtleWidth in Hindex |- *.
        rewrite <- PreH14, <- PreH15 in Hindex |- *. exact Hindex. }
    subst slot.
    rewrite Z.abs_neq by (rewrite <- PreH14; lia).
    rewrite <- PreH14.
    lia.
  - left. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_20_4 : solver_entail_wit_20_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_20_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_20_5_split_goal_1 : solver_entail_wit_20_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  subst n.
  rewrite PreH13.
  rewrite <- PreH12.
  replace ((((c * 2 + d) * W) + (p + 1)))
    with ((((c * 2 + d) * W) + p) + 1) by ring.
  eapply turtle_answer_prefix_consume_cell__answer_position.
  - exact PreH35.
  - reflexivity.
  - intros flips direction slot Heligible Hindex.
    pose proof (turtle_terminal_cell_one__answer_position
      commands changes_pre final_table_2 flips direction slot) as Hone.
    rewrite <- PreH11 in Hone.
    specialize (Hone PreH34 Heligible).
    rewrite Hindex in Hone.
    rewrite PreH36 in Hone.
    discriminate.
  - left. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_20_5 : solver_entail_wit_20_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_20_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_21_split_goal_1 : solver_entail_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  replace (((c * 2 + (d + 1)) * (2 * O + 1)))
    with (((c * 2 + d) * W) + p) by nia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_21_split_goal_2 : solver_entail_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_21 : solver_entail_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_21_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_21_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_22_1_split_goal_1 : solver_entail_wit_22_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  replace (((c + 1) * 2) * (2 * O + 1))
    with ((c * 2 + d) * W) by nia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_22_1_split_goal_2 : solver_entail_wit_22_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_22_1 : solver_entail_wit_22_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_22_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_22_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_22_2_split_goal_1 : solver_entail_wit_22_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  replace (2 * O + 1) with (TurtleWidth commands).
  2: unfold TurtleWidth; nia.
  apply (turtle_answer_prefix_skip_ineligible__answer_loop_exits
    commands changes_pre c ans).
  - exact PreH12.
  - exact PreH2.
  - unfold TurtleWidth. nia.
  - exact PreH1.
  - replace (TurtleWidth commands) with W by (unfold TurtleWidth; nia).
    exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_22_2 : solver_entail_wit_22_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_22_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_23_split_goal_1 : solver_entail_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  assert (Hc : c = changes_pre + 1) by lia.
  apply (turtle_answer_complete_spec__final_spec commands changes_pre final_table_2 ans).
  - unfold Pre.
    split; [lia|]. split; [lia|].
    apply command_alphabet_from_Znth__final_spec.
    intros k Hk. apply PreH10. lia.
  - rewrite <- PreH3. exact PreH19.
  - replace (((changes_pre + 1) * 2) * TurtleWidth commands)
      with (c * 2 * W) by (unfold TurtleWidth; lia).
    exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_23_split_goal_2 : solver_entail_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_23 : solver_entail_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst len.
  cancel (CharArray.full s_pre (Zlength commands + 1)
    (commands ++ 0 :: nil)).
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
Qed.
