From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib.
Local Open Scope sac.



Lemma proof_of_solver_partial_solve_wit_53_pure_split_goal_1 : solver_partial_solve_wit_53_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_53_pure_split_goal_2 : solver_partial_solve_wit_53_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_53_pure : solver_partial_solve_wit_53_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_53_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_53_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_54_pure_split_goal_1 : solver_partial_solve_wit_54_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_54_pure_split_goal_2 : solver_partial_solve_wit_54_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_54_pure : solver_partial_solve_wit_54_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_54_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_54_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_55_pure_split_goal_1 : solver_partial_solve_wit_55_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_55_pure_split_goal_2 : solver_partial_solve_wit_55_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_55_pure : solver_partial_solve_wit_55_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_55_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_55_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_56_pure_split_goal_1 : solver_partial_solve_wit_56_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH68 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_56_pure_split_goal_2 : solver_partial_solve_wit_56_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_56_pure_split_goal_3 : solver_partial_solve_wit_56_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_56_pure : solver_partial_solve_wit_56_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_56_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_56_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_56_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_57_pure_split_goal_1 : solver_partial_solve_wit_57_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_57_pure_split_goal_2 : solver_partial_solve_wit_57_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_57_pure : solver_partial_solve_wit_57_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_57_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_57_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_58_pure_split_goal_1 : solver_partial_solve_wit_58_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH68 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_58_pure_split_goal_2 : solver_partial_solve_wit_58_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_58_pure_split_goal_3 : solver_partial_solve_wit_58_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_58_pure : solver_partial_solve_wit_58_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_58_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_58_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_58_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_59_pure_split_goal_1 : solver_partial_solve_wit_59_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_59_pure_split_goal_2 : solver_partial_solve_wit_59_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_59_pure : solver_partial_solve_wit_59_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_59_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_59_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_60_pure_split_goal_1 : solver_partial_solve_wit_60_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH68 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_60_pure_split_goal_2 : solver_partial_solve_wit_60_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_60_pure_split_goal_3 : solver_partial_solve_wit_60_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_60_pure : solver_partial_solve_wit_60_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_60_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_60_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_60_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_61_pure_split_goal_1 : solver_partial_solve_wit_61_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_61_pure_split_goal_2 : solver_partial_solve_wit_61_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_61_pure : solver_partial_solve_wit_61_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_61_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_61_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_62_pure_split_goal_1 : solver_partial_solve_wit_62_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH68 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_62_pure_split_goal_2 : solver_partial_solve_wit_62_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_62_pure_split_goal_3 : solver_partial_solve_wit_62_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_62_pure : solver_partial_solve_wit_62_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_62_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_62_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_62_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_63_pure_split_goal_1 : solver_partial_solve_wit_63_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_63_pure_split_goal_2 : solver_partial_solve_wit_63_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_63_pure : solver_partial_solve_wit_63_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_63_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_63_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_64_pure_split_goal_1 : solver_partial_solve_wit_64_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH60 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_64_pure_split_goal_2 : solver_partial_solve_wit_64_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH53 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_64_pure_split_goal_3 : solver_partial_solve_wit_64_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH53 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_64_pure : solver_partial_solve_wit_64_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_64_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_64_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_64_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_65_pure_split_goal_1 : solver_partial_solve_wit_65_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_65_pure_split_goal_2 : solver_partial_solve_wit_65_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_65_pure : solver_partial_solve_wit_65_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_65_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_65_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_66_pure_split_goal_1 : solver_partial_solve_wit_66_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_66_pure_split_goal_2 : solver_partial_solve_wit_66_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct Hk as [Hk1 Hk2].
  match goal with
  | H : forall _ : Z, ((0 <= _) /\ (_ < ?b)) -> _ |- _ =>
      assert (Hb : (0 <= k) /\ (k < b)) by lia;
      specialize (H k Hb); tauto
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_66_pure : solver_partial_solve_wit_66_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_66_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_66_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_67_pure_split_goal_1 : solver_partial_solve_wit_67_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_67_pure_split_goal_2 : solver_partial_solve_wit_67_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_67_pure : solver_partial_solve_wit_67_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_67_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_67_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_68_pure_split_goal_1 : solver_partial_solve_wit_68_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_68_pure_split_goal_2 : solver_partial_solve_wit_68_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_68_pure : solver_partial_solve_wit_68_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_68_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_68_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_69_pure_split_goal_1 : solver_partial_solve_wit_69_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_69_pure_split_goal_2 : solver_partial_solve_wit_69_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_69_pure : solver_partial_solve_wit_69_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_69_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_69_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_70_pure_split_goal_1 : solver_partial_solve_wit_70_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_70_pure_split_goal_2 : solver_partial_solve_wit_70_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_70_pure : solver_partial_solve_wit_70_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_70_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_70_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_71_pure_split_goal_1 : solver_partial_solve_wit_71_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_71_pure_split_goal_2 : solver_partial_solve_wit_71_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    intros k Hk;
    pose proof (PreH63 k ltac:(lia)) as Hpack;
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_71_pure : solver_partial_solve_wit_71_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_71_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_71_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_72_pure_split_goal_1 : solver_partial_solve_wit_72_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH63 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_72_pure_split_goal_2 : solver_partial_solve_wit_72_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH63 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_72_pure : solver_partial_solve_wit_72_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_72_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_72_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_73_pure_split_goal_1 : solver_partial_solve_wit_73_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_73_pure_split_goal_2 : solver_partial_solve_wit_73_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_73_pure : solver_partial_solve_wit_73_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_73_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_73_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_74_pure_split_goal_1 : solver_partial_solve_wit_74_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_74_pure_split_goal_2 : solver_partial_solve_wit_74_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_74_pure : solver_partial_solve_wit_74_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_74_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_74_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_75_pure_split_goal_1 : solver_partial_solve_wit_75_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_75_pure_split_goal_2 : solver_partial_solve_wit_75_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_75_pure : solver_partial_solve_wit_75_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_75_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_75_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_76_pure_split_goal_1 : solver_partial_solve_wit_76_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_76_pure_split_goal_2 : solver_partial_solve_wit_76_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_76_pure_split_goal_3 : solver_partial_solve_wit_76_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_76_pure : solver_partial_solve_wit_76_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_76_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_76_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_76_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_77_pure_split_goal_1 : solver_partial_solve_wit_77_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_77_pure_split_goal_2 : solver_partial_solve_wit_77_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_77_pure_split_goal_3 : solver_partial_solve_wit_77_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_77_pure : solver_partial_solve_wit_77_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_77_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_77_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_77_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_78_pure_split_goal_1 : solver_partial_solve_wit_78_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_78_pure_split_goal_2 : solver_partial_solve_wit_78_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_78_pure_split_goal_3 : solver_partial_solve_wit_78_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_78_pure : solver_partial_solve_wit_78_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_78_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_78_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_78_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_79_pure_split_goal_1 : solver_partial_solve_wit_79_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_79_pure_split_goal_2 : solver_partial_solve_wit_79_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_79_pure_split_goal_3 : solver_partial_solve_wit_79_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_79_pure : solver_partial_solve_wit_79_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_79_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_79_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_79_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_80_pure_split_goal_1 : solver_partial_solve_wit_80_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_80_pure_split_goal_2 : solver_partial_solve_wit_80_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_80_pure_split_goal_3 : solver_partial_solve_wit_80_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_80_pure : solver_partial_solve_wit_80_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_80_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_80_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_80_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_81_pure_split_goal_1 : solver_partial_solve_wit_81_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_81_pure_split_goal_2 : solver_partial_solve_wit_81_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_81_pure_split_goal_3 : solver_partial_solve_wit_81_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_81_pure : solver_partial_solve_wit_81_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_81_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_81_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_81_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_82_pure_split_goal_1 : solver_partial_solve_wit_82_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH63 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_82_pure_split_goal_2 : solver_partial_solve_wit_82_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH63 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_82_pure : solver_partial_solve_wit_82_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_82_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_82_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_83_pure_split_goal_1 : solver_partial_solve_wit_83_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_83_pure_split_goal_2 : solver_partial_solve_wit_83_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH61 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_83_pure : solver_partial_solve_wit_83_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_83_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_83_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_84_pure_split_goal_1 : solver_partial_solve_wit_84_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_84_pure_split_goal_2 : solver_partial_solve_wit_84_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_84_pure_split_goal_3 : solver_partial_solve_wit_84_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_84_pure : solver_partial_solve_wit_84_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_84_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_84_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_84_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_85_pure_split_goal_1 : solver_partial_solve_wit_85_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_85_pure_split_goal_2 : solver_partial_solve_wit_85_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_85_pure_split_goal_3 : solver_partial_solve_wit_85_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_85_pure : solver_partial_solve_wit_85_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_85_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_85_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_85_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_86_pure_split_goal_1 : solver_partial_solve_wit_86_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_86_pure_split_goal_2 : solver_partial_solve_wit_86_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_86_pure_split_goal_3 : solver_partial_solve_wit_86_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_86_pure : solver_partial_solve_wit_86_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_86_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_86_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_86_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_87_pure_split_goal_1 : solver_partial_solve_wit_87_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_87_pure_split_goal_2 : solver_partial_solve_wit_87_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_87_pure_split_goal_3 : solver_partial_solve_wit_87_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_87_pure : solver_partial_solve_wit_87_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_87_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_87_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_87_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_88_pure_split_goal_1 : solver_partial_solve_wit_88_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_88_pure_split_goal_2 : solver_partial_solve_wit_88_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_88_pure_split_goal_3 : solver_partial_solve_wit_88_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_88_pure : solver_partial_solve_wit_88_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_88_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_88_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_88_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_89_pure_split_goal_1 : solver_partial_solve_wit_89_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  match goal with
  | Heq : retval_2 = RangeMax ?mm 1 (retval + 1) |- _ =>
      assert (Hb : RangeMax mm 1 (retval + 1) <= n_pre) by
        (apply rangemax_le_bound__pure_d1_bound_bit1;
         [ unfold MaxBitNeg; lia
         | intros r Hrr;
           match goal with
           | Hm : forall q : Z, (0 <= q /\ q <= nvals) -> _ |- _ =>
               specialize (Hm r ltac:(lia));
               exact (proj2 Hm) || exact (proj2 (proj1 (proj1 Hm)))
           end ]);
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_89_pure_split_goal_2 : solver_partial_solve_wit_89_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_89_pure_split_goal_3 : solver_partial_solve_wit_89_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | Hp : forall q : Z, (0 <= q /\ q < nvals + 1) ->
           ((((_ /\ _) /\ _) /\ _) /\ _) /\ _ |- _ =>
      specialize (Hp k ltac:(lia));
      exact (conj (proj2 (proj1 (proj1 (proj1 Hp)))) (proj2 (proj1 (proj1 Hp))))
  end.
Qed.

Lemma proof_of_solver_partial_solve_wit_89_pure : solver_partial_solve_wit_89_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_89_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_89_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_89_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_90_pure_split_goal_1 : solver_partial_solve_wit_90_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_90_pure_split_goal_2 : solver_partial_solve_wit_90_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_90_pure : solver_partial_solve_wit_90_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_90_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_90_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_91_pure_split_goal_1 : solver_partial_solve_wit_91_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH63 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_91_pure_split_goal_2 : solver_partial_solve_wit_91_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH63 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_91_pure : solver_partial_solve_wit_91_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_91_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_91_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_92_pure_split_goal_1 : solver_partial_solve_wit_92_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_92_pure_split_goal_2 : solver_partial_solve_wit_92_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_92_pure : solver_partial_solve_wit_92_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_92_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_92_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_93_pure_split_goal_1 : solver_partial_solve_wit_93_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_93_pure_split_goal_2 : solver_partial_solve_wit_93_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_93_pure : solver_partial_solve_wit_93_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_93_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_93_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_94_pure_split_goal_1 : solver_partial_solve_wit_94_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_94_pure_split_goal_2 : solver_partial_solve_wit_94_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_94_pure : solver_partial_solve_wit_94_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_94_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_94_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_95_pure_split_goal_1 : solver_partial_solve_wit_95_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_95_pure_split_goal_2 : solver_partial_solve_wit_95_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_95_pure : solver_partial_solve_wit_95_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_95_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_95_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_96_pure_split_goal_1 : solver_partial_solve_wit_96_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_96_pure_split_goal_2 : solver_partial_solve_wit_96_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH65 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_96_pure : solver_partial_solve_wit_96_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_96_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_96_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_97_pure_split_goal_1 : solver_partial_solve_wit_97_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  match goal with H : nvals = uniq |- _ => rewrite <- H in Hk2 end.
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_97_pure_split_goal_2 : solver_partial_solve_wit_97_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_97_pure : solver_partial_solve_wit_97_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_97_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_97_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_98_pure_split_goal_1 : solver_partial_solve_wit_98_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  match goal with H : nvals = uniq |- _ => rewrite <- H in Hk2 end.
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_98_pure_split_goal_2 : solver_partial_solve_wit_98_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_98_pure : solver_partial_solve_wit_98_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_98_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_98_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_99_pure_split_goal_1 : solver_partial_solve_wit_99_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  match goal with H : nvals = uniq |- _ => rewrite <- H in Hk2 end.
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_99_pure_split_goal_2 : solver_partial_solve_wit_99_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_99_pure : solver_partial_solve_wit_99_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_99_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_99_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_100_pure_split_goal_1 : solver_partial_solve_wit_100_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  match goal with H : nvals = uniq |- _ => rewrite <- H in Hk2 end.
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_100_pure_split_goal_2 : solver_partial_solve_wit_100_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_100_pure : solver_partial_solve_wit_100_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_100_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_100_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_101_pure_split_goal_1 : solver_partial_solve_wit_101_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  match goal with H : nvals = uniq |- _ => rewrite <- H in Hk2 end.
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_101_pure_split_goal_2 : solver_partial_solve_wit_101_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_101_pure : solver_partial_solve_wit_101_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_101_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_101_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_102_pure_split_goal_1 : solver_partial_solve_wit_102_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  match goal with H : nvals = uniq |- _ => rewrite <- H in Hk2 end.
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_102_pure_split_goal_2 : solver_partial_solve_wit_102_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_102_pure : solver_partial_solve_wit_102_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_102_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_102_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_103_pure_split_goal_1 : solver_partial_solve_wit_103_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_103_pure_split_goal_2 : solver_partial_solve_wit_103_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_103_pure : solver_partial_solve_wit_103_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_103_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_103_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_104_pure_split_goal_1 : solver_partial_solve_wit_104_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_104_pure_split_goal_2 : solver_partial_solve_wit_104_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_104_pure : solver_partial_solve_wit_104_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_104_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_104_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_105_pure_split_goal_1 : solver_partial_solve_wit_105_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_105_pure_split_goal_2 : solver_partial_solve_wit_105_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_105_pure : solver_partial_solve_wit_105_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_105_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_105_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_106_pure_split_goal_1 : solver_partial_solve_wit_106_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_106_pure_split_goal_2 : solver_partial_solve_wit_106_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH67 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_106_pure : solver_partial_solve_wit_106_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_106_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_106_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_107_pure_split_goal_1 : solver_partial_solve_wit_107_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH65 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_107_pure_split_goal_2 : solver_partial_solve_wit_107_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  intros k Hk.
  assert (Hkr : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH65 k Hkr).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_107_pure : solver_partial_solve_wit_107_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_107_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_107_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_109_pure_split_goal_1 : solver_partial_solve_wit_109_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_109_pure_split_goal_2 : solver_partial_solve_wit_109_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_109_pure_split_goal_3 : solver_partial_solve_wit_109_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_109_pure_split_goal_4 : solver_partial_solve_wit_109_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_109_pure_split_goal_5 : solver_partial_solve_wit_109_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.
