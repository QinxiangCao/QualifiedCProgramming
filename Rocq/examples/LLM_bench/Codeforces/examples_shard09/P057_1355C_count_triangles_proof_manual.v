From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P057_1355C_count_triangles_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P057_1355C_count_triangles_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P057_1355C_count_triangles_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply triangle_prefix_initial__prefix_initialization; lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_2 : solver_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_2 : solver_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_2 : solver_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (triangle_prefix_step__prefix_transition
      A_pre B_pre C_pre D_pre s total
      ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(split; lia) PreH18) as Hstep.
  replace
    (total + ((xhi - xlo + 1) * (zhi - C_pre + 1)))
    with (total + TriangleContribution A_pre B_pre C_pre D_pre s).
  - exact Hstep.
  - unfold TriangleContribution.
    rewrite <- PreH11, <- PreH12, <- PreH17.
    rewrite Z.max_r by lia.
    rewrite Z.max_r by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (triangle_prefix_step__prefix_transition
      A_pre B_pre C_pre D_pre s total
      ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(split; lia) PreH18) as Hstep.
  assert (Hslt : s - 1 < C_pre).
  {
    destruct (Z_le_gt_dec D_pre (s - 1)) as [Hle | Hgt].
    - rewrite Z.min_l in PreH17 by lia. lia.
    - rewrite Z.min_r in PreH17 by lia. lia.
  }
  replace total with
    (total + TriangleContribution A_pre B_pre C_pre D_pre s).
  - exact Hstep.
  - unfold TriangleContribution.
    replace (Z.max 0 (Z.min D_pre (s - 1) - C_pre + 1)) with 0.
    2: { symmetry. apply Z.max_l.
         pose proof (Z.le_min_r D_pre (s - 1)); lia. }
    ring.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply triangle_prefix_complete__final_result; eauto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
