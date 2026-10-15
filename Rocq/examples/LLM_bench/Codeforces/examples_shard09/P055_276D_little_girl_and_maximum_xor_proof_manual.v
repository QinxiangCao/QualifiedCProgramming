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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P055_276D_little_girl_and_maximum_xor_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P055_276D_little_girl_and_maximum_xor_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HighestBitScan.
  split; [reflexivity|].
  intros k Hk.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply lxor_u64_bound__bit_scan_transitions; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (0 <= Z.lxor l_pre r_pre).
  { rewrite Z.lxor_nonneg. lia. }
  lia.
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
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (highest_bit_scan_zero_step__bit_scan_transitions
       l_pre r_pre x b ltac:(lia) ltac:(lia) PreH9 PreH1) as [_ Hscan].
  exact Hscan.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (highest_bit_scan_zero_step__bit_scan_transitions
       l_pre r_pre x b ltac:(lia) ltac:(lia) PreH9 PreH1) as [Hb _].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmask : unsigned_last_nbits (Z.lnot 0) 64 = 2 ^ 64 - 1).
  { unfold unsigned_last_nbits.
    rewrite Z.lnot_0.
    symmetry.
    apply Z.mod_unique with (-1).
    - left. pose proof (Z.pow_pos_nonneg 2 64). lia.
    - lia. }
  rewrite Hmask.
  subst b.
  apply interval_max_xor_from_scan__interval_maximum with (x := x) (b := 63);
    try lia; assumption.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hb : 0 <= b < 63) by lia.
  assert (Hmask :
    unsigned_last_nbits
      (unsigned_last_nbits (Z.shiftl 1 (b + 1)) 64 - 1) 64 =
    2 ^ (b + 1) - 1).
  { unfold unsigned_last_nbits.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    assert (Hmod : 2 ^ (b + 1) mod 2 ^ 64 = 2 ^ (b + 1)).
    { apply Z.mod_small. split.
      - apply Z.pow_nonneg; lia.
      - apply Z.pow_lt_mono_r; lia. }
    rewrite Hmod.
    rewrite Z.mod_small.
    2: { split.
         - pose proof (Z.pow_pos_nonneg 2 (b + 1)); lia.
         - apply Z.lt_le_trans with (2 ^ (b + 1)); [lia|].
           apply Z.pow_le_mono_r; lia. }
    reflexivity. }
  rewrite Hmask.
  apply interval_max_xor_from_scan__interval_maximum with (x := x) (b := b);
    try lia; assumption.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj1 (Z.lxor_eq_0_iff l_pre r_pre)) in PreH1.
  rewrite <- PreH1.
  unfold Spec, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists 0. split.
  - split.
    + exists l_pre, l_pre. repeat split; try lia.
      symmetry. apply Z.lxor_nilpotent.
    + intros v Hv.
      destruct Hv as [a [d [[Hla Had] [Hdl Hv]]]].
      assert (a = l_pre) by lia.
      assert (d = l_pre) by lia.
      subst a; subst d; subst v.
      rewrite Z.lxor_nilpotent. lia.
  - reflexivity.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.
