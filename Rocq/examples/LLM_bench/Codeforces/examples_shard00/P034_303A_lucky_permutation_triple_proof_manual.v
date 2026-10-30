From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P034_303A_lucky_permutation_triple_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P034_303A_lucky_permutation_triple_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P034_303A_lucky_permutation_triple_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply identity_range_nil__identity_prefix.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (land_odd_mod_two__identity_prefix n_pre); lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply identity_range_snoc__identity_prefix.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  Exists (@nil Z) a_2.
  replace (n_pre + 0) with n_pre by lia.
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. apply identity_range_nil__identity_prefix.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (identity_range_snoc__identity_prefix i b_2 PreH8) as Hnew.
  Exists (b_2 ++ i :: nil) a_2.
  replace ((n_pre + i) + 1) with (n_pre + (i + 1)) by lia.
  split_pure_spatial.
  - cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact Hnew.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  Exists (@nil Z) b_2 a_2.
  split_pure_spatial.
  - replace (n_pre + n_pre) with (2 * n_pre) by lia.
    replace (2 * n_pre + 0) with (2 * n_pre) by lia.
    rewrite (IntArray.seg_empty out_pre (2 * n_pre) (2 * n_pre)).
    split_pure_spatial.
    + cancel (IntArray.seg out_pre 0 n_pre a_2).
      cancel (IntArray.seg out_pre n_pre (2 * n_pre) b_2).
      cancel (IntArray.undef_seg out_pre (2 * n_pre) (3 * n_pre)).
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply twice_mod_range_nil__twice_mod_prefix.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (c_2 ++ ((2 * i) mod n_pre :: nil)) b_2 a_2.
  split_pure_spatial.
  - replace ((2 * n_pre + i) + 1) with (2 * n_pre + (i + 1)) by lia.
    rewrite Z.rem_mod_nonneg by lia.
    cancel (IntArray.seg out_pre (2 * n_pre)
      (2 * n_pre + (i + 1)) (c_2 ++ ((2 * i) mod n_pre :: nil))).
    cancel (IntArray.undef_seg out_pre
      (2 * n_pre + (i + 1)) (3 * n_pre)).
    cancel (IntArray.seg out_pre 0 n_pre a_2).
    cancel (IntArray.seg out_pre n_pre (2 * n_pre) b_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply twice_mod_range_snoc__twice_mod_prefix; [lia | assumption].
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia. subst i.
  Exists a_2 b_2 c_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.seg_merge_to_seg out_pre 0 n_pre (2 * n_pre) a_2 b_2).
    + dump_pre_spatial. lia.
    + replace (2 * n_pre + n_pre) with (3 * n_pre) by lia.
      rewrite (IntArray.undef_seg_empty out_pre (3 * n_pre)).
      sep_apply_l_atomic
        (IntArray.seg_merge_to_full out_pre 0 (2 * n_pre) (3 * n_pre)
          (a_2 ++ b_2) c_2).
      * dump_pre_spatial. lia.
      * replace (out_pre + 0 * sizeof (INT)) with out_pre by ring.
        replace (3 * n_pre - 0) with (3 * n_pre) by ring.
        rewrite app_assoc.
        cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      pose proof (identity_range_permutation__lucky_spec
        n_pre a_2 ltac:(lia) PreH7) as Hpa.
      pose proof (identity_range_permutation__lucky_spec
        n_pre b_2 ltac:(lia) PreH8) as Hpb.
      assert (Hodd : n_pre mod 2 = 1).
      { apply rem_one_mod_two__lucky_spec; lia. }
      pose proof (twice_mod_range_permutation_odd__lucky_spec
        n_pre c_2 ltac:(lia) Hodd PreH9) as Hpc.
      destruct PreH7 as [Ha_len Ha_point].
      destruct PreH8 as [Hb_len Hb_point].
      destruct PreH9 as [Hc_len Hc_point].
      unfold Spec. left.
      exists ((a_2, b_2), c_2). split; [reflexivity |].
      unfold LuckyTriple. repeat split; try assumption.
      intros j Hj.
      rewrite Ha_point by lia.
      rewrite Hb_point by lia.
      rewrite Hc_point by lia.
      f_equal. ring.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec. right. split; [reflexivity |].
  intros triple Hluck.
  pose proof (land_even_mod_two__lucky_spec n_pre ltac:(lia) PreH1) as Heven.
  pose proof (lucky_triple_odd__lucky_spec n_pre triple ltac:(lia) Hluck) as Hodd.
  lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
