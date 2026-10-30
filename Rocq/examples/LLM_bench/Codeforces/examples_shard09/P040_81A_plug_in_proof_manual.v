From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P040_81A_plug_in_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P040_81A_plug_in_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec, ReducedFrom.
  exists ((@nil Z) :: (@nil (list Z))).
  split.
  - discriminate.
  - split.
    + simpl.
      rewrite Zsublist_nil by lia.
      reflexivity.
    + split.
      * reflexivity.
      * split.
        -- intros i Hi.
           simpl in Hi.
           lia.
        -- intros [q Hdelete].
           unfold DeletePair in Hdelete.
           destruct Hdelete as [i [Hi _]].
           simpl in Hi.
           lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH3.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstack_nonempty : stack_2 <> (@nil Z)).
  { intro Hnil. subst stack_2. rewrite Zlength_nil in PreH12. lia. }
  assert (Hprefix :
    sublist 0 (i + 1) text = sublist 0 i text ++ (Znth i text 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i text) by lia.
    rewrite (sublist_single 0 i text) by lia. reflexivity. }
  assert (Hspec : Spec (sublist 0 (i + 1) text)
    (sublist 0 (top - 1) stack_2)).
  { rewrite PreH12. rewrite Hprefix.
    apply Spec_extend_drop_equal__stack_transitions; try assumption.
    rewrite <- PreH12. exact PreH1. }
  Exists (sublist 0 (top - 1) stack_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre text).
    sep_apply_l_atomic
      (CharArray.full_split_to_full out_pre (top - 1) top stack_2).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.full_to_undef_full
          (out_pre + (top - 1) * 1) (top - (top - 1))
          (sublist (top - 1) top stack_2)).
      replace (top - (top - 1)) with 1 by lia.
      rewrite <- (CharArray.undef_seg_shift out_pre (top - 1) 0 1).
      replace (top - 1 + 0) with (top - 1) by lia.
      replace (top - 1 + 1) with top by lia.
      sep_apply_l_atomic
        (CharArray.undef_seg_merge_to_undef_seg out_pre (top - 1) top (n_pre + 1)).
      * dump_pre_spatial. lia.
      * cancel.
  - split_pures; dump_pre_spatial.
    all: try lia.
    all: try assumption.
    all: try (rewrite Zlength_sublist0 by lia; lia).
    all: exact Hspec.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Htop : top = 0) by lia.
  assert (stack_2 = (@nil Z)).
  { destruct stack_2 as [|x xs]; [reflexivity|].
    rewrite Zlength_cons in PreH11. pose proof (Zlength_nonneg xs). lia. }
  subst top. subst stack_2.
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (sublist_single 0 i text) by lia.
  apply Spec_extend_keep_distinct__stack_transitions.
  - exact PreH12.
  - left. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
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
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (sublist_single 0 i text) by lia.
  apply Spec_extend_keep_distinct__stack_transitions.
  - exact PreH13.
  - right. rewrite <- PreH12. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_self text i) in PreH11 by lia.
  rewrite PreH10.
  Exists stack.
  split_pure_spatial.
  - cancel.
    cancel (CharArray.full out_pre (Zlength stack + 1) (stack +:: 0)).
  - split_pures.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. lia.
Qed.
