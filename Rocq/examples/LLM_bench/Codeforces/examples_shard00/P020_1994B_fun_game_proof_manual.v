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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P020_1994B_fun_game_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P020_1994B_fun_game_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P020_1994B_fun_game_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    assert (Hvalid_target : valid_string target);
    [ unfold valid_string, all_ascii, no_inner_nul;
      split; intros k Hk; destruct (PreH10 k Hk); lia
    | unfold string_length; lia ]).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    assert (Hvalid_source : valid_string source);
    [ unfold valid_string, all_ascii, no_inner_nul;
      split; intros k Hk; destruct (PreH9 k Hk); lia
    | unfold string_length; lia ]).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros k Hk; destruct (PreH10 k Hk); lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros k Hk; destruct (PreH9 k Hk); lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_5 : solver_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH2.
  dump_pre_spatial.
  exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_6 : solver_entail_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_7 : solver_entail_wit_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold string_length, c_string.
  rewrite <- PreH5, <- PreH4.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth1 in PreH2 by lia.
  specialize (PreH10 i ltac:(lia)).
  destruct PreH10 as [H48 | H49].
  - contradiction.
  - exact H49.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = i) by lia. subst j.
  unfold Spec.
  split; [lia |].
  split.
  - intros _.
    apply (game_reachable_from_first_one__game_semantics source target i);
      try assumption; try lia.
  - intros _. lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  split; [lia |].
  split.
  - intros Hfalse. lia.
  - intros Hreach.
    exfalso.
    pose proof
      (game_reachable_preserves_zero_prefix__game_semantics
         source target i ltac:(lia) PreH14 Hreach) as [_ Hzero].
    pose proof (Hzero j ltac:(lia)) as Htarget_j.
    rewrite app_Znth1 in PreH1 by lia.
    contradiction.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  split; [lia |].
  split.
  - intros Hfalse. lia.
  - intros Hreach.
    exfalso.
    assert (source <> target) as Hneq.
    { intros Heq. subst target.
      unfold strncmp_result in PreH2.
      destruct PreH2 as (k & Hk0 & Hks & Hkt & Hprefix & Hend).
      destruct Hend as [[_ ->] | (_ & Hret & _)]; [contradiction |].
      rewrite Hret in PreH1.
      exfalso. apply PreH1. lia. }
    pose proof
      (game_reachable_preserves_zero_prefix__game_semantics
         source target n_pre ltac:(lia) PreH13 Hreach) as [_ Htarget_zero].
    apply Hneq.
    apply (proj2 (list_eq_ext source target 0)).
    split; [lia |].
    intros k Hk.
    rewrite PreH13 by lia.
    symmetry. apply Htarget_zero. lia.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_spatial : solver_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold c_string.
  rewrite PreH16, PreH17.
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
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  assert (source = target) as Heq.
  { unfold strncmp_result in PreH2.
    destruct PreH2 as (k & Hk0 & Hks & Hkt & Hprefix & Hend).
    destruct Hend as [[Hkn _] | (Hkn & Hret & Hstop)].
    - apply (proj2 (list_eq_ext source target 0)).
      split; [lia |].
      intros j Hj.
      specialize (Hprefix j ltac:(lia)).
      unfold c_string in Hprefix.
      rewrite !app_Znth1 in Hprefix by lia.
      exact Hprefix.
    - assert (Znth k (c_string source) 0 =
              Znth k (c_string target) 0) as Hsame by lia.
      destruct Hstop as [Hzero | Hneq]; [|contradiction].
      pose proof
        (c_string_zero_index_eq_length source k PreH14 ltac:(lia) Hks Hzero)
        as Hkend.
      unfold string_length in Hkend.
      lia. }
  subst target.
  unfold Spec.
  split; [lia |].
  split.
  - intros _. exists 0%nat. hnf. reflexivity.
  - intros _. lia.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_spatial : solver_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold c_string.
  rewrite PreH16, PreH17.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.
