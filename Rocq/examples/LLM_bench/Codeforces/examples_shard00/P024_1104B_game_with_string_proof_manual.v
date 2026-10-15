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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P024_1104B_game_with_string_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P024_1104B_game_with_string_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixGameState, PairDeletionTraceTo, PairDeletionIrreducible.
  repeat split.
  - lia.
  - exists (@cons (list Z) (@nil Z) (@nil (list Z))).
    repeat split; simpl; try lia; try reflexivity.
  - intros next Hdel.
    unfold OneEqualPairDeletion in Hdel.
    destruct Hdel as [idx [Hidx _]].
    simpl in Hidx.
    lia.
  - intros states Htrace.
    unfold DeletionGameTrace in Htrace.
    destruct Htrace as [Hpos [Hfirst [Hsteps Hterminal]]].
    assert (Hlen : Zlength states <= 1).
    { destruct (Z_lt_ge_dec 1 (Zlength states)) as [Hgt | Hle].
      - specialize (Hsteps 0 ltac:(lia)).
        unfold OneEqualPairDeletion in Hsteps.
        destruct Hsteps as [idx [Hidx _]].
        rewrite Hfirst in Hidx.
        simpl in Hidx.
        lia.
      - lia. }
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH3.
  assumption.
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
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength text).
  { eapply sentinel_nonzero_index_bound__stack_transitions; eauto; lia. }
  rewrite app_Znth1 in PreH1 by lia.
  assert (Hprefix :
    sublist 0 (i + 1) text =
      sublist 0 i text ++ (Znth i text 0 :: nil)).
  { rewrite (sublist_split 0 (i + 1) i text) by lia.
    rewrite (sublist_single 0 i text) by lia.
    reflexivity. }
  assert (Hstate : PrefixGameState (sublist 0 (i + 1) text)
    (sublist 0 (top - 1) reduced_2) (moves + 1)).
  { rewrite Hprefix, PreH10.
    apply prefix_game_state_pop_pair__stack_transitions.
    - exact PreH14.
    - rewrite <- PreH10. lia.
    - rewrite <- PreH10.
      exact PreH1. }
  Exists (sublist 0 (top - 1) reduced_2).
  split_pure_spatial.
  - cancel (CharArray.full s_pre (Zlength text + 1) (text ++ (0 :: nil))).
    sep_apply_l_atomic
      (CharArray.full_split_to_full (&( "stack" )) (top - 1) top reduced_2).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.full_to_undef_full
          ((&( "stack" )) + (top - 1) * 1) (top - (top - 1))
          (sublist (top - 1) top reduced_2)).
      replace (top - (top - 1)) with 1 by lia.
      rewrite <- (CharArray.undef_seg_shift (&( "stack" )) (top - 1) 0 1).
      replace (top - 1 + 0) with (top - 1) by lia.
      replace (top - 1 + 1) with top by lia.
      sep_apply_l_atomic
        (CharArray.undef_seg_merge_to_undef_seg
          (&( "stack" )) (top - 1) top 100005).
      * dump_pre_spatial. lia.
      * cancel.
  - split_pures; dump_pre_spatial.
    all: try lia.
    all: try assumption.
    all: try (rewrite Zlength_sublist0 by lia; lia).
    all: exact Hstate.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength text).
  { eapply sentinel_nonzero_index_bound__stack_transitions; eauto; lia. }
  assert (Hempty : reduced_2 = (@nil Z)).
  { destruct reduced_2 as [|x xs]; [reflexivity|].
    rewrite Zlength_cons in PreH9.
    pose proof (Zlength_nonneg xs).
    lia. }
  rewrite <- PreH12.
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (sublist_single 0 i text) by lia.
  apply prefix_game_state_push__stack_transitions.
  - exact PreH13.
  - left. exact Hempty.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (sentinel_nonzero_index_bound__stack_transitions
    text i ltac:(lia) PreH14) as Hi.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength text).
  { eapply sentinel_nonzero_index_bound__stack_transitions; eauto; lia. }
  rewrite app_Znth1 in PreH1 by lia.
  rewrite <- PreH13.
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (sublist_single 0 i text) by lia.
  apply prefix_game_state_push__stack_transitions.
  - exact PreH14.
  - right. split.
    + rewrite <- PreH10. lia.
    + rewrite <- PreH10.
      exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_3 : solver_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (sentinel_nonzero_index_bound__stack_transitions
    text i ltac:(lia) PreH15) as Hi.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (terminator_zero_index_eq_length__final_result
                text i ltac:(lia) PreH3 PreH13) as Hi.
  rewrite (sublist_self text i Hi) in PreH12.
  pose proof (prefix_game_state_spec_parity__final_result
                text reduced moves PreH12) as Hspec.
  dump_pre_spatial.
  exact Hspec.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (CharArray.full_to_undef_full
                        (&( "stack" )) top reduced).
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg
                        (&( "stack" )) top).
  sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_full
                        (&( "stack" )) 0 top 100005 ltac:(lia)).
  replace (&( "stack" ) + 0 * sizeof (CHAR)) with (&( "stack" )) by lia.
  replace (100005 - 0) with 100005 by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
