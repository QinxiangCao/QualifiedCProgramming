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
From SimpleC.EE.LLM_bench.Algorithms.kings_game Require Import kings_game_goal.
From SimpleC.EE.LLM_bench.Algorithms.kings_game Require Import kings_game_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib.
Local Open Scope sac.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_1 : swap_ministers_return_wit_1_split_goal_1.
Proof.
  pre_process.
  apply minister_swap_permutation__flat_bubble;
    rewrite PreH7; lia.
Qed.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_2 : swap_ministers_return_wit_1_split_goal_2.
Proof.
  pre_process.
  apply minister_swap_hands_bound__flat_bubble; auto;
    rewrite PreH7; lia.
Qed.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_3 : swap_ministers_return_wit_1_split_goal_3.
Proof.
  pre_process.
  apply flat_ministers_swap__flat_bubble; auto;
    rewrite PreH7; lia.
Qed.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_4 : swap_ministers_return_wit_1_split_goal_4.
Proof.
  pre_process.
  rewrite minister_swap_Zlength__flat_bubble.
  exact PreH7.
Qed.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_5 : swap_ministers_return_wit_1_split_goal_5.
Proof.
  pre_process.
  apply minister_swap_flat_preprocess_form__flat_bubble with (n := n_pre).
  - pose proof (flat_ministers_Zlength__flat_bubble flat ps PreH8).
    lia.
  - lia.
  - lia.
Qed.

Lemma proof_of_swap_ministers_return_wit_1 : swap_ministers_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_ministers_return_wit_1_split_goal_1.
  - Goal_apply proof_of_swap_ministers_return_wit_1_split_goal_2.
  - Goal_apply proof_of_swap_ministers_return_wit_1_split_goal_3.
  - Goal_apply proof_of_swap_ministers_return_wit_1_split_goal_4.
  - Goal_apply proof_of_swap_ministers_return_wit_1_split_goal_5.
Qed.

Lemma proof_of_kings_game_safety_wit_28_split_goal_1 : kings_game_safety_wit_28_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur (j + 1) PreH16 PreH17 ltac:(lia)) as Hproduct.
  lia.
Qed.

Lemma proof_of_kings_game_safety_wit_28_split_goal_2 : kings_game_safety_wit_28_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur (j + 1) PreH16 PreH17 ltac:(lia)) as Hproduct.
  lia.
Qed.

Lemma proof_of_kings_game_safety_wit_28 : kings_game_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_kings_game_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_kings_game_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_kings_game_safety_wit_29_split_goal_1 : kings_game_safety_wit_29_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur j PreH16 PreH17 ltac:(lia)) as Hproduct.
  lia.
Qed.

Lemma proof_of_kings_game_safety_wit_29_split_goal_2 : kings_game_safety_wit_29_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur j PreH16 PreH17 ltac:(lia)) as Hproduct.
  lia.
Qed.

Lemma proof_of_kings_game_safety_wit_29 : kings_game_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_kings_game_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_kings_game_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_kings_game_entail_wit_1_split_goal_1 : kings_game_entail_wit_1_split_goal_1.
Proof.
  pre_process.
  pose proof (flat_ministers_Zlength__flat_bubble input_flat input PreH8).
  lia.
Qed.

Lemma proof_of_kings_game_entail_wit_1_split_goal_2 : kings_game_entail_wit_1_split_goal_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_kings_game_entail_wit_1 : kings_game_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_kings_game_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_kings_game_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_kings_game_entail_wit_2_split_goal_1 : kings_game_entail_wit_2_split_goal_1.
Proof.
  pre_process.
  rewrite (sublist_split 0 (k + 1) k input_flat) by lia.
  rewrite (sublist_single 0 k input_flat) by lia.
  reflexivity.
Qed.

Lemma proof_of_kings_game_entail_wit_2 : kings_game_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_kings_game_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_kings_game_entail_wit_3 : kings_game_entail_wit_3.
Proof.
  aggressive_pre_process.
  Exists input.
  entailer!.
  - apply bubble_outer_initial__flat_bubble.
    exact PreH8.
  - replace k with (Zlength input_flat) by lia.
    rewrite sublist_self by reflexivity.
    exact PreH10.
Qed.

Lemma proof_of_kings_game_entail_wit_4 : kings_game_entail_wit_4.
Proof.
  aggressive_pre_process.
  Exists cur_2.
  entailer!.
  apply bubble_scan_initial__flat_bubble.
  lia.
Qed.

Lemma proof_of_kings_game_entail_wit_5_1 : kings_game_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Exists (minister_swap cur_2 j (j + 1)).
  entailer!.
  - eapply bubble_scan_step_swap__flat_bubble; eauto; try lia.
    pose proof
      (flat_minister_product_eq__flat_bubble
        flat_cur_2 cur_2 j PreH21 ltac:(lia)) as Hproduct_j.
    pose proof
      (flat_minister_product_eq__flat_bubble
        flat_cur_2 cur_2 (j + 1) PreH21 ltac:(lia)) as Hproduct_next.
    unfold MinisterProductLe.
    rewrite <- Hproduct_j, <- Hproduct_next.
    lia.
  - eapply bubble_outer_swap_prefix__flat_bubble; eauto; lia.
  - eapply Permutation_trans; eauto.
Qed.

Lemma proof_of_kings_game_entail_wit_5_2 : kings_game_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Exists cur_2.
  entailer!.
  eapply bubble_scan_step_no_swap__flat_bubble; eauto; try lia.
  pose proof
    (flat_minister_product_eq__flat_bubble
      flat_cur_2 cur_2 j PreH17 ltac:(lia)) as Hproduct_j.
  pose proof
    (flat_minister_product_eq__flat_bubble
      flat_cur_2 cur_2 (j + 1) PreH17 ltac:(lia)) as Hproduct_next.
  unfold MinisterProductLe.
  rewrite <- Hproduct_j, <- Hproduct_next.
  exact PreH1.
Qed.

Lemma proof_of_kings_game_entail_wit_6 : kings_game_entail_wit_6.
Proof.
  aggressive_pre_process.
  Exists cur_2.
  entailer!.
  eapply bubble_outer_finish_pass__flat_bubble with (j := j); eauto.
  lia.
Qed.

Lemma proof_of_kings_game_return_wit_1 : kings_game_return_wit_1.
Proof.
  pre_process.
  Exists flat_cur. Exists cur.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial.
      eapply positive_sorted_realizes_kings_optimum__greedy_optimum.
      * lia.
      * rewrite PreH13; lia.
      * exact PreH15.
      * eapply bubble_outer_final_sorted__greedy_optimum; eauto.
      * exact PreH16.
Qed.
