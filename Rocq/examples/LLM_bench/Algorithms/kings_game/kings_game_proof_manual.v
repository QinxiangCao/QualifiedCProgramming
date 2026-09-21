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
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH9 : (MinisterHandsBound ps )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  apply minister_swap_permutation__flat_bubble;
    rewrite PreH7; lia.
Qed.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_2 : swap_ministers_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH9 : (MinisterHandsBound ps )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  apply flat_ministers_swap__flat_bubble; auto;
    rewrite PreH7; lia.
Qed.

Lemma proof_of_swap_ministers_return_wit_1_split_goal_3 : swap_ministers_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH9 : (MinisterHandsBound ps )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
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
Qed. 

Lemma proof_of_kings_game_safety_wit_28_split_goal_1 : kings_game_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH17 : (MinisterHandsBound cur )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur n_pre pass ltac:(lia)) PreH25) as ReusePreH19.
  pose proof (proj1 (bubble_scan_facts cur n_pre pass j ltac:(lia)) PreH26) as ReusePreH20.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur (j + 1) PreH19 ReusePreH17 ltac:(lia)) as Hproduct.
  lia.
Qed.

Lemma proof_of_kings_game_safety_wit_28_split_goal_2 : kings_game_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH17 : (MinisterHandsBound cur )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur n_pre pass ltac:(lia)) PreH25) as ReusePreH19.
  pose proof (proj1 (bubble_scan_facts cur n_pre pass j ltac:(lia)) PreH26) as ReusePreH20.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur (j + 1) PreH19 ReusePreH17 ltac:(lia)) as Hproduct.
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
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH17 : (MinisterHandsBound cur )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur n_pre pass ltac:(lia)) PreH25) as ReusePreH19.
  pose proof (proj1 (bubble_scan_facts cur n_pre pass j ltac:(lia)) PreH26) as ReusePreH20.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur j PreH19 ReusePreH17 ltac:(lia)) as Hproduct.
  lia.
Qed.

Lemma proof_of_kings_game_safety_wit_29_split_goal_2 : kings_game_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH17 : (MinisterHandsBound cur )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur n_pre pass ltac:(lia)) PreH25) as ReusePreH19.
  pose proof (proj1 (bubble_scan_facts cur n_pre pass j ltac:(lia)) PreH26) as ReusePreH20.
  dump_pre_spatial.
  pose proof
    (flat_minister_product_bounds__flat_bubble
      flat_cur cur j PreH19 ReusePreH17 ltac:(lia)) as Hproduct.
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
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH9 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (flat_ministers_Zlength__flat_bubble input_flat input PreH8).
  lia.
Qed.

Lemma proof_of_kings_game_entail_wit_1_split_goal_2 : kings_game_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_kings_game_entail_wit_1 : kings_game_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_kings_game_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_kings_game_entail_wit_1_split_goal_2.
Qed. 

Lemma proof_of_kings_game_entail_wit_2_split_goal_1 : kings_game_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH11 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
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
  right.
  intros.
  assert (ReusePreH11 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  replace k with (2 * n_pre) in * by lia.
  Exists input_flat input.
  split_pure_spatial.
  - rewrite sublist_self by lia.
    sep_apply (IntArray.seg_to_full ans_pre 0 (2 * n_pre) input_flat).
    replace (ans_pre + 0 * sizeof(INT)) with ans_pre by lia.
    replace (2 * n_pre - 0) with (2 * n_pre) by lia.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try exact PreH10;
      try apply Permutation_refl;
      try (match goal with |- BubbleOuterProperty ?ps ?n ?pass => apply (proj2 (bubble_outer_facts ps n pass ltac:(lia))); eapply bubble_outer_initial__flat_bubble; lia end).
Qed. 

Lemma proof_of_kings_game_entail_wit_4 : kings_game_entail_wit_4.
Proof.
  right.
  intros.
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH15 : (MinisterHandsBound cur_2 )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur_2 n_pre pass ltac:(lia)) PreH23) as ReusePreH17.
  Exists cur_2.
  repeat (split_pure_spatial || split_pures); try cancel; dump_pre_spatial; auto; try lia.
  all: try match goal with
    | |- BubbleOuterProperty ?ps ?n ?pass =>
        apply (proj2 (bubble_outer_facts ps n pass ltac:(rewrite ?minister_swap_Zlength__flat_bubble; lia)))
    | |- BubbleScanProperty ?ps ?n ?pass ?j =>
        apply (proj2 (bubble_scan_facts ps n pass j ltac:(lia)))
    end.

  - rewrite PreH8. exact ReusePreH17.
  - apply bubble_scan_initial__flat_bubble.
    rewrite PreH8.
    lia.
Qed. 

Lemma proof_of_kings_game_entail_wit_5_1 : kings_game_entail_wit_5_1.
Proof.
  right.
  intros.
  assert (SwapLength : Zlength (minister_swap cur_2 j (j + 1)) = n_pre) by
    (rewrite minister_swap_Zlength__flat_bubble; assumption).
  assert (ReusePreH3 : (MinisterHandsBound (minister_swap (cur_2) (j) ((j + 1 ))) )).
  { eapply Permutation_Forall.
    - eassumption.
    - apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (minister_hands_explicit _) ReusePreH3) as
    [SwappedLeftLower [SwappedLeftUpper [SwappedRightLower SwappedRightUpper]]].
  assert (ReusePreH15 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH22 : (MinisterHandsBound cur_2 )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur_2 n_pre pass ltac:(lia)) PreH28) as ReusePreH24.
  pose proof (proj1 (bubble_scan_facts cur_2 n_pre pass j ltac:(lia)) PreH29) as ReusePreH25.
  Exists (minister_swap cur_2 j (j + 1)).
  repeat (split_pure_spatial || split_pures); try cancel; dump_pre_spatial; auto; try lia.
  all: try match goal with
    | |- BubbleOuterProperty ?ps ?n ?pass =>
        apply (proj2 (bubble_outer_facts ps n pass ltac:(rewrite ?minister_swap_Zlength__flat_bubble; lia)))
    | |- BubbleScanProperty ?ps ?n ?pass ?j =>
        apply (proj2 (bubble_scan_facts ps n pass j ltac:(lia)))
    end.

  - eapply Permutation_trans; eauto.
  - rewrite PreH11.
    eapply bubble_outer_swap_prefix__flat_bubble; eauto; lia.
  - rewrite PreH11.
    eapply bubble_scan_step_swap__flat_bubble; eauto; try lia.
    pose proof
      (flat_minister_product_eq__flat_bubble
        flat_cur_2 cur_2 j PreH22 ltac:(lia)) as Hproduct_j.
    pose proof
      (flat_minister_product_eq__flat_bubble
        flat_cur_2 cur_2 (j + 1) PreH22 ltac:(lia)) as Hproduct_next.
    unfold MinisterProductLe.
    try rewrite <- Hproduct_j.
    try rewrite <- Hproduct_next.
    lia.
Qed. 

Lemma proof_of_kings_game_entail_wit_5_2 : kings_game_entail_wit_5_2.
Proof.
  right.
  intros.
  assert (ReusePreH11 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH18 : (MinisterHandsBound cur_2 )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur_2 n_pre pass ltac:(lia)) PreH26) as ReusePreH20.
  pose proof (proj1 (bubble_scan_facts cur_2 n_pre pass j ltac:(lia)) PreH27) as ReusePreH21.
  Exists cur_2.
  repeat (split_pure_spatial || split_pures); try cancel; dump_pre_spatial; auto; try lia.
  all: try match goal with
    | |- BubbleOuterProperty ?ps ?n ?pass =>
        apply (proj2 (bubble_outer_facts ps n pass ltac:(rewrite ?minister_swap_Zlength__flat_bubble; lia)))
    | |- BubbleScanProperty ?ps ?n ?pass ?j =>
        apply (proj2 (bubble_scan_facts ps n pass j ltac:(lia)))
    end.

  - rewrite PreH9. exact ReusePreH20.
  - rewrite PreH9.
    eapply bubble_scan_step_no_swap__flat_bubble; eauto; try lia.
    pose proof
      (flat_minister_product_eq__flat_bubble
        flat_cur_2 cur_2 j PreH20 ltac:(lia)) as Hproduct_j.
    pose proof
      (flat_minister_product_eq__flat_bubble
        flat_cur_2 cur_2 (j + 1) PreH20 ltac:(lia)) as Hproduct_next.
    unfold MinisterProductLe.
    try rewrite <- Hproduct_j.
    try rewrite <- Hproduct_next.
    lia.
Qed. 

Lemma proof_of_kings_game_entail_wit_6 : kings_game_entail_wit_6.
Proof.
  right.
  intros.
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH17 : (MinisterHandsBound cur_2 )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur_2 n_pre pass ltac:(lia)) PreH25) as ReusePreH19.
  pose proof (proj1 (bubble_scan_facts cur_2 n_pre pass j ltac:(lia)) PreH26) as ReusePreH20.
  Exists cur_2.
  repeat (split_pure_spatial || split_pures); try cancel; dump_pre_spatial; auto; try lia.
  all: try match goal with
    | |- BubbleOuterProperty ?ps ?n ?pass =>
        apply (proj2 (bubble_outer_facts ps n pass ltac:(rewrite ?minister_swap_Zlength__flat_bubble; lia)))
    | |- BubbleScanProperty ?ps ?n ?pass ?j =>
        apply (proj2 (bubble_scan_facts ps n pass j ltac:(lia)))
    end.

  rewrite PreH8.
  eapply bubble_outer_finish_pass__flat_bubble with (j := j); eauto.
  lia.
Qed. 

Lemma proof_of_kings_game_return_wit_1 : kings_game_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (ReusePreH10 : (MinisterHandsBound input )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  assert (ReusePreH15 : (MinisterHandsBound cur )).
  { apply (proj2 (minister_hands_explicit _)); repeat split; assumption. }
  pose proof (proj1 (bubble_outer_facts cur n_pre pass ltac:(lia)) PreH23) as ReusePreH17.
  Exists flat_cur. Exists cur.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial.
      eapply positive_sorted_realizes_kings_optimum__greedy_optimum.
      * lia.
      * rewrite PreH16; lia.
      * exact ReusePreH15.
      * eapply bubble_outer_final_sorted__greedy_optimum; eauto.
      * exact PreH22.
Qed. 

