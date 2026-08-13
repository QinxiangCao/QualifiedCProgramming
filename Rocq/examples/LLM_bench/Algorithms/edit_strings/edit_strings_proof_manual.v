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
From SimpleC.EE.LLM_bench.Algorithms.edit_strings Require Import edit_strings_goal.
From SimpleC.EE.LLM_bench.Algorithms.edit_strings Require Import edit_strings_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib.
Local Open Scope sac.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_1 : max_edit_string_matches_entail_wit_1_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_1_split_goal_1.
  intros.
  eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_2 : max_edit_string_matches_entail_wit_1_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_1_split_goal_2.
  intros.
  eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_3 : max_edit_string_matches_entail_wit_1_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_1_split_goal_3.
  intros.
  eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_4 : max_edit_string_matches_entail_wit_1_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_1_split_goal_4.
  intros.
  eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_5 : max_edit_string_matches_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold EditZeroPrefix; split; simpl; intros;
    try rewrite Zlength_nil; try lia; auto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_6 : max_edit_string_matches_entail_wit_1_split_goal_6.
Proof.
  exact proof_of_max_edit_string_matches_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_7 : max_edit_string_matches_entail_wit_1_split_goal_7.
Proof.
  exact proof_of_max_edit_string_matches_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_8 : max_edit_string_matches_entail_wit_1_split_goal_8.
Proof.
  exact proof_of_max_edit_string_matches_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1 : max_edit_string_matches_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_1_split_goal_8.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_1 : max_edit_string_matches_entail_wit_2_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_2_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_2 : max_edit_string_matches_entail_wit_2_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_2_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_3 : max_edit_string_matches_entail_wit_2_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_2_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_4 : max_edit_string_matches_entail_wit_2_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_2_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_5 : max_edit_string_matches_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditZeroPrefix_snoc_zero__zeroing_and_base_build; eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_6 : max_edit_string_matches_entail_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditZeroPrefix_snoc_zero__zeroing_and_base_build; eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_7 : max_edit_string_matches_entail_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditZeroPrefix_snoc_zero__zeroing_and_base_build; eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_8 : max_edit_string_matches_entail_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditZeroPrefix_snoc_zero__zeroing_and_base_build; eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2 : max_edit_string_matches_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_8.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_3_split_goal_1 : max_edit_string_matches_entail_wit_3_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_3_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_3_split_goal_2 : max_edit_string_matches_entail_wit_3_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_3_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_3_split_goal_3 : max_edit_string_matches_entail_wit_3_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_3_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_3_split_goal_4 : max_edit_string_matches_entail_wit_3_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_3_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_3 : max_edit_string_matches_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.undef_full seg1_pre n_pre).
    cancel (IntArray.undef_full seg2_pre n_pre).
    cancel (IntArray.seg cnt10_pre 0 (i + 1) c10_2).
    cancel (IntArray.undef_seg cnt10_pre (i + 1) n_pre).
    cancel (IntArray.seg cnt11_pre 0 (i + 1) c11_2).
    cancel (IntArray.undef_seg cnt11_pre (i + 1) n_pre).
    cancel (IntArray.seg cnt20_pre 0 (i + 1) c20_2).
    cancel (IntArray.undef_seg cnt20_pre (i + 1) n_pre).
    cancel (IntArray.seg cnt21_pre 0 (i + 1) c21_2).
    cancel (IntArray.undef_seg cnt21_pre (i + 1) n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_4 : max_edit_string_matches_entail_wit_4.
Proof.
  aggressive_pre_process.
  replace i with n_pre in * by lia.
  Exists c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full cnt10_pre 0 n_pre c10_2).
    replace (cnt10_pre + 0 * sizeof(INT)) with cnt10_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    sep_apply (IntArray.seg_to_full cnt11_pre 0 n_pre c11_2).
    replace (cnt11_pre + 0 * sizeof(INT)) with cnt11_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    sep_apply (IntArray.seg_to_full cnt20_pre 0 n_pre c20_2).
    replace (cnt20_pre + 0 * sizeof(INT)) with cnt20_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    sep_apply (IntArray.seg_to_full cnt21_pre 0 n_pre c21_2).
    replace (cnt21_pre + 0 * sizeof(INT)) with cnt21_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try (eapply EditZeroFull_scratch_bound__zeroing_and_base_build; try lia;
        eapply EditZeroPrefix_to_full_at_bound__zeroing_and_base_build; eauto; lia);
      try (eapply EditZeroPrefix_to_full_at_bound__zeroing_and_base_build; eauto; lia).
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_5 : max_edit_string_matches_entail_wit_5.
Proof.
  aggressive_pre_process.
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_single seg1_pre 0 0).
    change (0 + 1) with 1.
    cancel (IntArray.seg seg1_pre 0 1 (0 :: nil)).
  - split_pures; dump_pre_spatial; simpl;
      try rewrite Zlength_cons; try rewrite Zlength_nil; eauto; try lia;
      try (destruct PreH11 as [_ Hzero10]; rewrite Hzero10 by lia; lia);
      try (destruct PreH12 as [_ Hzero11]; rewrite Hzero11 by lia; lia).
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_1 : max_edit_string_matches_entail_wit_6_1_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_2 : max_edit_string_matches_entail_wit_6_1_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_3 : max_edit_string_matches_entail_wit_6_1_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_4 : max_edit_string_matches_entail_wit_6_1_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_6_1_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_5 : max_edit_string_matches_entail_wit_6_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditScratchCountsBound_replace_c10_zero_inc__zeroing_and_base_build; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_6 : max_edit_string_matches_entail_wit_6_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditBuildState_initial_s1_zero__zeroing_and_base_build; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_1 : max_edit_string_matches_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_1_split_goal_6.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_1 : max_edit_string_matches_entail_wit_6_2_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_2 : max_edit_string_matches_entail_wit_6_2_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_3 : max_edit_string_matches_entail_wit_6_2_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_4 : max_edit_string_matches_entail_wit_6_2_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_6_2_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_5 : max_edit_string_matches_entail_wit_6_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditScratchCountsBound_replace_c11_zero_inc__zeroing_and_base_build; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_6 : max_edit_string_matches_entail_wit_6_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply EditBuildState_initial_s1_one__zeroing_and_base_build; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_6_2 : max_edit_string_matches_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_6_2_split_goal_6.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_7_split_goal_1 : max_edit_string_matches_entail_wit_7_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_7_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_7_split_goal_2 : max_edit_string_matches_entail_wit_7_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_7_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_7_split_goal_3 : max_edit_string_matches_entail_wit_7_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_7_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_7_split_goal_4 : max_edit_string_matches_entail_wit_7_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_7_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_7 : max_edit_string_matches_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists c21_2 c20_2 sg1_2 c10_2 c11_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.seg seg1_pre 0 1 sg1_2).
    cancel (IntArray.undef_seg seg1_pre 1 n_pre).
    cancel (IntArray.undef_full seg2_pre n_pre).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_1 : max_edit_string_matches_entail_wit_8_1_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_2 : max_edit_string_matches_entail_wit_8_1_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_3 : max_edit_string_matches_entail_wit_8_1_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_4 : max_edit_string_matches_entail_wit_8_1_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_8_1_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_5 : max_edit_string_matches_entail_wit_8_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast :
    Znth i (sg1_2 ++ Znth ((i - 1) - 0) sg1_2 0 :: nil) 0 =
    Znth ((i - 1) - 0) sg1_2 0).
  {
    rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  }
  rewrite Hlast.
  replace ((i - 1) - 0) with (i - 1) by lia.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       _ _ _ Hseg ltac:(lia)) as Hblock_bounds.
  pose proof (Hcnt11 (Znth (i - 1) sg1_2 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_6 : max_edit_string_matches_entail_wit_8_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast :
    Znth i (sg1_2 ++ Znth ((i - 1) - 0) sg1_2 0 :: nil) 0 =
    Znth ((i - 1) - 0) sg1_2 0).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    replace ((i - 1) - 0) with (i - 1) by lia.
    pose proof
      (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
         _ _ _ Hseg ltac:(lia)) as Hblock_bounds.
    pose proof (Hcnt10 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    pose proof (Hcnt11 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_7 : max_edit_string_matches_entail_wit_8_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast :
    Znth i (sg1_2 ++ Znth ((i - 1) - 0) sg1_2 0 :: nil) 0 =
    Znth ((i - 1) - 0) sg1_2 0).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    replace ((i - 1) - 0) with (i - 1) by lia.
    pose proof
      (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
         _ _ _ Hseg ltac:(lia)) as Hblock_bounds.
    pose proof (Hcnt10 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    pose proof (Hcnt11 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_8 : max_edit_string_matches_entail_wit_8_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast :
    Znth i (sg1_2 ++ Znth ((i - 1) - 0) sg1_2 0 :: nil) 0 =
    Znth ((i - 1) - 0) sg1_2 0).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    replace ((i - 1) - 0) with (i - 1) by lia.
    pose proof
      (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
         _ _ _ Hseg ltac:(lia)) as Hblock_bounds.
    pose proof (Hcnt10 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    pose proof (Hcnt11 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_9 : max_edit_string_matches_entail_wit_8_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast :
    Znth i (sg1_2 ++ Znth ((i - 1) - 0) sg1_2 0 :: nil) 0 =
    Znth ((i - 1) - 0) sg1_2 0).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    replace ((i - 1) - 0) with (i - 1) by lia.
    pose proof
      (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
         _ _ _ Hseg ltac:(lia)) as Hblock_bounds.
    pose proof (Hcnt10 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    pose proof (Hcnt11 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_10 : max_edit_string_matches_entail_wit_8_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast :
    Znth i (sg1_2 ++ Znth ((i - 1) - 0) sg1_2 0 :: nil) 0 =
    Znth ((i - 1) - 0) sg1_2 0).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    replace ((i - 1) - 0) with (i - 1) by lia.
    pose proof
      (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
         _ _ _ Hseg ltac:(lia)) as Hblock_bounds.
    pose proof (Hcnt10 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    pose proof (Hcnt11 (Znth (i - 1) sg1_2 0) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_11 : max_edit_string_matches_entail_wit_8_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [_ Hcounts]]]]. exact Hcounts.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_12 : max_edit_string_matches_entail_wit_8_1_split_goal_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace ((i - 1) - 0) with (i - 1) by lia.
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  eapply EditSegmentPrefix_extend_open__build_s1_segments_counts; eauto; try lia.
  unfold edit_edge_open; split; assumption.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_1 : max_edit_string_matches_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_8.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_9.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_10.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_11.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_1_split_goal_12.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_1 : max_edit_string_matches_entail_wit_8_2_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_2 : max_edit_string_matches_entail_wit_8_2_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_3 : max_edit_string_matches_entail_wit_8_2_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_4 : max_edit_string_matches_entail_wit_8_2_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_8_2_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_5 : max_edit_string_matches_entail_wit_8_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_6 : max_edit_string_matches_entail_wit_8_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_7 : max_edit_string_matches_entail_wit_8_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_8 : max_edit_string_matches_entail_wit_8_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_9 : max_edit_string_matches_entail_wit_8_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_10 : max_edit_string_matches_entail_wit_8_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_11 : max_edit_string_matches_entail_wit_8_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [_ Hcounts]]]]. exact Hcounts.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_12 : max_edit_string_matches_entail_wit_8_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH12 as [_ [_ [_ [Hseg _]]]].
  eapply EditSegmentPrefix_extend_new__build_s1_segments_counts; eauto; try lia.
  unfold edit_edge_open. intros [Hprev _]. contradiction.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_2 : max_edit_string_matches_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_8.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_9.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_10.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_11.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_2_split_goal_12.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_1 : max_edit_string_matches_entail_wit_8_3_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_2 : max_edit_string_matches_entail_wit_8_3_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_3 : max_edit_string_matches_entail_wit_8_3_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_4 : max_edit_string_matches_entail_wit_8_3_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_8_3_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_5 : max_edit_string_matches_entail_wit_8_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_6 : max_edit_string_matches_entail_wit_8_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_7 : max_edit_string_matches_entail_wit_8_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_8 : max_edit_string_matches_entail_wit_8_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_9 : max_edit_string_matches_entail_wit_8_3_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_10 : max_edit_string_matches_entail_wit_8_3_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  destruct PreH16 as [[_ Hcnt10] [[_ Hcnt11] _]].
  assert (Hlast : Znth i (sg1_2 ++ i :: nil) 0 = i).
  - rewrite app_Znth2 by (rewrite (proj1 Hseg); lia).
    rewrite (proj1 Hseg).
    replace (i - i) with 0 by lia.
    reflexivity.
  - rewrite Hlast.
    pose proof (Hcnt10 i ltac:(lia)).
    pose proof (Hcnt11 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_11 : max_edit_string_matches_entail_wit_8_3_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [_ Hcounts]]]]. exact Hcounts.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_12 : max_edit_string_matches_entail_wit_8_3_split_goal_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [_ [_ [_ [Hseg _]]]].
  eapply EditSegmentPrefix_extend_new__build_s1_segments_counts; eauto; try lia.
  unfold edit_edge_open. intros [_ Hcur]. contradiction.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_8_3 : max_edit_string_matches_entail_wit_8_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_8.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_9.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_10.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_11.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_8_3_split_goal_12.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_1 : max_edit_string_matches_entail_wit_9_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_9_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_2 : max_edit_string_matches_entail_wit_9_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_9_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_3 : max_edit_string_matches_entail_wit_9_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_9_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_4 : max_edit_string_matches_entail_wit_9_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_9_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_5 : max_edit_string_matches_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_6 : max_edit_string_matches_entail_wit_9_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_7 : max_edit_string_matches_entail_wit_9_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_8 : max_edit_string_matches_entail_wit_9_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_9 : max_edit_string_matches_entail_wit_9_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_10 : max_edit_string_matches_entail_wit_9_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9_split_goal_11 : max_edit_string_matches_entail_wit_9_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  end.
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_9 : max_edit_string_matches_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_8.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_9.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_10.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_9_split_goal_11.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_1 : max_edit_string_matches_entail_wit_10_1_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_2 : max_edit_string_matches_entail_wit_10_1_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_3 : max_edit_string_matches_entail_wit_10_1_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_4 : max_edit_string_matches_entail_wit_10_1_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_10_1_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_5 : max_edit_string_matches_entail_wit_10_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply (EditScratchCountsBound_inc_first__build_s1_segments_counts
            s1_l t1_l n_pre i c10_2 c11_2 c20_2 c21_2 block1); eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_6 : max_edit_string_matches_entail_wit_10_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply (EditBuildState_extend_zero__build_s1_segments_counts
            s1_l t1_l n_pre i sg1_2 c10_2 c11_2 block1); eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_1 : max_edit_string_matches_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_1_split_goal_6.
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_1 : max_edit_string_matches_entail_wit_10_2_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_2 : max_edit_string_matches_entail_wit_10_2_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_3 : max_edit_string_matches_entail_wit_10_2_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_4 : max_edit_string_matches_entail_wit_10_2_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_10_2_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_5 : max_edit_string_matches_entail_wit_10_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply (EditScratchCountsBound_inc_second__build_s1_segments_counts
            s1_l t1_l n_pre i c10_2 c11_2 c20_2 c21_2 block1); eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_6 : max_edit_string_matches_entail_wit_10_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply (EditBuildState_extend_one__build_s1_segments_counts
            s1_l t1_l n_pre i sg1_2 c10_2 c11_2 block1); eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_10_2 : max_edit_string_matches_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_10_2_split_goal_6.
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_split_goal_1 : max_edit_string_matches_entail_wit_11_split_goal_1.
Proof.
  unfold max_edit_string_matches_entail_wit_11_split_goal_1.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_11_split_goal_2 : max_edit_string_matches_entail_wit_11_split_goal_2.
Proof.
  unfold max_edit_string_matches_entail_wit_11_split_goal_2.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_11_split_goal_3 : max_edit_string_matches_entail_wit_11_split_goal_3.
Proof.
  unfold max_edit_string_matches_entail_wit_11_split_goal_3.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_11_split_goal_4 : max_edit_string_matches_entail_wit_11_split_goal_4.
Proof.
  unfold max_edit_string_matches_entail_wit_11_split_goal_4.
  intros.
  match goal with
  | H : forall idx : Z, _ -> _ |- _ => eapply H; lia
  | _ => lia
  end.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_11 : max_edit_string_matches_entail_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists c21_2 c20_2 sg1_2 c10_2 c11_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.seg seg1_pre 0 (i + 1) sg1_2).
    cancel (IntArray.undef_seg seg1_pre (i + 1) n_pre).
    cancel (IntArray.undef_full seg2_pre n_pre).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [intro Hbad; destruct Hbad; lia].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_12 : max_edit_string_matches_entail_wit_12.
Proof.
  aggressive_pre_process.
  replace i with n_pre in * by lia.
  Exists sg1_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full seg1_pre 0 n_pre sg1_2).
    replace (seg1_pre + 0 * sizeof(INT)) with seg1_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_13 : max_edit_string_matches_entail_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists c21_2 c20_2 sg1_2 c10_2 c11_2 (0 :: nil).
  pose proof PreH10 as Hzero21.
  unfold EditZeroFull in Hzero21.
  destruct Hzero21 as [_ Hzero21].
  pose proof PreH9 as Hzero20.
  unfold EditZeroFull in Hzero20.
  destruct Hzero20 as [_ Hzero20].
  split_pure_spatial.
  - sep_apply (IntArray.seg_single seg2_pre 0 0).
    cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.seg seg2_pre 0 1 (0 :: nil)).
    cancel (IntArray.undef_seg seg2_pre 1 n_pre).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia;
      try solve [rewrite Hzero21 by lia; lia];
      try solve [rewrite Hzero20 by lia; lia].
Qed. 

Lemma EditScratchCountsBound_replace_c20_zero_inc__manual :
  forall n c10 c11 c20 c21,
    1 <= n ->
    EditScratchCountsBound n c10 c11 c20 c21 ->
    EditZeroFull n c20 ->
    EditScratchCountsBound n c10 c11 (replace_Znth 0 (Znth 0 c20 0 + 1) c20) c21.
Proof.
  intros n c10 c11 c20 c21 Hn Hscratch Hzero.
  unfold EditScratchCountsBound in *.
  destruct Hscratch as [H10 [H11 [H20 H21]]].
  split; [exact H10|].
  split; [exact H11|].
  split.
  - eapply EditCountBounds_replace_zero_inc__zeroing_and_base_build; eauto.
  - exact H21.
Qed.

Lemma EditScratchCountsBound_replace_c21_zero_inc__manual :
  forall n c10 c11 c20 c21,
    1 <= n ->
    EditScratchCountsBound n c10 c11 c20 c21 ->
    EditZeroFull n c21 ->
    EditScratchCountsBound n c10 c11 c20 (replace_Znth 0 (Znth 0 c21 0 + 1) c21).
Proof.
  intros n c10 c11 c20 c21 Hn Hscratch Hzero.
  unfold EditScratchCountsBound in *.
  destruct Hscratch as [H10 [H11 [H20 H21]]].
  split; [exact H10|].
  split; [exact H11|].
  split; [exact H20|].
  eapply EditCountBounds_replace_zero_inc__zeroing_and_base_build; eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_14_1 : max_edit_string_matches_entail_wit_14_1.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
    try (eapply EditScratchCountsBound_replace_c20_zero_inc__manual; eauto; lia);
    try (eapply EditBuildState_initial_s1_zero__zeroing_and_base_build; eauto; lia).
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_14_2 : max_edit_string_matches_entail_wit_14_2.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
    try (eapply EditScratchCountsBound_replace_c21_zero_inc__manual; eauto; lia);
    try (eapply EditBuildState_initial_s1_one__zeroing_and_base_build; eauto; lia).
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_15 : max_edit_string_matches_entail_wit_15.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.seg seg2_pre 0 1 sg2_2).
    cancel (IntArray.undef_seg seg2_pre 1 n_pre).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try solve [intro Hbad; destruct Hbad; lia].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_1 : max_edit_string_matches_entail_wit_16_1_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). apply PreH19; assumption. Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_2 : max_edit_string_matches_entail_wit_16_1_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). apply PreH18; assumption. Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_3 : max_edit_string_matches_entail_wit_16_1_split_goal_3.
Proof. LLM_pre_process ltac:(int_auto). apply PreH17; assumption. Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_4 : max_edit_string_matches_entail_wit_16_1_split_goal_4.
Proof. LLM_pre_process ltac:(int_auto). apply PreH16; assumption. Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_5 : max_edit_string_matches_entail_wit_16_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [_ [_ [_ H21]]].
  destruct H21 as [_ Hcnt21].
  replace (i - 1 - 0) with (i - 1) by lia.
  assert (Hlast :
    Znth i (sg2_2 +:: Znth (i - 1) sg2_2 0) 0 =
    Znth (i - 1) sg2_2 0)
    by (change (sg2_2 +:: Znth (i - 1) sg2_2 0)
          with (sg2_2 ++ Znth (i - 1) sg2_2 0 :: nil);
        rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
        rewrite (proj1 Hseg);
        replace (i - i) with 0 by lia;
        reflexivity).
  rewrite Hlast.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       t2_l i sg2_2 Hseg ltac:(lia)).
  pose proof (Hcnt21 (Znth (i - 1) sg2_2 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_6 : max_edit_string_matches_entail_wit_16_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [_ [_ [_ H21]]].
  destruct H21 as [_ Hcnt21].
  replace (i - 1 - 0) with (i - 1) by lia.
  assert (Hlast :
    Znth i (sg2_2 +:: Znth (i - 1) sg2_2 0) 0 =
    Znth (i - 1) sg2_2 0)
    by (change (sg2_2 +:: Znth (i - 1) sg2_2 0)
          with (sg2_2 ++ Znth (i - 1) sg2_2 0 :: nil);
        rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
        rewrite (proj1 Hseg);
        replace (i - i) with 0 by lia;
        reflexivity).
  rewrite Hlast.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       t2_l i sg2_2 Hseg ltac:(lia)).
  pose proof (Hcnt21 (Znth (i - 1) sg2_2 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_7 : max_edit_string_matches_entail_wit_16_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [_ [_ [H20 _]]].
  destruct H20 as [_ Hcnt20].
  replace (i - 1 - 0) with (i - 1) by lia.
  assert (Hlast :
    Znth i (sg2_2 +:: Znth (i - 1) sg2_2 0) 0 =
    Znth (i - 1) sg2_2 0)
    by (change (sg2_2 +:: Znth (i - 1) sg2_2 0)
          with (sg2_2 ++ Znth (i - 1) sg2_2 0 :: nil);
        rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
        rewrite (proj1 Hseg);
        replace (i - i) with 0 by lia;
        reflexivity).
  rewrite Hlast.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       t2_l i sg2_2 Hseg ltac:(lia)).
  pose proof (Hcnt20 (Znth (i - 1) sg2_2 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_8 : max_edit_string_matches_entail_wit_16_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  destruct PreH15 as [_ [_ [H20 _]]].
  destruct H20 as [_ Hcnt20].
  replace (i - 1 - 0) with (i - 1) by lia.
  assert (Hlast :
    Znth i (sg2_2 +:: Znth (i - 1) sg2_2 0) 0 =
    Znth (i - 1) sg2_2 0)
    by (change (sg2_2 +:: Znth (i - 1) sg2_2 0)
          with (sg2_2 ++ Znth (i - 1) sg2_2 0 :: nil);
        rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
        rewrite (proj1 Hseg);
        replace (i - i) with 0 by lia;
        reflexivity).
  rewrite Hlast.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       t2_l i sg2_2 Hseg ltac:(lia)).
  pose proof (Hcnt20 (Znth (i - 1) sg2_2 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_9 : max_edit_string_matches_entail_wit_16_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  replace (i - 1 - 0) with (i - 1) by lia.
  assert (Hlast :
    Znth i (sg2_2 +:: Znth (i - 1) sg2_2 0) 0 =
    Znth (i - 1) sg2_2 0)
    by (change (sg2_2 +:: Znth (i - 1) sg2_2 0)
          with (sg2_2 ++ Znth (i - 1) sg2_2 0 :: nil);
        rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
        rewrite (proj1 Hseg);
        replace (i - i) with 0 by lia;
        reflexivity).
  rewrite Hlast.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       t2_l i sg2_2 Hseg ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_10 : max_edit_string_matches_entail_wit_16_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  replace (i - 1 - 0) with (i - 1) by lia.
  assert (Hlast :
    Znth i (sg2_2 +:: Znth (i - 1) sg2_2 0) 0 =
    Znth (i - 1) sg2_2 0)
    by (change (sg2_2 +:: Znth (i - 1) sg2_2 0)
          with (sg2_2 ++ Znth (i - 1) sg2_2 0 :: nil);
        rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
        rewrite (proj1 Hseg);
        replace (i - i) with 0 by lia;
        reflexivity).
  rewrite Hlast.
  pose proof
    (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
       t2_l i sg2_2 Hseg ltac:(lia)).
  lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_11 : max_edit_string_matches_entail_wit_16_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH14 as [_ [_ [_ [_ Hcounts]]]].
  exact Hcounts.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_12 : max_edit_string_matches_entail_wit_16_1_split_goal_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (i - 1 - 0) with (i - 1) by lia.
  destruct PreH14 as [_ [_ [_ [Hseg _]]]].
  eapply EditSegmentPrefix_extend_open__build_s1_segments_counts; eauto; try lia.
  unfold edit_edge_open; split; assumption.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_1 : max_edit_string_matches_entail_wit_16_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_4.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_5.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_6.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_7.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_8.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_9.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_10.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_11.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_16_1_split_goal_12.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_2 : max_edit_string_matches_entail_wit_16_2.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
    try solve [
      match goal with
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- 0 <= Znth ?pos (?sg +:: ?x) 0 =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg +:: x) 0 = x)
            by (unfold app at 1 in *;
                rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- Znth ?pos (?sg +:: ?x) 0 < ?n =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg +:: x) 0 = x)
            by (unfold app at 1 in *;
                rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- 0 <= Znth ?pos (?sg ++ ?x :: nil) 0 =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg ++ x :: nil) 0 = x)
            by (rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- Znth ?pos (?sg ++ ?x :: nil) 0 < ?n =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg ++ x :: nil) 0 = x)
            by (rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      end
    ];
    try solve [
      match goal with
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg ?c20 ?c21,
        Hscratch : EditScratchCountsBound ?n _ _ ?c20 ?c21 |- _ =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          match goal with
          | |- context [Znth ?pos (?sg0 ++ ?x :: nil) 0] =>
              assert (Hlast : Znth pos (sg0 ++ x :: nil) 0 = x)
                by (rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                    rewrite (proj1 Hseg);
                    replace (pos - i0) with 0 by lia;
                    reflexivity);
              rewrite Hlast
          end;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          try lia;
          unfold EditScratchCountsBound, EditCountBounds in Hscratch;
          destruct Hscratch as [_ [_ [[_ Hcnt20] [_ Hcnt21]]]];
          try (apply Hcnt20; lia);
          try (apply Hcnt21; lia);
          try lia
      end
    ];
    try solve [
      match goal with
      | Hbuild : EditBuildState _ _ _ _ _ _ _
          |- EditCountsForPrefix _ _ _ _ _ _ =>
          destruct Hbuild as [_ [_ [_ [_ Hcounts]]]];
          exact Hcounts
      end
    ];
    try solve [
      match goal with
      | Hbuild : EditBuildState _ ?t _ ?i ?sg _ _
          |- EditSegmentPrefix ?t (?i + 1)
               (?sg ++ Znth (?i - 1 - 0) ?sg 0 :: nil) =>
          replace (i - 1 - 0) with (i - 1) by lia;
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          eapply EditSegmentPrefix_extend_open__build_s1_segments_counts;
            eauto; try lia;
          unfold edit_edge_open; split; assumption
      | Hbuild : EditBuildState _ ?t _ ?i ?sg _ _
          |- EditSegmentPrefix ?t (?i + 1)
               (?sg ++ Znth (?i - 1) ?sg 0 :: nil) =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          eapply EditSegmentPrefix_extend_open__build_s1_segments_counts;
            eauto; try lia;
          unfold edit_edge_open; split; assumption
      | Hbuild : EditBuildState _ ?t _ ?i ?sg _ _
          |- EditSegmentPrefix ?t (?i + 1) (?sg ++ ?i :: nil) =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          eapply EditSegmentPrefix_extend_new__build_s1_segments_counts;
            eauto; try lia;
          unfold edit_edge_open; intros [Hprev Hcur]; contradiction
      end
    ].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_16_3 : max_edit_string_matches_entail_wit_16_3.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
    try solve [
      match goal with
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- 0 <= Znth ?pos (?sg +:: ?x) 0 =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg +:: x) 0 = x)
            by (unfold app at 1 in *;
                rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- Znth ?pos (?sg +:: ?x) 0 < ?n =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg +:: x) 0 = x)
            by (unfold app at 1 in *;
                rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- 0 <= Znth ?pos (?sg ++ ?x :: nil) 0 =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg ++ x :: nil) 0 = x)
            by (rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg _ _
          |- Znth ?pos (?sg ++ ?x :: nil) 0 < ?n =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          assert (Hlast : Znth pos (sg ++ x :: nil) 0 = x)
            by (rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                rewrite (proj1 Hseg);
                replace (pos - i0) with 0 by lia;
                reflexivity);
          rewrite Hlast;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          lia
      end
    ];
    try solve [
      match goal with
      | Hbuild : EditBuildState _ _ ?n ?i0 ?sg ?c20 ?c21,
        Hscratch : EditScratchCountsBound ?n _ _ ?c20 ?c21 |- _ =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          match goal with
          | |- context [Znth ?pos (?sg0 ++ ?x :: nil) 0] =>
              assert (Hlast : Znth pos (sg0 ++ x :: nil) 0 = x)
                by (rewrite app_Znth2 by (rewrite (proj1 Hseg); lia);
                    rewrite (proj1 Hseg);
                    replace (pos - i0) with 0 by lia;
                    reflexivity);
              rewrite Hlast
          end;
          try replace (i0 - 1 - 0) with (i0 - 1) by lia;
          try pose proof
            (EditSegmentPrefix_last_block_bounds__build_s1_segments_counts
               _ i0 sg Hseg ltac:(lia)) as Hblock_bounds;
          try lia;
          unfold EditScratchCountsBound, EditCountBounds in Hscratch;
          destruct Hscratch as [_ [_ [[_ Hcnt20] [_ Hcnt21]]]];
          try (apply Hcnt20; lia);
          try (apply Hcnt21; lia);
          try lia
      end
    ];
    try solve [
      match goal with
      | Hbuild : EditBuildState _ _ _ _ _ _ _
          |- EditCountsForPrefix _ _ _ _ _ _ =>
          destruct Hbuild as [_ [_ [_ [_ Hcounts]]]];
          exact Hcounts
      end
    ];
    try solve [
      match goal with
      | Hbuild : EditBuildState _ ?t _ ?i ?sg _ _
          |- EditSegmentPrefix ?t (?i + 1)
               (?sg ++ Znth (?i - 1 - 0) ?sg 0 :: nil) =>
          replace (i - 1 - 0) with (i - 1) by lia;
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          eapply EditSegmentPrefix_extend_open__build_s1_segments_counts;
            eauto; try lia;
          unfold edit_edge_open; split; assumption
      | Hbuild : EditBuildState _ ?t _ ?i ?sg _ _
          |- EditSegmentPrefix ?t (?i + 1)
               (?sg ++ Znth (?i - 1) ?sg 0 :: nil) =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          eapply EditSegmentPrefix_extend_open__build_s1_segments_counts;
            eauto; try lia;
          unfold edit_edge_open; split; assumption
      | Hbuild : EditBuildState _ ?t _ ?i ?sg _ _
          |- EditSegmentPrefix ?t (?i + 1) (?sg ++ ?i :: nil) =>
          destruct Hbuild as [_ [_ [_ [Hseg _]]]];
          eapply EditSegmentPrefix_extend_new__build_s1_segments_counts;
            eauto; try lia;
          unfold edit_edge_open; intros [Hprev Hcur]; contradiction
      end
    ].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_17 : max_edit_string_matches_entail_wit_17.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists c20_2 c21_2 sg1_2 c10_2 c11_2 sg2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.seg seg2_pre 0 (i + 1) sg2).
    cancel (IntArray.undef_seg seg2_pre (i + 1) n_pre).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia;
      try (replace (i - 0) with i by lia; auto).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_18_1 : max_edit_string_matches_entail_wit_18_1.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
    try solve [
      eapply (edit_scratch_bound_update_zero__build_s2_segments_counts
        s2_l t2_l n_pre i sg2_2 c10_2 c11_2 c20_2 c21_2 block2);
      eauto; lia
    ];
    try solve [
      eapply (EditBuildState_extend_zero__build_s1_segments_counts
        s2_l t2_l n_pre i sg2_2 c20_2 c21_2 block2);
      eauto; lia
    ].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_18_2 : max_edit_string_matches_entail_wit_18_2.
Proof.
  right. intros.
  assert (Hs2bit_one : Znth i s2_l 0 = 1).
  {
    pose proof (PreH23 i ltac:(lia)) as Hs2bit_bound.
    lia.
  }
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
    try solve [
      eapply (edit_scratch_bound_update_one__build_s2_segments_counts
        s2_l t2_l n_pre i sg2_2 c10_2 c11_2 c20_2 c21_2 block2);
      eauto; lia
    ];
    try solve [
      eapply (EditBuildState_extend_one__build_s1_segments_counts
        s2_l t2_l n_pre i sg2_2 c20_2 c21_2 block2);
      eauto; lia
    ].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_19 : max_edit_string_matches_entail_wit_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.seg seg2_pre 0 (i + 1) sg2_2).
    cancel (IntArray.undef_seg seg2_pre (i + 1) n_pre).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_20 : max_edit_string_matches_entail_wit_20.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace i with n_pre in * by lia.
  Exists sg2_2 c20_2 c21_2 sg1_2 c10_2 c11_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full seg2_pre 0 n_pre sg2_2).
    replace (seg2_pre + 0 * sizeof (INT)) with seg2_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_21 : max_edit_string_matches_entail_wit_21.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  eapply edit_greedy_prefix_state_start__greedy_common_and_mismatch_steps; eauto.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_22 : max_edit_string_matches_entail_wit_22.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_23 : max_edit_string_matches_entail_wit_23.
Proof.
  right.
  intros.
  pose proof (edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    s1_l s2_l t1_l t2_l n_pre i ans sg1 sg2
    c10_2 c11_2 c20_2 c21_2 PreH13 ltac:(lia))
    as [Hsg1 [Hsg2 [Hc10 [Hc11 [Hc20 Hc21]]]]].
  pose proof (edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps
    s1_l s2_l t1_l t2_l n_pre i ans sg1 sg2
    c10_2 c11_2 c20_2 c21_2 PreH13)
    as Havail.
  specialize (Havail ltac:(lia)).
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  unfold EditGreedyCurrentAvailability. intros _. exact Havail.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_24 : max_edit_string_matches_entail_wit_24.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  eapply edit_greedy_common_zero_step__greedy_common_and_mismatch_steps; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_25_1 : max_edit_string_matches_entail_wit_25_1.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  eapply edit_greedy_common_one_step__greedy_common_and_mismatch_steps; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_25_2 : max_edit_string_matches_entail_wit_25_2.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  eapply edit_greedy_common_one_step__greedy_common_and_mismatch_steps; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_27 : max_edit_string_matches_entail_wit_27.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  eapply edit_greedy_s1_zero_s2_one_step__greedy_common_and_mismatch_steps; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_29 : max_edit_string_matches_entail_wit_29.
Proof.
  right. intros. LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  eapply edit_greedy_s1_one_s2_zero_step__greedy_common_and_mismatch_steps; eauto; lia.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_30_1 : max_edit_string_matches_entail_wit_30_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH14 as Hstate.
  unfold EditGreedyPrefixState in PreH14.
  destruct PreH14 as [_ [_ [full10 [full11 [full20 [full21 [Hbuild1 [Hbuild2 _]]]]]]]].
  unfold EditBuildState in Hbuild1, Hbuild2.
  destruct Hbuild1 as [_ [Hs1 [Ht1 _]]].
  destruct Hbuild2 as [_ [Hs2 [Ht2 _]]].
  unfold EditBinaryList in Hs1, Hs2, Ht1, Ht2.
  destruct Hs1 as [HLs1 HBs1].
  destruct Hs2 as [HLs2 HBs2].
  destruct Ht1 as [HLt1 HBt1].
  destruct Ht2 as [HLt2 HBt2].
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try solve [intros idx Hidx; specialize (HBt2 idx Hidx);
      destruct HBt2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBt1 idx Hidx);
      destruct HBt1 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs2 idx Hidx);
      destruct HBs2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs1 idx Hidx);
      destruct HBs1 as [Hbit | Hbit]; rewrite Hbit; lia].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_30_2 : max_edit_string_matches_entail_wit_30_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH14 as Hstate.
  unfold EditGreedyPrefixState in PreH14.
  destruct PreH14 as [_ [_ [full10 [full11 [full20 [full21 [Hbuild1 [Hbuild2 _]]]]]]]].
  unfold EditBuildState in Hbuild1, Hbuild2.
  destruct Hbuild1 as [_ [Hs1 [Ht1 _]]].
  destruct Hbuild2 as [_ [Hs2 [Ht2 _]]].
  unfold EditBinaryList in Hs1, Hs2, Ht1, Ht2.
  destruct Hs1 as [HLs1 HBs1].
  destruct Hs2 as [HLs2 HBs2].
  destruct Ht1 as [HLt1 HBt1].
  destruct Ht2 as [HLt2 HBt2].
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try solve [intros idx Hidx; specialize (HBt2 idx Hidx);
      destruct HBt2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBt1 idx Hidx);
      destruct HBt1 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs2 idx Hidx);
      destruct HBs2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs1 idx Hidx);
      destruct HBs1 as [Hbit | Hbit]; rewrite Hbit; lia].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_30_3 : max_edit_string_matches_entail_wit_30_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH14 as Hstate.
  unfold EditGreedyPrefixState in PreH14.
  destruct PreH14 as [_ [_ [full10 [full11 [full20 [full21 [Hbuild1 [Hbuild2 _]]]]]]]].
  unfold EditBuildState in Hbuild1, Hbuild2.
  destruct Hbuild1 as [_ [Hs1 [Ht1 _]]].
  destruct Hbuild2 as [_ [Hs2 [Ht2 _]]].
  unfold EditBinaryList in Hs1, Hs2, Ht1, Ht2.
  destruct Hs1 as [HLs1 HBs1].
  destruct Hs2 as [HLs2 HBs2].
  destruct Ht1 as [HLt1 HBt1].
  destruct Ht2 as [HLt2 HBt2].
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try solve [intros idx Hidx; specialize (HBt2 idx Hidx);
      destruct HBt2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBt1 idx Hidx);
      destruct HBt1 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs2 idx Hidx);
      destruct HBs2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs1 idx Hidx);
      destruct HBs1 as [Hbit | Hbit]; rewrite Hbit; lia].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_30_4 : max_edit_string_matches_entail_wit_30_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH14 as Hstate.
  unfold EditGreedyPrefixState in PreH14.
  destruct PreH14 as [_ [_ [full10 [full11 [full20 [full21 [Hbuild1 [Hbuild2 _]]]]]]]].
  unfold EditBuildState in Hbuild1, Hbuild2.
  destruct Hbuild1 as [_ [Hs1 [Ht1 _]]].
  destruct Hbuild2 as [_ [Hs2 [Ht2 _]]].
  unfold EditBinaryList in Hs1, Hs2, Ht1, Ht2.
  destruct Hs1 as [HLs1 HBs1].
  destruct Hs2 as [HLs2 HBs2].
  destruct Ht1 as [HLt1 HBt1].
  destruct Ht2 as [HLt2 HBt2].
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try solve [intros idx Hidx; specialize (HBt2 idx Hidx);
      destruct HBt2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBt1 idx Hidx);
      destruct HBt1 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs2 idx Hidx);
      destruct HBs2 as [Hbit | Hbit]; rewrite Hbit; lia].
    all: try solve [intros idx Hidx; specialize (HBs1 idx Hidx);
      destruct HBs1 as [Hbit | Hbit]; rewrite Hbit; lia].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_31 : max_edit_string_matches_entail_wit_31.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  pose proof PreH13 as Hstate.
  pose proof
    (EditGreedyPrefixState_completed_state_facts
       s1_l s2_l t1_l t2_l n_pre ans
       sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH12 Hstate)
    as Hfacts.
  pose proof
    (EditGreedyCompletedStateFacts_to_Maximum
       s1_l s2_l t1_l t2_l n_pre ans
       sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 Hfacts)
    as Hmax.
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hmax.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_32 : max_edit_string_matches_entail_wit_32.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (EditGreedyCompletedStateFacts_to_Maximum
       s1_l s2_l t1_l t2_l n_pre ans
       sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 PreH7)
    as Hmax.
  Exists sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2.
  split_pure_spatial.
  - cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    cancel (IntArray.full t2_pre n_pre t2_l).
    cancel (IntArray.full seg1_pre n_pre sg1_2).
    cancel (IntArray.full seg2_pre n_pre sg2_2).
    cancel (IntArray.full cnt10_pre n_pre c10_2).
    cancel (IntArray.full cnt11_pre n_pre c11_2).
    cancel (IntArray.full cnt20_pre n_pre c20_2).
    cancel (IntArray.full cnt21_pre n_pre c21_2).
  - split_pures; dump_pre_spatial; auto; try lia; try exact Hmax.
Qed.
