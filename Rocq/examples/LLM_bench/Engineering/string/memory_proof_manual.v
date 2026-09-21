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
From SimpleC.EE.LLM_bench.Engineering.string Require Import memory_goal.
From SimpleC.EE.LLM_bench.Engineering.string Require Import memory_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_memcpy_entail_wit_1 : memcpy_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg dest_pre n_pre).
  change (sublist 0 0 bytes) with (@nil Z).
  rewrite (CharArray.full_empty dest_pre 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg dest_pre 0 n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memcpy_entail_wit_2 : memcpy_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (sublist 0 (i + 1) bytes)
    with (sublist 0 i bytes ++ Znth i bytes 0 :: nil).
  2: {
    rewrite (sublist_split 0 (i + 1) i bytes) by lia.
    rewrite (sublist_single 0 i bytes) by lia.
    reflexivity.
  }
  split_pure_spatial.
  - cancel (CharArray.full dest_pre (i + 1)
      (sublist 0 i bytes ++ Znth i bytes 0 :: nil)).
    cancel (CharArray.undef_seg dest_pre (i + 1) n_pre).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memcpy_return_wit_1 : memcpy_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (HlenZ : Zlength bytes = n_pre) by lia.
  rewrite (sublist_self bytes n_pre) by exact (eq_sym HlenZ).
  rewrite (CharArray.undef_seg_empty dest_pre n_pre).
  split_pure_spatial.
  - cancel (CharArray.full dest_pre n_pre bytes).
    cancel (CharArray.full src_pre n_pre bytes).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_memmove_entail_wit_1_1_split_goal_spatial : memmove_entail_wit_1_1_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_1_1_split_goal_spatial; intros.
  assert (Hs : src0 = base + source) by lia. rewrite Hs, char_buffer_seg_view.
  rewrite memmove_content_zero by lia. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_1_1 : memmove_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_1_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_1_2_split_goal_1 : memmove_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_memmove_entail_wit_1_2_split_goal_spatial : memmove_entail_wit_1_2_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_1_2_split_goal_spatial; intros.
  subst dest_pre src_pre n_pre. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_1_2 : memmove_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_1_2_split_goal_1 | Goal_apply proof_of_memmove_entail_wit_1_2_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_2_1_split_goal_1 : memmove_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial. replace (i - -source) with (source + i) by lia.
  apply memmove_content_outside; lia.
Qed.

Lemma proof_of_memmove_entail_wit_2_1_split_goal_spatial : memmove_entail_wit_2_1_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_2_1_split_goal_spatial; intros.
  try subst src0; try subst dest0.
  rewrite !char_buffer_seg_view.
  apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_2_1 : memmove_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_2_1_split_goal_1 | Goal_apply proof_of_memmove_entail_wit_2_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_3_1_split_goal_spatial : memmove_entail_wit_3_1_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_3_1_split_goal_spatial; intros.
  try subst src0; try subst dest0.
  rewrite !char_buffer_seg_view.
  subst value. rewrite ascii_Znth_cast by (assumption || lia).
  replace (i - -destination) with (destination + i) by lia.
  pose proof (memmove_content_forward_step memory source destination i
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hstep.
  rewrite memmove_content_outside in Hstep by lia.
  rewrite Hstep. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_3_1 : memmove_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_3_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_3_2_split_goal_1 : memmove_entail_wit_3_2_split_goal_1.
Proof.
  unfold memmove_entail_wit_3_2_split_goal_1; intros.
  subst value. rewrite ascii_Znth_cast by (assumption || lia).
  rewrite (sublist_split 0 (i + 1) i bytes) by lia.
  rewrite (sublist_single 0 i bytes) by lia. reflexivity.
Qed.

Lemma proof_of_memmove_entail_wit_3_2 : memmove_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_3_2_split_goal_1].
Qed.

Lemma proof_of_memmove_entail_wit_4_1_split_goal_spatial : memmove_entail_wit_4_1_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_4_1_split_goal_spatial; intros.
  subst n_pre.
  assert (Hs : src0 = base + source) by lia. rewrite Hs, char_buffer_seg_view.
  replace (n0 - n0) with 0 by lia. rewrite memmove_content_zero by lia.
  apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_4_1 : memmove_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_4_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_4_2_split_goal_1 : memmove_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial. apply Zsublist_nil; lia.
Qed.

Lemma proof_of_memmove_entail_wit_4_2_split_goal_spatial : memmove_entail_wit_4_2_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_4_2_split_goal_spatial; intros.
  subst dest_pre src_pre n_pre. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_4_2 : memmove_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_4_2_split_goal_1 | Goal_apply proof_of_memmove_entail_wit_4_2_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_5_1_split_goal_1 : memmove_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial. replace (i - 1 - -source) with (source + (i - 1)) by lia.
  apply memmove_content_outside; lia.
Qed.

Lemma proof_of_memmove_entail_wit_5_1_split_goal_spatial : memmove_entail_wit_5_1_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_5_1_split_goal_spatial; intros.
  try subst src0; try subst dest0.
  rewrite !char_buffer_seg_view.
  replace (i - 1 + 1) with i by lia. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_5_1 : memmove_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_5_1_split_goal_1 | Goal_apply proof_of_memmove_entail_wit_5_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_5_2_split_goal_spatial : memmove_entail_wit_5_2_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_5_2_split_goal_spatial; intros.
  replace (i - 1 + 1) with i by lia.
  unfold CharArray.undef_full, CharArray.undef_seg, store_undef_array.
  rewrite Z.sub_0_r. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_5_2 : memmove_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_5_2_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_6_1_split_goal_spatial : memmove_entail_wit_6_1_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_6_1_split_goal_spatial; intros.
  try subst src0; try subst dest0.
  rewrite !char_buffer_seg_view.
  subst value. rewrite ascii_Znth_cast by (assumption || lia).
  replace (i - -destination) with (destination + i) by lia.
  pose proof (memmove_content_backward_step memory source destination n0 (i + 1)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hstep.
  rewrite memmove_content_outside in Hstep by lia.
  replace (i + 1 - 1) with i in Hstep by lia.
  rewrite Hstep. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_entail_wit_6_1 : memmove_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_6_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_entail_wit_6_2_split_goal_spatial : memmove_entail_wit_6_2_split_goal_spatial.
Proof.
  unfold memmove_entail_wit_6_2_split_goal_spatial; intros.
  subst value. rewrite ascii_Znth_cast by (assumption || lia).
  rewrite (sublist_split i n0 (i + 1) bytes) by lia.
  rewrite (sublist_single 0 i bytes) by lia. cbn [app].
  rewrite CharArray.full_unfold, CharArray.seg_0_shift.
  unfold CharArray.undef_full, CharArray.undef_seg, store_undef_array.
  rewrite Z.sub_0_r.
  replace (dest0 + i * sizeof(CHAR) + 1 * sizeof(CHAR)) with
    (dest0 + (i + 1) * sizeof(CHAR)) by lia.
  replace (n0 - i - 1) with (n0 - (i + 1)) by lia.
  unfold CharArray.full, CharArray.seg, store_array. repeat cancel.
  all: try (replace (dest0 + i * sizeof(CHAR) + 0 * sizeof(CHAR)) with
    (dest0 + i * sizeof(CHAR)) by lia).
  all: entailer!.
Qed.

Lemma proof_of_memmove_entail_wit_6_2 : memmove_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_entail_wit_6_2_split_goal_spatial].
Qed.

Lemma proof_of_memmove_return_wit_1_split_goal_spatial : memmove_return_wit_1_split_goal_spatial.
Proof.
  unfold memmove_return_wit_1_split_goal_spatial; intros.
  subst src0. rewrite char_buffer_seg_view.
  replace i with n0 by lia. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_return_wit_1_split_goal_spatial].
Qed.

Lemma proof_of_memmove_return_wit_2_split_goal_spatial : memmove_return_wit_2_split_goal_spatial.
Proof.
  unfold memmove_return_wit_2_split_goal_spatial; intros.
  replace i with n0 by lia. rewrite sublist_self by lia. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_return_wit_2_split_goal_spatial].
Qed.

Lemma proof_of_memmove_return_wit_3_split_goal_spatial : memmove_return_wit_3_split_goal_spatial.
Proof.
  unfold memmove_return_wit_3_split_goal_spatial; intros.
  subst src0. rewrite char_buffer_seg_view.
  replace i with 0 by lia. rewrite !Z.add_0_r, Z.sub_0_r. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_return_wit_3 : memmove_return_wit_3.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_return_wit_3_split_goal_spatial].
Qed.

Lemma proof_of_memmove_return_wit_4_split_goal_spatial : memmove_return_wit_4_split_goal_spatial.
Proof.
  unfold memmove_return_wit_4_split_goal_spatial; intros.
  replace i with 0 by lia. rewrite sublist_self by lia.
  replace (dest0 + 0 * sizeof(CHAR)) with dest0 by lia.
  rewrite Z.sub_0_r. apply derivable1_refl.
Qed.

Lemma proof_of_memmove_return_wit_4 : memmove_return_wit_4.
Proof.
  aggressive_pre_process.
  all: first [Goal_apply proof_of_memmove_return_wit_4_split_goal_spatial].
Qed.

Lemma proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg s_pre n_pre).
  unfold repeat_Z.
  simpl.
  rewrite (CharArray.full_empty s_pre 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg s_pre 0 n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite repeat_Z_tail.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (i + 1) (repeat_Z c_pre i ++ c_pre :: nil)).
    cancel (CharArray.undef_seg s_pre (i + 1) n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
  - lia.
Qed.

Lemma proof_of_memset_return_wit_1 : memset_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  rewrite (CharArray.undef_seg_empty s_pre n_pre).
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre (repeat_Z c_pre n_pre)).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.
