Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_strategy_goal.
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_project_strategy3_correctness : sll_project_strategy3.
Proof.
  pre_process_default.
  simpl.
  split_pure_spatial.
  - Intros_p H.
    cancel.
  - Intros_p H.
    dump_pre_spatial.
    exact H.
Qed.

Lemma sll_project_strategy4_correctness : sll_project_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst p.
  simpl.
  cancel.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_project_strategy5_correctness : sll_project_strategy5.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_project_strategy6_correctness : sll_project_strategy6.
Proof.
  pre_process_default.
  sep_apply_l_atomic (sll_zero 0 l eq_refl).
  Intros_p H.
  subst l.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_project_strategy14_correctness : sll_project_strategy14.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_project_strategy31_correctness : sll_project_strategy31.
Proof.
  pre_process_default.
Qed.


Lemma sll_project_strategy20_correctness : sll_project_strategy20.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_project_strategy40_correctness : sll_project_strategy40.
  pre_process_default.
Qed.

Lemma sll_project_strategy41_correctness : sll_project_strategy41.
  pre_process_default.
Qed.

Lemma sll_project_strategy42_correctness : sll_project_strategy42.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_project_strategy50_correctness : sll_project_strategy50.
Proof.
  pre_process_default.
Qed.

Lemma sll_project_strategy51_correctness : sll_project_strategy51.
Proof.
  pre_process_default.
Qed.

Lemma sll_project_strategy52_correctness : sll_project_strategy52.
Proof.  
  pre_process_default.
Qed.

Lemma sll_project_strategy60_correctness : sll_project_strategy60.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    rewrite <- H, <- H0.
    reflexivity.
Qed.

Lemma sll_project_strategy61_correctness : sll_project_strategy61.
Proof.
  pre_process_default.
  inversion H; subst.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; reflexivity.
Qed.

(* sllb_sll strategies *)

Lemma sll_project_strategy37_correctness : sll_project_strategy37.
Proof.
  pre_process_default.
  unfold sllb_sll.
  Exists h.
  normalize.
  split_pure_spatial.
  - cancel. cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma sll_project_strategy7_correctness : sll_project_strategy7.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_project_strategy16_correctness : sll_project_strategy16.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_project_strategy30_correctness : sll_project_strategy30.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_project_strategy22_correctness : sll_project_strategy22.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_project_strategy38_correctness : sll_project_strategy38.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_project_strategy72_correctness : sll_project_strategy72.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (UIntArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + replace (p + x * 4) with (p + x * sizeof (UINT))
        by (rewrite sizeof_uint; lia).
      cancel (UIntArray.undef_seg p (x + 1) y).
      apply_sepcon_adjoint.
      normalize.
      cancel.
Qed.

Lemma sll_project_strategy73_correctness : sll_project_strategy73.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg p n).
  cancel.
Qed.

Lemma sll_project_strategy74_correctness : sll_project_strategy74.
Proof.
  pre_process_default.
  subst n.
  rewrite UIntArray.undef_full_empty.
  cancel.
Qed.

Lemma sll_project_strategy75_correctness : sll_project_strategy75.
Proof.
  pre_process_default.
  subst y.
  rewrite UIntArray.undef_seg_empty.
  cancel.
Qed.

Lemma sll_project_strategy76_correctness : sll_project_strategy76.
Proof.
  pre_process_default.
  apply UIntArray.undef_seg_empty.
Qed.

Lemma sll_project_strategy77_correctness : sll_project_strategy77.
Proof.
  pre_process_default.
  subst x1 y1.
  cancel.
Qed.

Lemma sll_project_strategy78_correctness : sll_project_strategy78.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (UIntArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + cancel (UIntArray.undef_seg p 1 n).
      apply_sepcon_adjoint.
      cancel.
      replace (p + 0 * sizeof (UINT)) with (p + 0) by lia.
      cancel.
      normalize.
      cancel.
Qed.

Lemma sll_project_strategy80_correctness : sll_project_strategy80.
Proof.
  pre_process_default.
  subst m.
  rewrite Zlength_nil.
  cancel.
Qed.

Lemma sll_project_strategy85_correctness : sll_project_strategy85.
Proof.
  pre_process_default.
  subst y.
  rewrite (UIntArray.seg_shape_empty p x).
  cancel.
Qed.

Lemma sll_project_strategy86_correctness : sll_project_strategy86.
Proof.
  pre_process_default.
  subst y.
  rewrite (UIntArray.seg_shape_empty p x).
  cancel.
Qed.

Lemma sll_project_strategy87_correctness : sll_project_strategy87.
Proof.
  pre_process_default.
  subst y1.
  cancel.
Qed.

Lemma sll_project_strategy90_correctness : sll_project_strategy90.
Proof.
  pre_process_default.
Qed.

Lemma sll_project_strategy91_correctness : sll_project_strategy91.
Proof.
  pre_process_default.
  rewrite Zlength_nil.
  rewrite UIntArray.seg_shape_empty.
  cancel.
Qed.

Lemma sll_project_strategy92_correctness : sll_project_strategy92.
Proof.
  pre_process_default.
  subst i.
  sep_apply UIntArray.seg_shape_to_full_shape.
  replace (n - 0) with n by lia.
  replace (p + 0 * sizeof (UINT)) with p by lia.
  cancel.
Qed.

Lemma sll_project_strategy93_correctness : sll_project_strategy93.
Proof.
  pre_process_default.
  subst n.
  rewrite UIntArray.full_shape_empty.
  cancel.
Qed.

Lemma sll_project_strategy71_correctness : sll_project_strategy71.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.undef_missing_i_merge_to_undef_full p i n).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma sll_project_strategy32_correctness : sll_project_strategy32.
Proof.
  pre_process_default.
  sep_apply (sllb_2_sll p l).
  Intros h_val pt_val.
  Exists h_val pt_val.
  normalize.
  split_pure_spatial.
  - cancel (sll h_val l).
    cancel (&( p # "sllb" ->ₛ "head") # Ptr |-> h_val).
    cancel.
    wand_elim.
    cancel.
  - dump_pre_spatial.
    exact H.
Qed.

(* sllb_sll unfold left - strategy 35 *)
Lemma sll_project_strategy35_correctness : sll_project_strategy35.
Proof.
  pre_process_default.
  unfold sllb_sll.
  Intros h.
  Exists h.
  normalize.
  split_pure_spatial.
  - cancel (sll h l).
    cancel (&( p # "sllb" ->ₛ "head") # Ptr |-> h).
    cancel.
    wand_elim.
    cancel.
  - dump_pre_spatial.
    exact H.
Qed.

(* sllb_sll unfold right - strategy 36 *)
Lemma sll_project_strategy36_correctness : sll_project_strategy36.
Proof.
  pre_process_default.
  unfold sllb_sll.
  Exists h.
  Intros_p H.
  split_pure_spatial.
  - cancel. cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma sll_project_strategy70_correctness : sll_project_strategy70.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_missing_i p i n).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 4) with (p + i * sizeof (UINT))
      by (rewrite sizeof_uint; lia).
    cancel (UIntArray.undef_missing_i p i 0 n).
    apply_sepcon_adjoint.
    normalize.
    cancel.
Qed.
