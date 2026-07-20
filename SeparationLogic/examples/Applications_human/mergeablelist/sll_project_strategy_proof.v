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
  unfold sll.
  entailer!.
Qed.

Lemma sll_project_strategy4_correctness : sll_project_strategy4.
Proof.  
  pre_process_default.
  unfold sll.
  entailer!.
Qed.

Lemma sll_project_strategy5_correctness : sll_project_strategy5.
Proof.
  pre_process_default.
  entailer!.
  subst l.
  unfold sll.
  entailer!.
Qed.

Lemma sll_project_strategy6_correctness : sll_project_strategy6.
Proof.
  pre_process_default.
  sep_apply (sll_zero 0 l).
  + reflexivity.
  + entailer!.
Qed.

Lemma sll_project_strategy14_correctness : sll_project_strategy14.
Proof.
  pre_process_default.
  entailer!.
  subst l.
  unfold sllseg.
  entailer!.
Qed.

Lemma sll_project_strategy31_correctness : sll_project_strategy31.
Proof.
  pre_process_default.
Qed.


Lemma sll_project_strategy20_correctness : sll_project_strategy20.
Proof.
  pre_process_default.
  entailer!.
  subst l.
  unfold sllbseg.
  entailer!.
Qed.

Lemma sll_project_strategy40_correctness : sll_project_strategy40.
  pre_process_default.
Qed.

Lemma sll_project_strategy41_correctness : sll_project_strategy41.
  pre_process_default.
Qed.

Lemma sll_project_strategy42_correctness : sll_project_strategy42.
  pre_process_default.
  entailer!.
  subst l.
  simpl.
  entailer!.
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
  entailer!.
  rewrite <- H.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma sll_project_strategy61_correctness : sll_project_strategy61.
Proof.
  pre_process_default.
  entailer!.
  inversion H.
  reflexivity.
  inversion H.
  reflexivity.
Qed.

(* sllb_sll strategies *)

Lemma sll_project_strategy37_correctness : sll_project_strategy37.
Proof.
  pre_process_default.
  unfold sllb_sll.
  Exists h.
  entailer!.
Qed.

Lemma sll_project_strategy7_correctness : sll_project_strategy7.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma sll_project_strategy16_correctness : sll_project_strategy16.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma sll_project_strategy30_correctness : sll_project_strategy30.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma sll_project_strategy22_correctness : sll_project_strategy22.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma sll_project_strategy38_correctness : sll_project_strategy38.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma sll_project_strategy72_correctness : sll_project_strategy72.
Proof.
  pre_process_default.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg p x (x + 1) y).
  entailer!.
  pose proof (UIntArray.undef_seg_unfold p x (x + 1)) as H_unfold.
  assert (H_ineq: x < x + 1) by lia.
  specialize (H_unfold H_ineq).
  destruct H_unfold as [H_LtoR _].
  sep_apply H_LtoR.
  unfold UIntArray.undef_seg.
  replace (x + 1 - (x + 1)) with 0 by lia.
  simpl.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  lia.
Qed.

Lemma sll_project_strategy73_correctness : sll_project_strategy73.
Proof.
  pre_process_default.
  unfold UIntArray.undef_full.
  unfold UIntArray.undef_seg.
  replace (n - 0) with n by lia.
  replace (p + 0 * sizeof (UINT)) with p.
  2: { 
    rewrite Z.mul_0_l. rewrite Z.add_0_r. reflexivity.
  }
  entailer!.
Qed.

Lemma sll_project_strategy74_correctness : sll_project_strategy74.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  unfold UIntArray.undef_full.
  unfold store_undef_array.
  simpl.
  entailer!.
Qed.

Lemma sll_project_strategy75_correctness : sll_project_strategy75.
Proof.
  pre_process_default.
  unfold UIntArray.undef_seg.
  replace (y - x) with 0 by lia.
  simpl.
  entailer!.
Qed.

Lemma sll_project_strategy76_correctness : sll_project_strategy76.
Proof.
  pre_process_default.
  unfold UIntArray.undef_seg.
  replace (x - x) with 0 by lia.
  simpl.
  entailer!.
Qed.

Lemma sll_project_strategy77_correctness : sll_project_strategy77.
Proof.
  pre_process_default.
  rewrite H, H0.
  entailer!.
Qed.

Lemma sll_project_strategy78_correctness : sll_project_strategy78.
Proof.
  pre_process_default.
  unfold UIntArray.undef_full.
  pose proof (UIntArray.undef_seg_unfold p 0 n) as H_unfold.
  assert (H_cond: 0 < n) by lia.
  specialize (H_unfold H_cond).
  destruct H_unfold as [H_LtoR _].
  unfold UIntArray.undef_seg in H_LtoR.
  unfold store_undef_array.
  unfold UIntArray.undef_seg.
  simpl in H_LtoR.
  replace (n - 0) with n in H_LtoR by lia.
  sep_apply H_LtoR.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_project_strategy80_correctness : sll_project_strategy80.
Proof.
  pre_process_default.
  rewrite H.
  entailer!.
Qed.

Lemma sll_project_strategy85_correctness : sll_project_strategy85.
Proof.
  pre_process_default.
  rewrite <- H.
  unfold UIntArray.seg_shape.
  replace (x - x) with 0 by lia.
  simpl. 
  entailer!.
Qed.

Lemma sll_project_strategy86_correctness : sll_project_strategy86.
Proof.
  pre_process_default.
  rewrite <- H.
  unfold UIntArray.seg_shape.
  replace (x - x) with 0 by lia.
  simpl. 
  entailer!.
Qed.

Lemma sll_project_strategy87_correctness : sll_project_strategy87.
Proof.
  pre_process_default.
  rewrite H.
  unfold UIntArray.seg_shape.
  entailer!.
Qed.

Lemma sll_project_strategy90_correctness : sll_project_strategy90.
Proof.
  pre_process_default.
Qed.

Lemma sll_project_strategy91_correctness : sll_project_strategy91.
Proof.
  pre_process_default.
  unfold UIntArray.seg_shape.
  simpl.
  entailer!.
Qed.

Lemma sll_project_strategy92_correctness : sll_project_strategy92.
Proof.
  pre_process_default.
  rewrite H.
  unfold UIntArray.seg_shape, UIntArray.full_shape.
  unfold store_undef_array.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma sll_project_strategy93_correctness : sll_project_strategy93.
Proof.
  pre_process_default.
  rewrite H.
  unfold UIntArray.full_shape.
  unfold store_undef_array.
  simpl.
  entailer!.
Qed.

Lemma sll_project_strategy71_correctness : sll_project_strategy71.
Proof.
  pre_process_default.
  unfold UIntArray.undef_full.
  assert (H_merge: (p + i * sizeof ( UINT )) # UInt |->_ ** UIntArray.undef_missing_i p i 0 n 
          |-- UIntArray.undef_seg p 0 n).
  {
    apply UIntArray.undef_missing_i_merge_to_undef_seg.
    lia.
  }
  sep_apply H_merge.
  unfold UIntArray.undef_seg.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma sll_project_strategy32_correctness : sll_project_strategy32.
Proof.
  pre_process_default.
  sep_apply (sllb_2_sll p l).
  Intros h_val pt_val.
  Exists h_val pt_val.
  entailer!.
  apply derivable1s_wand_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

(* sllb_sll unfold left - strategy 35 *)
Lemma sll_project_strategy35_correctness : sll_project_strategy35.
Proof.
  pre_process_default.
  unfold sllb_sll.
  Intros h.
  Exists h.
  entailer!.
  apply derivable1s_wand_sepcon_adjoint.
  elim_emp.
  reflexivity.
Qed.

(* sllb_sll unfold right - strategy 36 *)
Lemma sll_project_strategy36_correctness : sll_project_strategy36.
Proof.
  pre_process_default.
  entailer!.
  unfold sllb_sll.
  Exists h.
  entailer!.
Qed.

Lemma sll_project_strategy70_correctness : sll_project_strategy70.
Proof.
  pre_process_default.
  assert (H_to_seg: UIntArray.undef_full p n |-- UIntArray.undef_seg p 0 n).
  {
    unfold UIntArray.undef_full, UIntArray.undef_seg.
    replace (n - 0) with n by lia.
    replace (p + 0 * sizeof (UINT)) with p.
    - entailer!. 
    - rewrite Z.mul_0_l, Z.add_0_r. reflexivity.
  }

  sep_apply H_to_seg.
  clear H_to_seg.
  sep_apply (UIntArray.undef_seg_split_to_undef_missing_i p 0 i n).
  - entailer!.
    apply derivable1_wand_sepcon_adjoint.
    entailer!.
  - lia.
Qed.
