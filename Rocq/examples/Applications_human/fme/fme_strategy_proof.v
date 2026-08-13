Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.EE.Applications_human.fme Require Import fme_lib.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme Require Import fme_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.fme Require Import fme_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma fme_strategy5_correctness : fme_strategy5.
  pre_process_default.
  entailer!.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma fme_strategy6_correctness : fme_strategy6.
  pre_process_default.
  entailer!.
  rewrite H, H0, H1.
  entailer!.
Qed.

Lemma fme_strategy18_correctness : fme_strategy18.
  pre_process_default.
  entailer!.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma fme_strategy19_correctness : fme_strategy19.
  pre_process_default.
  entailer!.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma fme_strategy7_correctness : fme_strategy7.
  pre_process_default.
  Intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma fme_strategy13_correctness : fme_strategy13.
  pre_process_default.
  Intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma fme_strategy15_correctness : fme_strategy15.
  pre_process_default.
  simpl.
  unfold coef_array.
  unfold coef_array_missing_i_rec.
  Split ; Intros; try lia.
  - subst. unfold NULL in H1. lia. 
  - sep_apply (IntArray.full_split_to_missing_i p i n (Constraint_list l) 0) ; try lia.
    entailer!. 
    Intros_r v.
    pre_process_default. Intros.
    subst.
    entailer!.
Qed.

Lemma fme_strategy16_correctness : fme_strategy16.
  pre_process_default.
  unfold coef_array.
  unfold coef_array_missing_i_rec.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply IntArray.missing_i_merge_to_full; try lia.
  unfold coef_Znth.
  rewrite replace_Znth_Znth by tauto.
  Right.
  entailer!.
Qed.

Lemma fme_strategy8_correctness : fme_strategy8.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  destruct H; subst.
  - Intros_r l1.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
  - Intros_r l1.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
Qed.

Lemma fme_strategy14_correctness : fme_strategy14.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  destruct H; subst.
  - Intros_r l2.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
  - Intros_r l2.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
Qed.

Lemma fme_strategy11_correctness : fme_strategy11.
  pre_process_default.
  simpl.
  entailer!.
  Intros x0.
  Intros y.
  Exists y x0.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma fme_strategy12_correctness : fme_strategy12.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  assert(H0: p <> 0) by lia.
  clear H.
  do 5 Intros_r_any.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Exists x x1.
  entailer!.
Qed.

Lemma fme_strategy17_correctness : fme_strategy17.
  pre_process_default.
  unfold coef_array.
  unfold coef_array_missing_i_rec.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply IntArray.missing_i_merge_to_full; try lia.
  destruct i; try lia.
  unfold coef_replace_Znth.
  unfold Constraint_list.
  simpl const.
  set (k:= Z.pos p0) in *.
  set (t:= k-1).
  simpl coef.
  unfold t.
  rewrite replace_Znth_cons; try lia. Right.
  entailer!.
Qed.

Lemma fme_strategy9_correctness : fme_strategy9.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  assert(H0: p <> 0) by lia.
  destruct l; simpl; entailer!.
  Intros x y.
  Exists c l.
  entailer!.
  Exists x y.
  entailer!.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  Intros_r q.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma fme_strategy10_correctness : fme_strategy10.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  assert(H0: p <> 0) by lia.
  do 4 Intros_r_any.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros x3 y.
  rewrite H1.
  simpl.
  entailer!.
  Exists x3 y.
  entailer!.
Qed.
