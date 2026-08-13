Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import poly_sll_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import poly_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma poly_sll_strategy1_correctness : poly_sll_strategy1.
  pre_process_default.
Qed.

Lemma poly_sll_strategy2_correctness : poly_sll_strategy2.
  pre_process_default.
Qed.

Lemma poly_sll_strategy4_correctness : poly_sll_strategy4.
  pre_process_default.
  sep_apply sll_zero; [ | tauto].
  entailer!.
Qed.

Lemma poly_sll_strategy5_correctness : poly_sll_strategy5.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma poly_sll_strategy16_correctness : poly_sll_strategy16.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma poly_sll_strategy17_correctness : poly_sll_strategy17.
  pre_process_default.
  destruct l; simpl.
  + entailer!.
  + Intros h q.
    destruct l0; simpl.
    - entailer!.
    - Intros h0 q0.
      pose proof dup_store_ptr (&( p # "list" ->ₛ "data")) h h0.
      sep_apply H1.
      entailer!.
Qed.

Lemma poly_sll_strategy18_correctness : poly_sll_strategy18.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma poly_sll_strategy7_correctness : poly_sll_strategy7.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma poly_sll_strategy10_correctness : poly_sll_strategy10.
  pre_process_default.
  simpl.
  Intros h y; Exists y h; entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma poly_sll_strategy11_correctness : poly_sll_strategy11.
  pre_process_default.
  simpl.
  Exists h y; entailer!.
Qed.

Lemma poly_sll_strategy12_correctness : poly_sll_strategy12.
  pre_process_default.
  Intros.
  subst.
  sep_apply sllseg_sll.
  entailer!.
Qed.

Lemma poly_sll_strategy8_correctness : poly_sll_strategy8.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  sep_apply sll_not_zero; [ | destruct H; unfold NULL; congruence ].
  Intros h y a l0.
  Exists a l0.
  subst.
  simpl.
  Exists h y.
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma poly_sll_strategy9_correctness : poly_sll_strategy9.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  entailer!.
  Intros_r A.
  Intros_r l.
  Intros_r x.
  Intros_r l0.
  Intros_r storeA.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma poly_sll_strategy19_correctness : poly_sll_strategy19.
  pre_process_default.
Qed.