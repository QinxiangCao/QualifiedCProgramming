Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import fme_gmp_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma fme_gmp_strategy5_correctness : fme_gmp_strategy5.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma fme_gmp_strategy6_correctness : fme_gmp_strategy6.
Proof.
  pre_process_default.
  entailer!.
  rewrite H, H0, H1.
  entailer!.
Qed.

Lemma fme_gmp_strategy18_correctness : fme_gmp_strategy18.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma fme_gmp_strategy19_correctness : fme_gmp_strategy19.
Proof.
  pre_process_default.
  entailer!.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma fme_gmp_strategy7_correctness : fme_gmp_strategy7.
Proof.
  pre_process_default.
  Intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma fme_gmp_strategy13_correctness : fme_gmp_strategy13.
Proof.
  pre_process_default.
  Intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma fme_gmp_strategy15_correctness : fme_gmp_strategy15.
Proof.
  pre_process_default.
  assert (Hp_null : p <> NULL) by (unfold NULL; lia).
  sep_apply (mpz_coef_array_split p i n l); try lia; try exact Hp_null.
  cancel (mpz_coef_array_missing_i_rec p i 0 n l).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  unfold mpz_store, mpz_sizeof.
  cancel.
Qed.

Lemma fme_gmp_strategy115_correctness : fme_gmp_strategy115.
Proof.
  pre_process_default.
  assert (Hp_null : p <> NULL) by (unfold NULL; lia).
  sep_apply (mpz_coef_array_split p 0 n l); try lia; try exact Hp_null.
  cancel (mpz_coef_array_missing_i_rec p 0 0 n l).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  unfold mpz_store, mpz_sizeof.
  replace (p + 0 * sizeof("__mpz_struct")) with p by lia.
  cancel.
Qed.

Lemma fme_gmp_strategy16_correctness : fme_gmp_strategy16.
Proof.
  pre_process_default.
  change (store_Z (p + i * sizeof("__mpz_struct")) (coef_Znth i l 0))
    with (mpz_store p i (coef_Znth i l 0)).
  unfold mpz_coef_array_missing_i_rec.
  sep_apply MpzArray.missing_i_merge_to_full; try lia.
  unfold mpz_coef_array.
  unfold coef_Znth.
  rewrite replace_Znth_Znth by tauto.
  Right.
  entailer!.
Qed.

Lemma fme_gmp_strategy116_correctness : fme_gmp_strategy116.
Proof.
  pre_process_default.
  replace (store_Z p (coef_Znth 0 l 0))
    with (mpz_store p 0 (coef_Znth 0 l 0)).
  2:{
    unfold mpz_store, mpz_sizeof.
    replace (p + 0 * sizeof("__mpz_struct")) with p by lia.
    reflexivity.
  }
  unfold mpz_coef_array_missing_i_rec.
  sep_apply MpzArray.missing_i_merge_to_full; try lia.
  unfold mpz_coef_array.
  unfold coef_Znth.
  rewrite replace_Znth_Znth by tauto.
  Right.
  entailer!.
Qed.

Lemma fme_gmp_strategy8_correctness : fme_gmp_strategy8.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  destruct H; subst.
  - Intros_r l1.
    entailer!.
    apply_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
  - Intros_r l1.
    entailer!.
    apply_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
Qed.

Lemma fme_gmp_strategy14_correctness : fme_gmp_strategy14.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  destruct H; subst.
  - Intros_r l2.
    entailer!.
    apply_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
  - Intros_r l2.
    entailer!.
    apply_sepcon_adjoint.
    Intros.
    subst.
    reflexivity.
Qed.

Lemma fme_gmp_strategy11_correctness : fme_gmp_strategy11.
Proof.
  pre_process_default.
  simpl.
  entailer!.
  Intros x0.
  Intros y.
  Exists y x0.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma fme_gmp_strategy12_correctness : fme_gmp_strategy12.
Proof.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  assert (H0 : p <> 0) by lia.
  clear H.
  do 5 Intros_r_any.
  entailer!.
  apply_sepcon_adjoint.
  Exists x x1.
  entailer!.
Qed.

Lemma fme_gmp_strategy17_correctness : fme_gmp_strategy17.
Proof.
  pre_process_default.
  assert (Hp_null : p <> NULL) by (unfold NULL; lia).
  change (store_Z (p + i * sizeof("__mpz_struct")) v)
    with (mpz_store p i v).
  sep_apply (mpz_coef_array_merge p i n v l); try lia; try exact Hp_null.
  cancel.
Qed.

Lemma fme_gmp_strategy9_correctness : fme_gmp_strategy9.
Proof.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  assert (H0 : p <> 0) by lia.
  destruct l; simpl; entailer!.
  Intros x y.
  Exists c l.
  entailer!.
  Exists x y.
  entailer!.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  Intros_r q.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma fme_gmp_strategy10_correctness : fme_gmp_strategy10.
Proof.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  entailer!.
  assert (H0 : p <> 0) by lia.
  do 4 Intros_r_any.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
  Intros x3 y.
  rewrite H1.
  simpl.
  entailer!.
  Exists x3 y.
  entailer!.
Qed.
