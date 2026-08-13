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
  Intros_p Hl.
  subst l.
  simpl.
  split_pure_spatial.
  - normalize; cancel.
  - dump_pre_spatial; reflexivity.
Qed.

Lemma fme_gmp_strategy6_correctness : fme_gmp_strategy6.
Proof.
  pre_process_default.
  Intros_p Hn.
  Intros_p Hx.
  Intros_p Hl.
  subst n2 x1 l1.
  cancel.
Qed.

Lemma fme_gmp_strategy18_correctness : fme_gmp_strategy18.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  simpl.
  split_pure_spatial.
  - normalize; cancel.
  - dump_pre_spatial; reflexivity.
Qed.

Lemma fme_gmp_strategy19_correctness : fme_gmp_strategy19.
Proof.
  pre_process_default.
  Intros_p Hn.
  Intros_p Hl.
  subst n2 l2.
  cancel.
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
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; assumption.
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
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; assumption.
Qed.

Lemma fme_gmp_strategy8_correctness : fme_gmp_strategy8.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or).
  Intros_p Hnm.
  destruct Hnm as [Hnm | Hmn]; subst.
  - split_pure_spatial.
    + Intros_r l1.
    apply_sepcon_adjoint.
      Intros_p Hl.
      subst l1.
      cancel.
    + dump_pre_spatial; left; reflexivity.
  - split_pure_spatial.
    + Intros_r l1.
      apply_sepcon_adjoint.
      Intros_p Hl.
      subst l1.
      cancel.
    + dump_pre_spatial; left; reflexivity.
Qed.

Lemma fme_gmp_strategy14_correctness : fme_gmp_strategy14.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or).
  Intros_p Hnm.
  destruct Hnm as [Hnm | Hmn]; subst.
  - split_pure_spatial.
    + Intros_r l2.
      apply_sepcon_adjoint.
      Intros_p Hl.
      subst l2.
      cancel.
    + dump_pre_spatial; left; reflexivity.
  - split_pure_spatial.
    + Intros_r l2.
      apply_sepcon_adjoint.
      Intros_p Hl.
      subst l2.
      cancel.
    + dump_pre_spatial; left; reflexivity.
Qed.

Lemma fme_gmp_strategy11_correctness : fme_gmp_strategy11.
Proof.
  pre_process_default.
  simpl.
  Intros.
  Intros x0 y.
  Intros.
  Exists y x0.
  split_pure_spatial.
  - cancel (&(p # "InequList" ->ₛ "coef") # Ptr |-> x0).
    cancel (mpz_coef_array x0 n x).
    cancel (&(p # "InequList" ->ₛ "next") # Ptr |-> y).
    cancel (InequList y n l).
    apply_sepcon_adjoint.
    normalize; cancel.
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma fme_gmp_strategy12_correctness : fme_gmp_strategy12.
Proof.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  Intros_p Hor.
  assert (Hp : p <> 0) by lia.
  split_pure_spatial.
  - Intros_r h c y l n.
    apply_sepcon_adjoint.
    Intros_p Hh.
    Exists h y.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
  - dump_pre_spatial; exact Hor.
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
  Intros_p Hor.
  assert (Hp : p <> 0) by lia.
  destruct l as [| c l].
  - simpl.
    Intros_p Hnull.
    unfold NULL in Hnull.
    contradiction.
  - simpl.
    Intros x y.
    Intros.
    Exists c l.
    normalize.
    Exists x y.
    apply sepcon_cancel_end.
    + rewrite <- (logic_equiv_coq_prop_or).
      split_pure_spatial.
      * cancel (&(p # "InequList" ->ₛ "coef") # Ptr |-> x).
        cancel (mpz_coef_array x n c).
        repeat cancel.
      * repeat split_pures; dump_pre_spatial; try assumption; try reflexivity.
    + Intros_r q.
      apply_sepcon_adjoint.
      normalize.
      Split.
      * Left; cancel.
      * Right; cancel.
Qed.

Lemma fme_gmp_strategy10_correctness : fme_gmp_strategy10.
Proof.
  pre_process_default.
  simpl.
  rewrite <- (logic_equiv_coq_prop_or).
  Intros_p Hor.
  split_pure_spatial.
  - Intros_r l1 c l0 n.
    apply_sepcon_adjoint.
    Intros x y.
    repeat Intros.
    subst l1.
    simpl.
    Exists x y.
    split_pure_spatial.
    + normalize; repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
  - dump_pre_spatial; exact Hor.
Qed.
