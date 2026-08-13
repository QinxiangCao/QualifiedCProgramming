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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_tdiv_r_entail_wit_1_split_goal_spatial :
  mpz_tdiv_r_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold optional_store_Z.
  Left.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_tdiv_r_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_2 : mpz_tdiv_r_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH1 into Hr_eq.
  rename PreH2 into Hmath.
  rename PreH3 into Hret_low.
  rename PreH4 into Hret_high.
  rename PreH5 into Hret_ok.
  rename PreH6 into Hr_eq2.
  rename PreH7 into Hn_nonnull.
  rename PreH8 into Hzd_pre.
  unfold mpz_div_qr_math in Hmath.
  destruct Hmath as [Htrunc | [Hfloor | Hceil]].
  - unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC in Htrunc.
    destruct Htrunc as [Hzd [_ [Hdiv [Hrem Hsign]]]].
    destruct Hsign as [Hzero | Hsame].
    + Left.
      Exists rv_2 qv_2.
      unfold optional_store_Z.
      Split.
      * Intros.
        Left.
        split_pure_spatial.
        -- normalize.
           repeat cancel.
        -- repeat split_pures; dump_pre_spatial; assumption.
      * Intros.
        exfalso.
        match goal with
        | Hnonnull : 0 <> NULL |- False => apply Hnonnull; reflexivity
        end.
    + Right.
      Exists rv_2 qv_2.
      unfold optional_store_Z.
      Split.
      * Intros.
        Left.
        split_pure_spatial.
        -- normalize.
           repeat cancel.
        -- repeat split_pures; dump_pre_spatial; assumption.
      * Intros.
        exfalso.
        match goal with
        | Hnonnull : 0 <> NULL |- False => apply Hnonnull; reflexivity
        end.
  - unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR in Hfloor.
    lia.
  - unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL in Hceil.
    lia.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH1 into Hr_eq.
  rename PreH2 into Hzd.
  rename PreH3 into Hdiv.
  rename PreH4 into Hrem.
  rename PreH5 into Hzero.
  Left.
  Exists rv_2 qv_2.
  unfold optional_store_Z.
  Split.
  - Intros.
    split_pure_spatial.
    + normalize.
      repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
  - Intros.
    exfalso.
    match goal with
    | Hnonnull : 0 <> NULL |- False => apply Hnonnull; reflexivity
    end.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_2 : mpz_tdiv_r_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH1 into Hr_eq.
  rename PreH2 into Hzd.
  rename PreH3 into Hdiv.
  rename PreH4 into Hrem.
  rename PreH5 into Hsame.
  Right.
  Exists rv_2 qv_2.
  unfold optional_store_Z.
  Split.
  - Intros.
    split_pure_spatial.
    + normalize.
      repeat cancel.
    + repeat split_pures; dump_pre_spatial; assumption.
  - Intros.
    exfalso.
    match goal with
    | Hnonnull : 0 <> NULL |- False => apply Hnonnull; reflexivity
    end.
Qed.
