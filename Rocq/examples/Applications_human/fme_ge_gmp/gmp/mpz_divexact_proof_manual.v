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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_divexact_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_divexact_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_divexact_entail_wit_1_split_goal_spatial :
  mpz_divexact_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply derivable1_sepcon_mono.
  - cancel.
  - apply derivable1_sepcon_mono.
    + cancel.
    + eapply sepcon_cancel_end.
      * cancel.
      * apply emp_to_optional_store_Z_null.
        reflexivity.
Qed.

Lemma proof_of_mpz_divexact_entail_wit_1 : mpz_divexact_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_divexact_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_divexact_entail_wit_2_split_goal_1 :
  mpz_divexact_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (mpz_div_qr_math_exact_quotient 2 zn zd qv_2 rv_2 PreH1 PreH7) as [Hq Hr].
  subst qv_2 rv_2.
  split_pures.
  dump_pre_spatial.
  exact PreH1.
Qed.

Lemma proof_of_mpz_divexact_entail_wit_2_split_goal_spatial :
  mpz_divexact_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (mpz_div_qr_math_exact_quotient 2 zn zd qv_2 rv_2 PreH1 PreH7) as [Hq Hr].
  subst qv_2 rv_2.
  cancel.
Qed.

Lemma proof_of_mpz_divexact_entail_wit_2 : mpz_divexact_entail_wit_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_divexact_entail_wit_2_split_goal_spatial.
  + Goal_apply proof_of_mpz_divexact_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpz_divexact_return_wit_1_split_goal_spatial :
  mpz_divexact_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst qv rv.
  assert (Hopt_emp : optional_store_Z 0 0 |-- emp).
  { unfold optional_store_Z.
    Split.
    - Intros_p Hnull.
      cancel.
    - Intros_p Hnonnull.
      exfalso.
      apply Hnonnull.
      reflexivity. }
  apply
    (derivable1_trans _
      (store_Z num_pre zn ** (store_Z den_pre zd ** store_Z q_pre (zn ÷ zd)))).
  - apply derivable1_sepcon_mono.
    + cancel.
    + apply derivable1_sepcon_mono.
      * cancel.
      * eapply sepcon_cancel_lhs_emp.
        exact Hopt_emp.
  - cancel.
Qed.

Lemma proof_of_mpz_divexact_return_wit_1 : mpz_divexact_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_divexact_return_wit_1_split_goal_spatial.
Qed.
