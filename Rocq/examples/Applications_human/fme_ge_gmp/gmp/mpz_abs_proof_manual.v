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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_entail_wit_1_eq : mpz_abs_entail_wit_1_eq.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre.
  unfold store_Z.
  Intros ptr size cap.
  Exists ptr cap size.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; reflexivity.
Qed.

Lemma proof_of_mpz_abs_return_wit_1_eq_split_goal_spatial :
  mpz_abs_return_wit_1_eq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre.
  subst retval.
  unfold store_Z.
  Exists ptr (Zabs size) cap.
  replace (Zabs (Zabs z_eq)) with (Zabs z_eq)
    by (destruct (Z_lt_dec z_eq 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  replace (Zabs (Zabs size)) with (Zabs size)
    by (destruct (Z_lt_dec size 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption.
    unfold same_sign.
    lia.
Qed.

Lemma proof_of_mpz_abs_return_wit_1_eq : mpz_abs_return_wit_1_eq.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_return_wit_1_eq_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_return_wit_2_neq_split_goal_1 :
  mpz_abs_return_wit_2_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_return_wit_2_neq_split_goal_2 :
  mpz_abs_return_wit_2_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst retval.
  dump_pre_spatial.
  unfold same_sign.
  apply or_introl.
  apply conj.
  - pose proof (Z.abs_nonneg z_neq); lia.
  - pose proof (Z.abs_nonneg rsize); lia.
Qed.

Lemma proof_of_mpz_abs_return_wit_2_neq_split_goal_spatial :
  mpz_abs_return_wit_2_neq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst retval.
  replace (Zabs (Zabs z_neq)) with (Zabs z_neq)
    by (destruct (Z_lt_dec z_neq 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  replace (Zabs (Zabs rsize)) with (Zabs rsize)
    by (destruct (Z_lt_dec rsize 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  cancel.
Qed.

Lemma proof_of_mpz_abs_return_wit_2_neq : mpz_abs_return_wit_2_neq.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_abs_return_wit_2_neq_split_goal_spatial.
  + Goal_apply proof_of_mpz_abs_return_wit_2_neq_split_goal_1.
  + Goal_apply proof_of_mpz_abs_return_wit_2_neq_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_partial_solve_wit_3_eq_pure_split_goal_1 :
  mpz_abs_partial_solve_wit_3_eq_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_partial_solve_wit_3_eq_pure :
  mpz_abs_partial_solve_wit_3_eq_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_partial_solve_wit_3_eq_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_partial_solve_wit_4_neq_pure_split_goal_1 :
  mpz_abs_partial_solve_wit_4_neq_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_partial_solve_wit_4_neq_pure :
  mpz_abs_partial_solve_wit_4_neq_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_partial_solve_wit_4_neq_pure_split_goal_1.
Qed.
