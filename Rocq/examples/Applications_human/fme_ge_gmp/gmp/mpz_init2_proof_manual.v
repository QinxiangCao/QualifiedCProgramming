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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_init2_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_init2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_init2_return_wit_1_split_goal_1 :
  mpz_init2_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hround:
    signed_last_nbits (1 + ((bits_pre - 1) ÷ 32)) 32 = alloc).
  {
    rewrite PreH3.
    replace (alloc * 32 - 1) with ((alloc - 1) * 32 + 31) by ring.
    rewrite Z.quot_div_nonneg by lia.
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia.
    replace (1 + (alloc - 1 + 0)) with alloc by ring.
    rewrite signed_last_nbits_eq; lia.
  }
  dump_pre_spatial.
  rewrite <- PreH3.
  exact Hround.
Qed.

Lemma proof_of_mpz_init2_return_wit_1_split_goal_spatial :
  mpz_init2_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hround:
    signed_last_nbits (1 + ((bits_pre - 1) ÷ 32)) 32 = alloc).
  {
    rewrite PreH3.
    replace (alloc * 32 - 1) with ((alloc - 1) * 32 + 31) by ring.
    rewrite Z.quot_div_nonneg by lia.
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia.
    replace (1 + (alloc - 1 + 0)) with alloc by ring.
    rewrite signed_last_nbits_eq; lia.
  }
  rewrite Hround.
  cancel.
Qed.

Lemma proof_of_mpz_init2_return_wit_1 : mpz_init2_return_wit_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_init2_return_wit_1_split_goal_spatial.
  + Goal_apply proof_of_mpz_init2_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpz_init2_partial_solve_wit_1_pure_split_goal_1 :
  mpz_init2_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hround:
    signed_last_nbits (1 + ((bits_pre - 1) ÷ 32)) 32 = alloc).
  {
    rewrite PreH8.
    replace (alloc * 32 - 1) with ((alloc - 1) * 32 + 31) by ring.
    rewrite Z.quot_div_nonneg by nia.
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia.
    replace (1 + (alloc - 1 + 0)) with alloc by ring.
    rewrite signed_last_nbits_eq; lia.
  }
  rewrite <- PreH8.
  rewrite Hround.
  dump_pre_spatial.
  exact PreH9.
Qed.

Lemma proof_of_mpz_init2_partial_solve_wit_1_pure_split_goal_2 :
  mpz_init2_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hround:
    signed_last_nbits (1 + ((bits_pre - 1) ÷ 32)) 32 = alloc).
  {
    rewrite PreH8.
    replace (alloc * 32 - 1) with ((alloc - 1) * 32 + 31) by ring.
    rewrite Z.quot_div_nonneg by nia.
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia.
    replace (1 + (alloc - 1 + 0)) with alloc by ring.
    rewrite signed_last_nbits_eq; lia.
  }
  rewrite <- PreH8.
  rewrite Hround.
  dump_pre_spatial.
  exact PreH9.
Qed.

Lemma proof_of_mpz_init2_partial_solve_wit_1_pure : mpz_init2_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_init2_partial_solve_wit_1_pure_split_goal_1.
  + Goal_apply proof_of_mpz_init2_partial_solve_wit_1_pure_split_goal_2.
Qed.
