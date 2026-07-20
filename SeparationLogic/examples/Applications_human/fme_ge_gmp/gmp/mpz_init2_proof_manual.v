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

Lemma proof_of_mpz_init2_return_wit_1 : mpz_init2_return_wit_1.
Proof.
  aggressive_pre_process.
  all: assert (Hround:
    signed_last_nbits (1 + unsigned_last_nbits (bits_pre - 1) 64 ÷ 32) 32 = alloc)
    by (apply mpz_init2_alloc_round_quot; auto).
  all: rewrite Hround.
  all: entailer!.
Qed.

Lemma proof_of_mpz_init2_partial_solve_wit_1_pure : mpz_init2_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  all: assert (Hround:
    signed_last_nbits (1 + unsigned_last_nbits (bits_pre - 1) 64 ÷ 32) 32 = alloc)
    by (apply mpz_init2_alloc_round_quot; auto).
  all: rewrite Hround.
  all: entailer!.
Qed.
