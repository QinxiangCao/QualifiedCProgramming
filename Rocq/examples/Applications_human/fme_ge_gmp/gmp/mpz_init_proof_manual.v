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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_init_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_init_return_wit_1 : mpz_init_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z_dummy.
  cancel (&( x_pre # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> 0).
  cancel (&( x_pre # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0).
  cancel (&( x_pre # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> &( "mpz_dummy_limb")).
Qed.

Lemma proof_of_mpz_init_derive_abs_by_dummy : mpz_init_derive_abs_by_dummy.
Proof.
  LLM_pre_process ltac:(int_auto).
  cancel (&( x_pre # "__mpz_struct" ->ₛ "_mp_alloc") # Int |->_).
  cancel (&( x_pre # "__mpz_struct" ->ₛ "_mp_size") # Int |->_).
  cancel (&( x_pre # "__mpz_struct" ->ₛ "_mp_d") # Ptr |->_).
  apply derivable1_wand_sepcon_adjoint.
  sep_apply (store_Z_dummy_to_store_Z_0 x_pre (&( "mpz_dummy_limb" ))).
  cancel.
Qed.
