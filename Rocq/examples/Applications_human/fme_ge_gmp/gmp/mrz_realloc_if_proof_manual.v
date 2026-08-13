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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mrz_realloc_if_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mrz_realloc_if_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists cap.
  assert (Z.max n_pre cap = cap) as Hmax.
  {
    apply Z.max_r.
    lia.
  }
  rewrite Hmax.
  split_pure_spatial.
  - cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs m) (Zabs old)).
    cancel (UIntArray.undef_seg ptr (Zabs old) cap).
    cancel (&( z_pre # "__mpz_struct" ->ₛ "_mp_size") # Int |-> old).
    cancel (&( z_pre # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap).
    cancel (&( z_pre # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists r_callee__mp_alloc.
  assert (Z.max n_pre cap = Z.max n_pre 1) as Hmax.
  {
    rewrite Z.max_l by lia.
    rewrite Z.max_l by lia.
    reflexivity.
  }
  rewrite Hmax.
  split_pure_spatial.
  - cancel (mpd_store_Z_compact UINT_MOD retval (Zabs m) (Zabs old)).
    cancel (UIntArray.undef_seg retval (Zabs old) (Z.max n_pre 1)).
    cancel (&( z_pre # "__mpz_struct" ->ₛ "_mp_size") # Int |-> old).
    cancel (&( z_pre # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> r_callee__mp_alloc).
    cancel (&( z_pre # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> retval).
  - split_pures; dump_pre_spatial; auto.
Qed.
