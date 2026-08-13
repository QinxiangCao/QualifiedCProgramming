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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_set_entail_wit_3_neq : mpz_set_entail_wit_3_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z.
  Intros rptr rsize rcap.
  Exists rptr ptr rcap rsize cap size.
  replace (Zabs size) with retval by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_entail_wit_4_neq : mpz_set_entail_wit_4_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists optr_2 retval z_callee__mp_alloc rsize_2 ocap_2 rcap_2 osize_2.
  subst z_callee__mp_alloc.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
               retval (Zabs old_neq) (Zabs rsize_2) n (Z.max n rcap_2)).
  all: try lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_entail_wit_5_neq : mpz_set_entail_wit_5_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists optr_2 rop__mp_d_2 rop__mp_alloc_2 rsize_2 ocap_2 rcap_2 osize_2.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact optr_2 (Zabs z_neq) n).
  - LLM_pre_process ltac:(int_auto).
  - assumption.
Qed.

Lemma proof_of_mpz_set_return_wit_1_neq : mpz_set_return_wit_1_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z optr (Zabs z_neq) n).
  Intros.
  unfold store_Z.
  Exists rp osize (Z.max n rcap) optr osize ocap.
  replace (Zabs osize) with n by lia.
  subst rop__mp_alloc.
  subst rop__mp_d.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp (Zabs z_neq) n).
  - LLM_pre_process ltac:(int_auto).
  - assumption.
Qed.

Lemma proof_of_mpz_set_return_wit_3_neq : mpz_set_return_wit_3_neq.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre.
  unfold store_Z.
  Intros ptr1 size1 cap1 ptr2 size2 cap2.
  sep_apply (dup_store_int (&(op_pre # "__mpz_struct" ->ₛ "_mp_size")) size2 size1).
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_partial_solve_wit_2_neq_pure : mpz_set_partial_solve_wit_2_neq_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | |- context[mpd_store_Z_compact UINT_MOD ?ptr ?v (Zabs ?size)] =>
      prop_apply (mpd_store_Z_compact_range UINT_MOD ptr v (Zabs size))
  end.
  Intros.
  match goal with
  | H : 0 <= Zabs ?size <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      pose proof (Z.abs_le size 1073741824)
  end.
  split_pures; dump_pre_spatial; lia.
Qed.
