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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_si_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_si_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_set_si_entail_wit_1 : mpz_set_si_entail_wit_1.
Proof.
  unfold mpz_set_si_entail_wit_1.
  left.
  intros.
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap_2).
  Intros_p Hcap_range.
  Exists ptr_2 cap_2 size_2.
  sep_apply_l_atomic
    (mpd_store_Z_compact_undef_tail_to_undef_split
       ptr_2 (Zabs old) (Zabs size_2) cap_2 cap_2).
  - entailer!.
  - entailer!.
  - entailer!.
  - entailer!.
  - rewrite UIntArray.undef_seg_empty.
    entailer!.
Qed.

Lemma proof_of_mpz_set_si_entail_wit_2 : mpz_set_si_entail_wit_2.
Proof.
  unfold mpz_set_si_entail_wit_2.
  left.
  intros.
  Exists z_callee__mp_alloc.
  sep_apply_l_atomic
    (UIntArray.undef_full_split_to_undef_seg retval 1 (Z.max 1 cap)).
  - entailer!.
  - rewrite <- PreH1.
    entailer!.
Qed.

Lemma proof_of_mpz_set_si_return_wit_2 : mpz_set_si_return_wit_2.
Proof.
  unfold mpz_set_si_return_wit_2.
  right.
  intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (((-(x_pre + 1)) + 1) :: nil).
  replace (Zabs (-1)) with 1 by lia.
  replace (Zabs x0) with ((-(x_pre + 1)) + 1) by lia.
  sep_apply_l_atomic (UIntArray.seg_single rp_addr_v 0 ((-(x_pre + 1)) + 1)).
  rewrite UIntArray.seg_to_full.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  entailer!; unfold UINT_MOD in *; simpl; try lia.
  - replace (rp_addr_v + 0) with rp_addr_v by lia.
    entailer!.
  - rewrite list_to_Z_single.
    reflexivity.
  - unfold same_sign.
    lia.
Qed.
