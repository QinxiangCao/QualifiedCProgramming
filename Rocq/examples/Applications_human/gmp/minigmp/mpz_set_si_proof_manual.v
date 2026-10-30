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
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_set_si_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_set_si_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_set_si_entail_wit_1 : mpz_set_si_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists ptr_2 cap_2 size_2.
  sep_apply
    (mpd_store_Z_compact_undef_tail_to_undef_split
       ptr_2 (Zabs old) (Zabs size_2) cap_2 cap_2);
    try lia; try apply Z.abs_nonneg; try exact PreH2.
  rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - LLM_pre_process ltac:(int_auto).
  - LLM_pre_process ltac:(int_auto).
    prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap_2).
    Intros_p Hcap_range.
    split_pures; dump_pre_spatial; try assumption; try lia.
    change Int.max_signed with 2147483647 in Hcap_range.
    lia.
Qed.

Lemma proof_of_mpz_set_si_entail_wit_2_split_goal_1 :
  mpz_set_si_entail_wit_2_split_goal_1.
Abort.

Lemma proof_of_mpz_set_si_entail_wit_2_split_goal_2 :
  mpz_set_si_entail_wit_2_split_goal_2.
Abort.

Lemma proof_of_mpz_set_si_entail_wit_2_split_goal_spatial :
  mpz_set_si_entail_wit_2_split_goal_spatial.
Abort.

Lemma proof_of_mpz_set_si_entail_wit_2 : mpz_set_si_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists z__mp_alloc.
  split_pure_spatial.
  - subst z__mp_alloc.
    sep_apply_l_atomic
      (UIntArray.undef_full_split_to_undef_seg retval 1 (Z.max 1 cap)).
    + LLM_pre_process ltac:(int_auto).
    + cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_set_si_return_wit_2_split_goal_1 :
  mpz_set_si_return_wit_2_split_goal_1.
Abort.

Lemma proof_of_mpz_set_si_return_wit_2_split_goal_2 :
  mpz_set_si_return_wit_2_split_goal_2.
Abort.

Lemma proof_of_mpz_set_si_return_wit_2_split_goal_spatial :
  mpz_set_si_return_wit_2_split_goal_spatial.
Abort.

Lemma proof_of_mpz_set_si_return_wit_2 : mpz_set_si_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply
    (store_uint_range
      (rp_addr_v + 0 * sizeof(UINT)) ((-(x_pre + 1)) + 1)).
  Intros.
  unfold store_Z, mpd_store_Z_compact, mpd_store_list.
  Exists rp_addr_v. Exists (-1). Exists cap_new.
  Exists (((-(x_pre + 1)) + 1) :: nil).
  replace (Zabs (-1)) with 1 by lia.
  replace (Zabs x0) with ((-(x_pre + 1)) + 1) by lia.
  sep_apply_l_atomic
    (UIntArray.seg_single rp_addr_v 0 ((-(x_pre + 1)) + 1)).
  rewrite UIntArray.seg_to_full.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  split_pure_spatial.
  - rewrite Zlength_cons, Zlength_nil.
    replace (rp_addr_v + 0 * sizeof(UINT)) with rp_addr_v by lia.
    cancel.
    change (Z.succ 0) with 1.
    cancel.
  - repeat split_pures; dump_pre_spatial.
    + lia.
    + unfold same_sign; lia.
    + rewrite list_to_Z_single.
      repeat split.
      * simpl; lia.
      * lia.
      * unfold UINT_MOD.
        change Int.max_unsigned with 4294967295 in H.
        lia.
    + rewrite Zlength_cons, Zlength_nil; lia.
Qed.
