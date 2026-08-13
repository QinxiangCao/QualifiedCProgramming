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
    Intros Hcap_range.
    split_pures; dump_pre_spatial; try assumption; try lia.
    change Int.max_signed with 2147483647 in H4.
    lia.
Qed.

Lemma proof_of_mpz_set_si_entail_wit_2_split_goal_1 :
  mpz_set_si_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_si_entail_wit_2_split_goal_2 :
  mpz_set_si_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_si_entail_wit_2_split_goal_spatial :
  mpz_set_si_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic
    (UIntArray.undef_full_split_to_undef_seg retval 1 (Z.max 1 cap)).
  - LLM_pre_process ltac:(int_auto).
  - cancel.
Qed.

Lemma proof_of_mpz_set_si_entail_wit_2 : mpz_set_si_entail_wit_2.
Proof.
  aggressive_pre_process.
  + exact
      (proof_of_mpz_set_si_entail_wit_2_split_goal_spatial
        x_pre x0 old size cap z_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
  + exact
      (proof_of_mpz_set_si_entail_wit_2_split_goal_1
        x_pre x0 old size cap z_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
  + exact
      (proof_of_mpz_set_si_entail_wit_2_split_goal_2
        x_pre x0 old size cap z_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
Qed.

Lemma proof_of_mpz_set_si_return_wit_2_split_goal_1 :
  mpz_set_si_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_si_return_wit_2_split_goal_2 :
  mpz_set_si_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold same_sign.
  lia.
Qed.

Lemma proof_of_mpz_set_si_return_wit_2_split_goal_spatial :
  mpz_set_si_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (((-(x_pre + 1)) + 1) :: nil).
  replace (Zabs (-1)) with 1 by lia.
  replace (Zabs x0) with ((-(x_pre + 1)) + 1) by lia.
  sep_apply_l_atomic (UIntArray.seg_single rp_addr_v 0 ((-(x_pre + 1)) + 1)).
  rewrite UIntArray.seg_to_full.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  split_pure_spatial.
  - LLM_pre_process ltac:(int_auto).
    rewrite Zlength_cons, Zlength_nil.
    replace (rp_addr_v + 0 * sizeof(UINT)) with rp_addr_v by lia.
    cancel.
    change (Z.succ 0) with 1.
    cancel.
  - repeat split_pures.
    all: dump_pre_spatial.
    all: try (rewrite list_to_Z_single; repeat split; simpl; unfold UINT_MOD in *; lia).
    all: try (rewrite Zlength_cons, Zlength_nil; lia).
    all: unfold UINT_MOD in *; simpl; lia.
Qed.

Lemma proof_of_mpz_set_si_return_wit_2 : mpz_set_si_return_wit_2.
Proof.
  aggressive_pre_process.
  + exact
      (proof_of_mpz_set_si_return_wit_2_split_goal_spatial
        x_pre x0 cap cap_new rp_addr_v
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  + exact
      (proof_of_mpz_set_si_return_wit_2_split_goal_1
        x_pre x0 cap cap_new rp_addr_v
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  + exact
      (proof_of_mpz_set_si_return_wit_2_split_goal_2
        x_pre x0 cap cap_new rp_addr_v
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
Qed.
