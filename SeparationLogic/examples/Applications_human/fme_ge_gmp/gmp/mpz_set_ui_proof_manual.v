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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_ui_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_ui_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Proof.
  pre_process.
  Exists retval_2.
  rewrite <- PreH3.
  rewrite PreH9.
  rewrite UIntArray.undef_full_empty.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_2 : mpz_realloc_return_wit_2.
Proof.
  pre_process.
  Exists retval_2.
  rewrite <- PreH3.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_6_pure : mpz_realloc_partial_solve_wit_6_pure.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_7_pure : mpz_realloc_partial_solve_wit_7_pure.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_1 : mpz_realloc_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg r__mp_d r__mp_alloc).
  entailer!.
  simpl; lia.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_2 : mpz_realloc_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply_l_atomic (mpd_store_Z_compact_to_mpd_store_Z r__mp_d 0 0).
  sep_apply_l_atomic (mpd_store_Z_to_undef_full r__mp_d 0 0).
  rewrite UIntArray.undef_full_empty.
  sep_apply_l_atomic (UIntArray.undef_seg_to_undef_full r__mp_d 0 size).
  replace (r__mp_d + 0 * sizeof(UINT)) with r__mp_d by lia.
  replace (size - 0) with size by lia.
  repeat cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Proof.
  pre_process.
  Exists cap_raw.
  replace (Z.max n_pre cap_raw) with cap_raw by lia.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Proof.
  pre_process.
  Exists r_callee__mp_alloc.
  replace (Z.max n_pre cap_raw) with r_callee__mp_alloc by lia.
  replace (Z.max n_pre 1) with r_callee__mp_alloc by lia.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
Qed.

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_1 : mpz_set_ui_entail_wit_1.
Proof.
  pre_process.
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

Lemma proof_of_mpz_set_ui_entail_wit_2 : mpz_set_ui_entail_wit_2.
Proof.
  pre_process.
  Exists z_callee__mp_alloc.
  sep_apply_l_atomic
    (UIntArray.undef_full_split_to_undef_seg retval 1 (Z.max 1 cap)).
  - entailer!.
  - rewrite <- PreH1.
    entailer!.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1 : mpz_set_ui_return_wit_1.
Proof.
  aggressive_pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (x_pre :: nil).
  replace (Zabs 1) with 1 by lia.
  replace (Zabs x0) with x_pre by lia.
  sep_apply_l_atomic (UIntArray.seg_single rp_addr_v 0 x_pre).
  rewrite UIntArray.seg_to_full.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  entailer!; unfold UINT_MOD in *; simpl; try lia.
  - replace (rp_addr_v + 0) with rp_addr_v by lia.
    entailer!.
  - rewrite list_to_Z_single.
    reflexivity.
  - replace (Zabs 1) with 1 by lia.
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      unfold same_sign.
      left; split; lia.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2 : mpz_set_ui_return_wit_2.
Proof.
  aggressive_pre_process.
  assert (Hx0 : x0 = 0) by lia.
  subst x0.
  rewrite Z.abs_0.
  sep_apply_l_atomic
    (mpd_store_Z_compact_undef_tail_to_undef_split
       ptr (Zabs old) (Zabs size) 0 cap);
    try solve [entailer!].
  rewrite UIntArray.undef_full_empty.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  entailer!; simpl; try rewrite list_to_Z_nil; try unfold same_sign; try lia.
  - split_pures.
    + dump_pre_spatial.
      rewrite Z.abs_0.
      pose proof (Z.abs_nonneg size).
      lia.
  - split_pures.
    + dump_pre_spatial.
      unfold same_sign.
      left; split; lia.
Qed.
