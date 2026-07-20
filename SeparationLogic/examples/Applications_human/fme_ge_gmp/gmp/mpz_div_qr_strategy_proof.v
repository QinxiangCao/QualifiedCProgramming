Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_div_qr_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma mpz_div_qr_strategy1_correctness : mpz_div_qr_strategy1.
Proof.
  pre_process_default.
  Intros_r v used store_cap.
  apply_sepcon_adjoint.
  pre_process_default.
  sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve p full_cap l).
  Intros_p Hbound.
  prop_apply (UIntArray.full_Zlength p full_cap l).
  Intros_p Hlen.
  sep_apply_l_atomic (UIntArray.full_split_to_seg p used full_cap l).
  - entailer!.
  - sep_apply_l_atomic (UIntArray.seg_to_undef_seg p used full_cap (sublist used full_cap l)).
    sep_apply_l_atomic (UIntArray.seg_to_full p 0 used (sublist 0 used l)).
    replace (p + 0 * sizeof(UINT)) with p by lia.
    replace (used - 0) with used by lia.
    assert (Hprefix_len : Zlength (sublist 0 used l) = used).
    { rewrite Zlength_sublist; lia. }
    assert (Hprefix_bound : list_within_bound UINT_MOD (sublist 0 used l)).
    { eapply (list_within_bound_sublist UINT_MOD l 0 used); try lia; exact Hbound. }
    sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_compact p used (sublist 0 used l) v); try assumption.
    rewrite H1.
    entailer!.
    entailer!.
    entailer!.
    entailer!.
    rewrite H1.
    entailer!.
Qed.

Lemma mpz_div_qr_strategy2_correctness : mpz_div_qr_strategy2.
Proof.
  pre_process_default.
  pre_process_default.
  subst.
  entailer!.
Qed.

Lemma mpz_div_qr_strategy3_correctness : mpz_div_qr_strategy3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.seg_to_undef_seg p lo hi l).
  entailer!.
Qed.

Lemma mpz_div_qr_strategy4_correctness : mpz_div_qr_strategy4.
Proof.
  pre_process_default.
  pre_process_default.
  subst.
  sep_apply_l_atomic (UIntArray.seg_to_undef_seg p lo hi l).
  sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg p lo hi z_goal).
  - entailer!.
  - sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg p x_goal lo z_goal).
    + entailer!.
    + entailer!.
Qed.
