Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Proof.
  unfold mpz_clear_return_wit_2.
  right.
  intros n ptr_2 size_2 cap_2 PreH1 PreH2 PreH3.
  subst cap_2.
  assert (Hsize_abs: Zabs size_2 = 0) by lia.
  rewrite Hsize_abs.
  rewrite UIntArray.undef_seg_empty.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  assert (data = nil).
  { apply Zlength_nil_inv. lia. }
  subst data.
  rewrite UIntArray.full_empty.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Proof.
  unfold mpz_realloc_return_wit_1.
  left.
  intros size_pre r_pre n cap old ptr retval_2 retval retval_3
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  assert (Hold_zero: old = 0) by lia.
  subst old.
  Exists retval_2.
  rewrite PreH3.
  entailer!.
  sep_apply (UIntArray.undef_full_to_undef_seg retval); try lia.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l.
  assert (l = nil).
  { apply Zlength_nil_inv. lia. }
  subst l.
  rewrite UIntArray.full_empty.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  try rewrite UIntArray.undef_seg_empty.
  entailer!.
  rewrite PreH10.
  change (Zabs 0) with 0.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
  all: try lia; try tauto.
Qed.

Lemma proof_of_mpz_realloc_return_wit_3 : mpz_realloc_return_wit_3.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_return_wit_4 : mpz_realloc_return_wit_4.
Proof.
  unfold mpz_realloc_return_wit_4.
  left.
  intros size_pre r_pre n cap old retval_2 retval retval_3
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  exfalso.
  subst retval_3 retval_2.
  assert (cap > 0) by lia.
  assert (Z.max size_pre 1 = size_pre) by lia.
  lia.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_2_pure : mpz_realloc_partial_solve_wit_2_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Proof.
  pre_process.
  Exists cap.
  assert (Z.max (Z.max n_pre 1) cap = cap) as Hmax.
  {
    apply Zmax_right.
    apply Z.max_lub; lia.
  }
  rewrite Hmax.
  entailer!.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Proof.
  pre_process.
  Exists r_callee__mp_alloc.
  assert (Z.max (Z.max n_pre 1) cap = Z.max n_pre 1) as Hmax.
  {
    apply Zmax_left.
    lia.
  }
  rewrite Hmax.
  entailer!.
Qed.

Lemma proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Proof. 
  pre_process. 
  unfold store_Z.
  Exists ptr size cap.
  entailer!.
  unfold same_sign in PreH3.
  destruct PreH3 as [[_ Hsize_nonneg] | [Hn_neg _]]; [lia | exact Hn_neg].
Qed.

Lemma proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Proof.
  pre_process. 
  unfold store_Z.
  Exists ptr size cap.
  replace (Zabs size) with size by lia.
  subst size.
  prop_apply (mpd_store_Z_compact_zero) ; try lia.
  Intros.
  assert (n = 0) by lia.
  replace (Zabs n) with n by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Proof.
  pre_process. 
  unfold store_Z.
  Exists ptr size cap.
  replace (Zabs size) with size by lia.
  prop_apply (mpd_store_Z_compact_pos); try lia.
  Intros.
  assert (Hn_pos: n > 0).
  { unfold same_sign in PreH3.
    match goal with
    | [ Habs_pos : Zabs n > 0 |- _ ] =>
        destruct PreH3 as [[Hn_nonneg _] | [_ Hsize_neg]]; lia
    end. }
  replace (Zabs n) with n by lia.
  entailer!.
  unfold UINT_MOD; lia.
Qed.
