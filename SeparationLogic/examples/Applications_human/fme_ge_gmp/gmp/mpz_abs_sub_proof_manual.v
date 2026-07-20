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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_sub_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_sub_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_sub_entail_wit_1 : mpz_abs_sub_entail_wit_1.
Proof.
  pre_process.
  unfold store_Z.
  Intros rptr rsize rcap bptr bsize bcap.
  Exists bptr rptr bcap rcap bsize rsize.
  pre_process.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_size")) rsize).
  Intros.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  match goal with
  | H : Int.min_signed <= rsize <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= rcap <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= bsize <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= bcap <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_2 : mpz_abs_sub_entail_wit_2.
Proof.
  pre_process.
  rewrite <- PreH6.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_3 : mpz_abs_sub_entail_wit_3.
Proof.
  pre_process.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&( "cmp")) cmp).
  Intros.
  prop_apply (store_int_range (&( "an")) an).
  Intros.
  prop_apply (store_int_range (&( "bn")) bn).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr (Zabs za_r_eq_a) (Zabs rsize)).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs za_r_eq_a) (Zabs rsize) |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs za_r_eq_a) (Zabs rsize) Hc ltac:(pose proof (Z.abs_nonneg zb_r_eq_a); lia))
  end.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_4 : mpz_abs_sub_entail_wit_4.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_6 : mpz_abs_sub_entail_wit_6.
Proof.
  pre_process.
  subst a_pre.
  Exists z_callee__mp_alloc.
  replace an with (Zabs rsize) by lia.
  replace z_callee__mp_alloc with (Z.max (Z.max (Zabs rsize) 1) rcap) by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_7 : mpz_abs_sub_entail_wit_7.
Proof.
  pre_process.
  rewrite <- PreH7.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_8 : mpz_abs_sub_entail_wit_8.
Proof.
  pre_process.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&( "cmp")) cmp).
  Intros.
  prop_apply (store_int_range (&( "an")) an).
  Intros.
  prop_apply (store_int_range (&( "bn")) bn).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z bptr (Zabs zb_r_eq_a) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs zb_r_eq_a) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs zb_r_eq_a) bn Hc ltac:(pose proof (Z.abs_nonneg za_r_eq_a); lia))
  end.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_9 : mpz_abs_sub_entail_wit_9.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_11 : mpz_abs_sub_entail_wit_11.
Proof.
  pre_process.
  subst a_pre.
  Exists z_callee__mp_alloc.
  replace an with (Zabs rsize) by lia.
  replace z_callee__mp_alloc with (Z.max (Z.max bn 1) rcap) by lia.
  prop_apply (mpd_store_Z_compact_mono_size
    bptr retval (Zabs zb_r_eq_a) (Zabs za_r_eq_a) bn (Zabs rsize) ltac:(lia)).
  Intros.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg retval (Zabs rsize) bn (Z.max (Z.max bn 1) rcap)); try lia.
  entailer!.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_1 : mpz_abs_sub_return_wit_1.
Proof.
  pre_process.
  subst a_pre.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split rptr (Zabs za_r_eq_a) (Zabs rsize) 0 rcap); try lia.
  Intros.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr rsize rcap.
  Exists bptr bsize bcap.
  replace (Zabs za_r_eq_a - Zabs zb_r_eq_a) with 0 by lia.
  replace (Zabs 0) with 0 by lia.
  rewrite UIntArray.undef_full_empty.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  Exists data (@nil Z).
  rewrite UIntArray.full_empty.
  pre_process.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try apply same_sign_refl; try (unfold same_sign; lia); try lia.
  all: try (rewrite list_to_Z_nil; simpl; lia).
  all: rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_2 : mpz_abs_sub_return_wit_2.
Proof.
  pre_process.
  subst a.
  subst r_pre.
  pose proof (is_compact_Z_mono_size (Zabs zb_r_eq_a) (Zabs za_r_eq_a) bn an ltac:(lia) PreH4 PreH5).
  prop_apply (mpn_sub_ret_0_compact rptr_new (Zabs zb_r_eq_a) (Zabs za_r_eq_a) val_r_out bn an retval retval_2).
  Intros.
  all: try assumption; try lia.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr_new val_r_out retval).
  Intros.
  sep_apply_l_atomic (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn PreH4).
  match goal with
  | Hc : is_compact_Z UINT_MOD val_r_out retval |- _ =>
      pose proof (is_compact_Z_positive_size val_r_out retval Hc ltac:(lia))
  end.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg rptr_new retval bn rcap_new); try lia.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  Exists bptr bsize bcap.
  replace val_r_out with (Zabs zb_r_eq_a - Zabs za_r_eq_a) by lia.
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs zb_r_eq_a - Zabs za_r_eq_a) by lia.
  replace (Zabs (- retval)) with retval by lia.
  replace (Zabs bsize) with bn by lia.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try (unfold same_sign; right; lia); lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_3 : mpz_abs_sub_return_wit_3.
Proof.
  pre_process.
  subst a.
  subst r_pre.
  pose proof (is_compact_Z_mono_size (Zabs za_r_eq_a) (Zabs zb_r_eq_a) an bn ltac:(lia) PreH5 PreH4).
  prop_apply (mpn_sub_ret_0_compact rptr_new (Zabs za_r_eq_a) (Zabs zb_r_eq_a) val_r_out an bn retval retval_2).
  Intros.
  all: try assumption; try lia.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr_new val_r_out retval).
  Intros.
  sep_apply_l_atomic (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn PreH4).
  match goal with
  | Hc : is_compact_Z UINT_MOD val_r_out retval |- _ =>
      pose proof (is_compact_Z_positive_size val_r_out retval Hc ltac:(lia))
  end.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg rptr_new retval an rcap_new); try lia.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  Exists bptr bsize bcap.
  replace val_r_out with (Zabs za_r_eq_a - Zabs zb_r_eq_a) by lia.
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs za_r_eq_a - Zabs zb_r_eq_a) by lia.
  replace (Zabs retval) with retval by lia.
  replace (Zabs bsize) with bn by lia.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_3_pure : mpz_abs_sub_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_pure : mpz_abs_sub_partial_solve_wit_5_pure.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_compact_mono_size
    rptr_new bptr (Zabs za_r_eq_a) (Zabs zb_r_eq_a) an bn ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr_new (Zabs za_r_eq_a) an).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs za_r_eq_a) an |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs za_r_eq_a) an Hc ltac:(pose proof (Z.abs_nonneg zb_r_eq_a); lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_6_pure : mpz_abs_sub_partial_solve_wit_6_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_pure : mpz_abs_sub_partial_solve_wit_8_pure.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_compact_mono_size
    bptr rptr_new (Zabs zb_r_eq_a) (Zabs za_r_eq_a) bn an ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z bptr (Zabs zb_r_eq_a) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs zb_r_eq_a) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs zb_r_eq_a) bn Hc ltac:(pose proof (Z.abs_nonneg za_r_eq_a); lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9_pure : mpz_abs_sub_partial_solve_wit_9_pure.
Proof.
  pre_process.
Qed.
