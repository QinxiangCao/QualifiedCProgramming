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
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_mpz_abs_add_safety_wit_1 : mpz_abs_add_safety_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_range UINT_MOD aptr (Zabs n_new) an).
  Intros.
  match goal with
  | H : 0 <= an <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_1 : mpz_abs_add_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z at 1.
  Intros rptr rsize rcap.
  Exists rptr; Exists ptr; Exists ptr_2; Exists rcap; Exists rsize.
  Exists cap; Exists cap_2; Exists size; Exists size_2; Exists m; Exists n.
  subst retval retval_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption.
    apply perm_swap.
    all: try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_2 : mpz_abs_add_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z at 1.
  Intros rptr rsize rcap.
  Exists rptr; Exists ptr_2; Exists ptr; Exists rcap; Exists rsize.
  Exists cap_2; Exists cap; Exists size_2; Exists size; Exists n; Exists m.
  subst retval retval_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2 : mpz_abs_add_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l) (Zabs rsize_2) an
    (Z.max (Z.max (an + 1) 1) rcap_2)); try lia.
  Intros_p Hcompact.
  Exists bptr_2; Exists aptr_2; Exists retval; Exists z_callee__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists bcap_2; Exists acap_2.
  Exists bsize_2; Exists asize_2; Exists n_new_2; Exists m_new_2.
  split_pure_spatial.
  - cancel (UIntArray.undef_full retval an).
    cancel (UIntArray.undef_seg retval an
      (Z.max (Z.max (an + 1) 1) rcap_2)).
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_1 : mpz_abs_add_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (mpn_add_ret_0_or_1 aptr bptr rp (Zabs n_new) (Zabs m_new) val_r_out an bn retval
    ltac:(lia) ltac:(lia)) as Hadd_ret.
  prop_apply Hadd_ret.
  Intros.
  prop_apply (store_int_range (&( r_pre # "__mpz_struct" ->ₛ "_mp_alloc"))).
  Intros.
  match goal with
  | Halloc : Int.min_signed <= r__mp_alloc <= Int.max_signed,
    Hz : r__mp_alloc = Z.max (Z.max (an + 1) 1) rcap |- _ =>
      assert (Han_int : an <= Int.max_signed) by (rewrite Hz in Halloc; lia)
  end.
  match goal with
  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval
  end.
  - assert (Hsize_ret : signed_last_nbits (unsigned_last_nbits an 32 + 0) 32 = an).
    {
      match goal with
      | Hc : is_compact_Z UINT_MOD (Zabs n_new) an |- _ =>
          pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an Hc)
            as [Han_nonneg _]
      end.
      assert (Han_u32 : 0 <= an < 2 ^ 32)
        by (change (2 ^ 32) with 4294967296; change Int.max_signed with 2147483647 in Han_int; lia).
      assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))
        by (change (2 ^ (32 - 1)) with 2147483648; change Int.max_signed with 2147483647 in Han_int; lia).
      rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
      replace (an + 0) with an by lia.
      rewrite signed_last_nbits_eq.
      2:{ lia. }
      2:{ exact Han_s32. }
      lia.
    }
    prop_apply (mpd_store_Z_bound rp val_r_out an).
    Intros.
    assert (Hcompact_r : is_compact_Z UINT_MOD val_r_out an).
    {
      replace val_r_out with (Zabs n_new + Zabs m_new) by lia.
      replace an with (Z.max an bn) by lia.
      eapply is_compact_Z_add_0.
      - eassumption.
      - eassumption.
      - rewrite Z.max_l by lia; lia.
    }
    match goal with
    | Hperm : Permutation (Prod2 a n_new :: Prod2 b m_new :: nil)
                          (Prod2 a_pre n :: Prod2 b_pre m :: nil) |- _ =>
        pose proof (Permutation_length_2 Hperm) as HP
    end.
    destruct HP as [[Hpair1 Hpair2] | [Hpair1 Hpair2]].
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs an) with an by lia.
      replace (Zabs (Zabs n_new + Zabs m_new)) with (Zabs n_new + Zabs m_new) by lia.
      replace (Zabs n_new + Zabs m_new) with val_r_out by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp val_r_out an);
        try assumption.
      sep_apply (store_uint_undef_store_uint (rp + an * sizeof ( UINT )) 0);
        try lia.
      sep_apply (UIntArray.undef_seg_single rp an); try lia.
      sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
      rewrite PreH15, PreH16.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try (unfold same_sign; left; lia); lia.
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs an) with an by lia.
      replace (Zabs (Zabs m_new + Zabs n_new)) with (Zabs m_new + Zabs n_new) by lia.
      replace (Zabs m_new + Zabs n_new) with val_r_out by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp val_r_out an);
        try assumption.
      sep_apply (store_uint_undef_store_uint (rp + an * sizeof ( UINT )) 0);
        try lia.
      sep_apply (UIntArray.undef_seg_single rp an); try lia.
      sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
      rewrite PreH15, PreH16.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try (unfold same_sign; left; lia); lia.
  - assert (Han1 : an + 1 <= Int.max_signed).
    {
      match goal with
      | Halloc : Int.min_signed <= r__mp_alloc <= Int.max_signed,
        Hz : r__mp_alloc = Z.max (Z.max (an + 1) 1) rcap |- _ =>
          rewrite Hz in Halloc; lia
      end.
    }
    assert (Hsize_ret : signed_last_nbits (unsigned_last_nbits an 32 + 1) 32 = an + 1).
    {
      match goal with
      | Hc : is_compact_Z UINT_MOD (Zabs n_new) an |- _ =>
          pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an Hc)
            as [Han_nonneg _]
      end.
      assert (Han_u32 : 0 <= an < 2 ^ 32)
        by (change (2 ^ 32) with 4294967296; change Int.max_signed with 2147483647 in Han_int; lia).
      assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))
        by (change (2 ^ (32 - 1)) with 2147483648; change Int.max_signed with 2147483647 in Han1; lia).
      rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
      rewrite signed_last_nbits_eq.
      2:{ lia. }
      2:{ exact Han1_s32. }
      lia.
    }
    match goal with
    | Hperm : Permutation (Prod2 a n_new :: Prod2 b m_new :: nil)
                          (Prod2 a_pre n :: Prod2 b_pre m :: nil) |- _ =>
        pose proof (Permutation_length_2 Hperm) as HP
    end.
    destruct HP as [[Hpair1 Hpair2] | [Hpair1 Hpair2]].
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs (an + 1)) with (an + 1) by lia.
      replace (Zabs (Zabs n_new + Zabs m_new)) with (Zabs n_new + Zabs m_new) by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_append_one_compact rp val_r_out an).
      replace (val_r_out + UINT_MOD ^ an) with (Zabs n_new + Zabs m_new) by lia.
      rewrite PreH15, PreH16.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try lia.
        unfold same_sign; left.
        pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an PreH3)
          as [Han_nonneg _].
        pose proof (Z.pow_pos_nonneg UINT_MOD an UINT_MOD_pos (Z.ge_le _ _ Han_nonneg)).
        lia.
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs (an + 1)) with (an + 1) by lia.
      replace (Zabs (Zabs m_new + Zabs n_new)) with (Zabs m_new + Zabs n_new) by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_append_one_compact rp val_r_out an).
      replace (val_r_out + UINT_MOD ^ an) with (Zabs m_new + Zabs n_new) by lia.
      rewrite PreH15, PreH16.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try lia.
        unfold same_sign; left.
        pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an PreH3)
          as [Han_nonneg _].
        pose proof (Z.pow_pos_nonneg UINT_MOD an UINT_MOD_pos (Z.ge_le _ _ Han_nonneg)).
        lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_2_pure : mpz_abs_add_partial_solve_wit_2_pure.
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

Lemma proof_of_mpz_abs_add_partial_solve_wit_4_pure : mpz_abs_add_partial_solve_wit_4_pure.
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

Lemma proof_of_mpz_abs_add_partial_solve_wit_7_pure : mpz_abs_add_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | |- context[mpd_store_Z_compact UINT_MOD ?ptr ?v ?size] =>
      prop_apply (mpd_store_Z_compact_range UINT_MOD ptr v size)
  end.
  Intros.
  match goal with
  | H : 0 <= ?size <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  prop_apply (store_int_range (&( r_pre # "__mpz_struct" ->ₛ "_mp_alloc"))).
  Intros.
  match goal with
  | H : Int.min_signed <= rcap <= Int.max_signed |- _ =>
      change Int.max_signed with 2147483647 in H
  end.
  split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_8_pure : mpz_abs_add_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
