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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_div_qr_entail_wit_30_1_nonalias_q_rem : mpz_div_qr_entail_wit_30_1_nonalias_q_rem.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH41.
    - exact PreH33.
    - exact PreH35.
    - exact PreH38.
    - exact PreH34.
    - exact PreH8.
    - exact PreH9.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH19.
    - exact PreH20. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qtr rtr.
  split_pure_spatial.
  - sep_apply
      (store_Z_to_optional_store_Z_nonzero q0_nonalias qtr).
    + sep_apply
        (store_Z_to_optional_store_Z_nonzero r0_nonalias rtr).
      * sep_apply
          (store_int_undef_store_int (&( "ns" )) tr_size).
        sep_apply
          (store_ptr_undef_store_ptr (&( "np" )) np).
        sep_apply
          (store_ptr_undef_store_ptr (&( "tr" )) tr).
        sep_apply
          (store_int_undef_store_int (&( "qs" )) qs).
        sep_apply
          (store_ptr_undef_store_ptr (&( "qp" )) qp).
        sep_apply
          (store_ptr_undef_store_ptr (&( "tq" )) tq).
        sep_apply
          (store_int_undef_store_int (&( "nn" )) nn_g).
        sep_apply
          (store_int_undef_store_int (&( "dn" )) dn_g).
        sep_apply
          (store_int_undef_store_int (&( "ds" )) d_size).
        repeat cancel.
      * assumption.
    + assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_2_nonalias_noq_rem : mpz_div_qr_entail_wit_30_2_nonalias_noq_rem.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  pose proof
    (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH11) as Hqbound.
  assert (Hqv_nonneg : 0 <= qv) by lia.
  set (qout := if Z_lt_dec qs 0 then - qv else qv).
  assert (Hqsign : same_sign_or_zero qout qs).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia.
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia. }
  assert (Hqabs : Zabs qout = qv).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - rewrite Z.abs_opp, Z.abs_eq; lia.
    - rewrite Z.abs_eq; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH38.
    - exact PreH30.
    - exact PreH32.
    - exact PreH35.
    - exact PreH31.
    - exact Hqsign.
    - exact Hqabs.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH17.
    - exact PreH18. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  subst q0_nonalias.
  Exists qout rtr.
  split_pure_spatial.
  - sep_apply
      (store_Z_to_optional_store_Z_nonzero r0_nonalias rtr).
    + normalize.
      sep_apply
        (store_int_undef_store_int (&( "ns" )) tr_size).
      sep_apply
        (store_ptr_undef_store_ptr (&( "np" )) np).
      sep_apply
        (store_ptr_undef_store_ptr (&( "tr" )) tr).
      sep_apply
        (store_int_undef_store_int (&( "nn" )) nn_g).
      sep_apply
        (store_int_undef_store_int (&( "dn" )) dn_g).
      sep_apply
        (store_ptr_undef_store_ptr (&( "qp" )) qp).
      sep_apply
        (store_int_undef_store_int (&( "qn" )) qn).
      sep_apply
        (store_int_undef_store_int (&( "ds" )) d_size).
      sep_apply
        (store_int_undef_store_int (&( "qs" )) qs).
      repeat cancel.
      apply emp_to_optional_store_Z_null.
      reflexivity.
    + assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_3_nonalias_q_rem : mpz_div_qr_entail_wit_30_3_nonalias_q_rem.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH41.
    - exact PreH33.
    - exact PreH35.
    - exact PreH38.
    - exact PreH34.
    - exact PreH8.
    - exact PreH9.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH19.
    - exact PreH20. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  subst r0_nonalias.
  Exists qtr rtr.
  split_pure_spatial.
  - sep_apply
      (store_Z_to_optional_store_Z_nonzero q0_nonalias qtr).
    + normalize.
      sep_apply
        (store_int_undef_store_int (&( "ns" )) tr_size).
      sep_apply
        (store_ptr_undef_store_ptr (&( "np" )) np).
      sep_apply
        (store_ptr_undef_store_ptr (&( "tr" )) tr).
      sep_apply
        (store_int_undef_store_int (&( "qs" )) qs).
      sep_apply
        (store_ptr_undef_store_ptr (&( "qp" )) qp).
      sep_apply
        (store_ptr_undef_store_ptr (&( "tq" )) tq).
      sep_apply
        (store_int_undef_store_int (&( "nn" )) nn_g).
      sep_apply
        (store_int_undef_store_int (&( "dn" )) dn_g).
      sep_apply
        (store_int_undef_store_int (&( "ds" )) d_size).
      repeat cancel.
      apply emp_to_optional_store_Z_null.
      reflexivity.
    + assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_4_nonalias_noq_rem : mpz_div_qr_entail_wit_30_4_nonalias_noq_rem.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  pose proof
    (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH11) as Hqbound.
  assert (Hqv_nonneg : 0 <= qv) by lia.
  set (qout := if Z_lt_dec qs 0 then - qv else qv).
  assert (Hqsign : same_sign_or_zero qout qs).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia.
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia. }
  assert (Hqabs : Zabs qout = qv).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - rewrite Z.abs_opp, Z.abs_eq; lia.
    - rewrite Z.abs_eq; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH38.
    - exact PreH30.
    - exact PreH32.
    - exact PreH35.
    - exact PreH31.
    - exact Hqsign.
    - exact Hqabs.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH17.
    - exact PreH18. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  subst q0_nonalias.
  subst r0_nonalias.
  Exists qout rtr.
  split_pure_spatial.
  - normalize.
    sep_apply
      (store_int_undef_store_int (&( "ns" )) tr_size).
    sep_apply
      (store_ptr_undef_store_ptr (&( "np" )) np).
    sep_apply
      (store_ptr_undef_store_ptr (&( "tr" )) tr).
    sep_apply
      (store_int_undef_store_int (&( "nn" )) nn_g).
    sep_apply
      (store_int_undef_store_int (&( "dn" )) dn_g).
    sep_apply
      (store_ptr_undef_store_ptr (&( "qp" )) qp).
    sep_apply
      (store_int_undef_store_int (&( "qn" )) qn).
    sep_apply
      (store_int_undef_store_int (&( "ds" )) d_size).
    sep_apply
      (store_int_undef_store_int (&( "qs" )) qs).
    repeat cancel.
    sep_apply_right
      (emp_to_optional_store_Z_null 0 qout eq_refl).
    sep_apply_right
      (emp_to_optional_store_Z_null 0 rtr eq_refl).
    normalize.
    cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_31_1_r_eq_n_q_rem : mpz_div_qr_entail_wit_31_1_r_eq_n_q_rem.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst zd_g.
  subst r0_r_eq_n_read0.
  assert (Habsdiv :
    Zabs zn_r_eq_n_read0 = qv * Zabs zd_r_eq_n_read0 + rv) by lia.
  assert (Hmod : rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Hzn_nonzero : zn_r_eq_n_read0 <> 0).
  { assert (Hnn_pos : 0 < nn_g) by lia.
    pose proof (is_compact_Z_size_pos_value_pos
      (Zabs zn_r_eq_n_read0) nn_g PreH33 Hnn_pos) as Habs_pos.
    intro Hzero; subst zn_r_eq_n_read0; cbn in Habs_pos; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qtr rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH42.
    - exact Hzn_nonzero.
    - exact PreH36.
    - exact PreH39.
    - exact PreH35.
    - exact PreH8.
    - exact PreH9.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH19.
    - exact PreH20. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qtr rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qtr rtr.
  split_pure_spatial.
  - sep_apply
      (store_Z_to_optional_store_Z_nonzero q0_r_eq_n_read0 qtr).
    + normalize.
      sep_apply
        (store_int_undef_store_int (&( "ns" )) tr_size).
      sep_apply
        (store_ptr_undef_store_ptr (&( "np" )) np).
      sep_apply
        (store_ptr_undef_store_ptr (&( "tr" )) tr).
      sep_apply
        (store_int_undef_store_int (&( "qs" )) qs).
      sep_apply
        (store_ptr_undef_store_ptr (&( "qp" )) qp).
      sep_apply
        (store_ptr_undef_store_ptr (&( "tq" )) tq).
      sep_apply
        (store_int_undef_store_int (&( "nn" )) nn_g).
      sep_apply
        (store_int_undef_store_int (&( "dn" )) dn_g).
      sep_apply
        (store_int_undef_store_int (&( "ds" )) d_size).
      repeat cancel.
    + assumption.
  - split_pures; dump_pre_spatial; try assumption; reflexivity.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_31_2_r_eq_n_noq_rem : mpz_div_qr_entail_wit_31_2_r_eq_n_noq_rem.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst zd_g.
  subst r0_r_eq_n_read0.
  assert (Habsdiv :
    Zabs zn_r_eq_n_read0 = qv * Zabs zd_r_eq_n_read0 + rv) by lia.
  assert (Hmod : rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Hzn_nonzero : zn_r_eq_n_read0 <> 0).
  { assert (Hnn_pos : 0 < nn_g) by lia.
    pose proof (is_compact_Z_size_pos_value_pos
      (Zabs zn_r_eq_n_read0) nn_g PreH30 Hnn_pos) as Habs_pos.
    intro Hzero; subst zn_r_eq_n_read0; cbn in Habs_pos; lia. }
  pose proof
    (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH11) as Hqbound.
  assert (Hqv_nonneg : 0 <= qv) by lia.
  set (qout := if Z_lt_dec qs 0 then - qv else qv).
  assert (Hqsign : same_sign_or_zero qout qs).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia.
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia. }
  assert (Hqabs : Zabs qout = qv).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - rewrite Z.abs_opp, Z.abs_eq; lia.
    - rewrite Z.abs_eq; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qout rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH39.
    - exact Hzn_nonzero.
    - exact PreH33.
    - exact PreH36.
    - exact PreH32.
    - exact Hqsign.
    - exact Hqabs.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH17.
    - exact PreH18. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qout rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  subst q0_r_eq_n_read0.
  Exists qout rtr.
  split_pure_spatial.
  - normalize.
    sep_apply
      (store_int_undef_store_int (&( "ns" )) tr_size).
    sep_apply
      (store_ptr_undef_store_ptr (&( "np" )) np).
    sep_apply
      (store_ptr_undef_store_ptr (&( "tr" )) tr).
    sep_apply
      (store_int_undef_store_int (&( "nn" )) nn_g).
    sep_apply
      (store_int_undef_store_int (&( "dn" )) dn_g).
    sep_apply
      (store_ptr_undef_store_ptr (&( "qp" )) qp).
    sep_apply
      (store_int_undef_store_int (&( "qn" )) qn).
    sep_apply
      (store_int_undef_store_int (&( "ds" )) d_size).
    sep_apply
      (store_int_undef_store_int (&( "qs" )) qs).
    repeat cancel.
    apply emp_to_optional_store_Z_null.
    reflexivity.
  - split_pures; dump_pre_spatial; try assumption; reflexivity.
Qed.
