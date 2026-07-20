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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_2_preinv_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_2_preinv_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_1_1 : mpn_div_qr_2_preinv_entail_wit_1_1.
Proof.
  pre_process.
  unfold store_div_inverse, div_inverse_store.
  Intros shift d1 d0 di.
  Exists di d0 d1 shift.
  rewrite PreH1, PreH2, PreH3, PreH4.
  split_pure_spatial.
  - cancel ((&("nn")) # Int |-> nn_pre).
    cancel ((&("qp")) # Ptr |-> qp_pre).
    cancel ((&("np")) # Ptr |-> np_pre).
    cancel ((&("inv")) # Ptr |-> inv_pre).
    cancel (UIntArray.undef_full qp_pre (nn_pre - 1)).
    cancel (UIntArray.full np_pre nn_pre l_np_bare).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"di") # UInt |-> di).
  - unfold gmp_div_inverse_valid, div_inverse_den in H.
    destruct H as [Hdn [Hdpos [Hshift [Hd1 [Hd0 [Hdi [Hsmall [Hrepr [Hhalf [Hlo Hhi]]]]]]]]]].
    destruct Hrepr as [[Hbad _] | [Hdn_gt Hrepr]]; [lia|].
    destruct (Z.eq_dec 2 1) as [Heq|Hneq]; [lia|].
    change (2 - 2) with 0 in Hrepr.
    rewrite Z.pow_0_r in Hrepr.
    rewrite Z.div_1_r in Hrepr.
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_1_2 : mpn_div_qr_2_preinv_entail_wit_1_2.
Proof.
  pre_process.
  unfold store_div_inverse, div_inverse_store.
  Intros shift d1 d0 di.
  Exists di d0 d1 shift.
  rewrite PreH1, PreH2, PreH3, PreH4.
  split_pure_spatial.
  - cancel ((&("nn")) # Int |-> nn_pre).
    cancel ((&("qp")) # Ptr |-> qp_pre).
    cancel ((&("np")) # Ptr |-> np_pre).
    cancel ((&("inv")) # Ptr |-> inv_pre).
    cancel (UIntArray.full np_pre nn_pre l_np_bare).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0).
    cancel (&(inv_pre # "gmp_div_inverse" ->ₛ"di") # UInt |-> di).
  - unfold gmp_div_inverse_valid, div_inverse_den in H.
    destruct H as [Hdn [Hdpos [Hshift [Hd1 [Hd0 [Hdi [Hsmall [Hrepr [Hhalf [Hlo Hhi]]]]]]]]]].
    destruct Hrepr as [[Hbad _] | [Hdn_gt Hrepr]]; [lia|].
    destruct (Z.eq_dec 2 1) as [Heq|Hneq]; [lia|].
    change (2 - 2) with 0 in Hrepr.
    rewrite Z.pow_0_r in Hrepr.
    rewrite Z.div_1_r in Hrepr.
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_2_1 : mpn_div_qr_2_preinv_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hretval_nonneg : 0 <= retval).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (Hnotneg : ~ retval < 0).
    {
      intro Hneg.
      assert (Hle : retval <= -1) by lia.
      assert (Hmul : retval * P <= -1 * P) by (apply Z.mul_le_mono_nonneg_r; lia).
      replace (-1 * P) with (- P) in Hmul by ring.
      assert (Hlhs_neg : B + retval * P < P + (- P))
        by (apply Z.add_lt_le_mono; [exact Hout_lt | exact Hmul]).
      replace (P + - P) with 0 in Hlhs_neg by ring.
      assert (Hrhs_nonneg : 0 <= A * S) by (apply Z.mul_nonneg_nonneg; lia).
      rewrite PreH3 in Hlhs_neg.
      lia.
    }
    lia.
  }
  assert (Hretval_lt_S : retval < 2 ^ shift_orig).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    rewrite PreH19 in Hnp_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (HretP_le : retval * P <= A * S) by (rewrite <- PreH3; lia).
    assert (HAS_lt : A * S < P * S)
      by (apply (proj1 (Z.mul_lt_mono_pos_r S A P HS)); exact Hnp_lt).
    apply (proj2 (Z.mul_lt_mono_pos_r P retval S HU)).
    replace (S * P) with (P * S) by ring.
    eapply Z.le_lt_trans; [exact HretP_le | exact HAS_lt].
  }
  assert (Hretval_lt_d1 : retval < d1_orig).
  {
    assert (Hpow_le : 2 ^ shift_orig <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
    assert (Hhalf_le : 2 ^ 31 <= d1_orig).
    {
      change (2 ^ 31) with 2147483648.
      change UINT_MOD with 4294967296 in PreH11.
      change (4294967296 ÷ 2) with 2147483648 in PreH11.
      exact PreH11.
    }
    lia.
  }
  assert (Htop_bound : 0 <= Znth (nn0_bare - 1) l_out 0 <= UINT_MAX).
  {
    pose proof (list_within_bound_Znth_bound UINT_MOD l_out (nn0_bare - 1)) as Hbound.
    specialize (Hbound ltac:(rewrite PreH1; lia) PreH2).
    change UINT_MOD with 4294967296 in Hbound.
    change UINT_MAX with 4294967295.
    lia.
  }
  assert (Hretval_uint : retval <= UINT_MAX) by (change UINT_MAX with 4294967295; lia).
  assert (Hrem_nonneg : 0 <= retval * UINT_MOD + Znth (nn0_bare - 1) l_out 0).
  {
    apply Z.add_nonneg_nonneg.
    - apply Z.mul_nonneg_nonneg.
      + exact Hretval_nonneg.
      + change UINT_MOD with 4294967296; lia.
    - lia.
  }
  assert (Hrem_lt : retval * UINT_MOD + Znth (nn0_bare - 1) l_out 0 < d1_orig * UINT_MOD + d0_orig).
  {
    change UINT_MOD with 4294967296.
    change UINT_MAX with 4294967295 in Htop_bound.
    lia.
  }
  Exists retval (retval * UINT_MOD + Znth (nn0_bare - 1) l_out 0) 0 (@nil Z) l_out.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg qp0_bare (nn0_bare - 1)).
    replace (nn0_bare - 2 + 1) with (nn0_bare - 1) by ring.
    rewrite (UIntArray.seg_empty qp0_bare (nn0_bare - 1) (nn0_bare - 1)).
    cancel (UIntArray.full np0_bare nn0_bare l_out).
    cancel (UIntArray.undef_seg qp0_bare 0 (nn0_bare - 1)).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
    split_pure_spatial.
    + cancel emp.
    + apply derivable1s_coq_prop_r; reflexivity.
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_nil; lia.
    + replace (nn0_bare - 2 + 1) with (nn0_bare - 1) by ring;
      assert (Hsub : sublist (nn0_bare - 1) nn0_bare l_out =
                     Znth (nn0_bare - 1) l_out 0 :: nil)
        by (replace (sublist (nn0_bare - 1) nn0_bare l_out)
              with (sublist (nn0_bare - 1) (nn0_bare - 1 + 1) l_out)
              by (f_equal; ring);
            apply sublist_single; rewrite PreH1; lia);
      replace (nn0_bare - (nn0_bare - 1)) with 1 by ring;
      change (UINT_MOD ^ 1) with UINT_MOD;
      rewrite Hsub; simpl; rewrite list_to_Z_cons; rewrite list_to_Z_nil; ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_2_2 : mpn_div_qr_2_preinv_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hretval_nonneg : 0 <= retval).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (Hnotneg : ~ retval < 0).
    {
      intro Hneg.
      assert (Hle : retval <= -1) by lia.
      assert (Hmul : retval * P <= -1 * P) by (apply Z.mul_le_mono_nonneg_r; lia).
      replace (-1 * P) with (- P) in Hmul by ring.
      assert (Hlhs_neg : B + retval * P < P + (- P))
        by (apply Z.add_lt_le_mono; [exact Hout_lt | exact Hmul]).
      replace (P + - P) with 0 in Hlhs_neg by ring.
      assert (Hrhs_nonneg : 0 <= A * S) by (apply Z.mul_nonneg_nonneg; lia).
      rewrite PreH3 in Hlhs_neg.
      lia.
    }
    lia.
  }
  assert (Hretval_lt_S : retval < 2 ^ shift_orig).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    rewrite PreH19 in Hnp_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (HretP_le : retval * P <= A * S) by (rewrite <- PreH3; lia).
    assert (HAS_lt : A * S < P * S)
      by (apply (proj1 (Z.mul_lt_mono_pos_r S A P HS)); exact Hnp_lt).
    apply (proj2 (Z.mul_lt_mono_pos_r P retval S HU)).
    replace (S * P) with (P * S) by ring.
    eapply Z.le_lt_trans; [exact HretP_le | exact HAS_lt].
  }
  assert (Hretval_lt_d1 : retval < d1_orig).
  {
    assert (Hpow_le : 2 ^ shift_orig <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
    assert (Hhalf_le : 2 ^ 31 <= d1_orig).
    {
      change (2 ^ 31) with 2147483648.
      change UINT_MOD with 4294967296 in PreH11.
      change (4294967296 ÷ 2) with 2147483648 in PreH11.
      exact PreH11.
    }
    lia.
  }
  assert (Htop_bound : 0 <= Znth (nn0_bare - 1) l_out 0 <= UINT_MAX).
  {
    pose proof (list_within_bound_Znth_bound UINT_MOD l_out (nn0_bare - 1)) as Hbound.
    specialize (Hbound ltac:(rewrite PreH1; lia) PreH2).
    change UINT_MOD with 4294967296 in Hbound.
    change UINT_MAX with 4294967295.
    lia.
  }
  assert (Hretval_uint : retval <= UINT_MAX) by (change UINT_MAX with 4294967295; lia).
  assert (Hrem_nonneg : 0 <= retval * UINT_MOD + Znth (nn0_bare - 1) l_out 0).
  {
    apply Z.add_nonneg_nonneg.
    - apply Z.mul_nonneg_nonneg.
      + exact Hretval_nonneg.
      + change UINT_MOD with 4294967296; lia.
    - lia.
  }
  assert (Hrem_lt : retval * UINT_MOD + Znth (nn0_bare - 1) l_out 0 < d1_orig * UINT_MOD + d0_orig).
  {
    change UINT_MOD with 4294967296.
    change UINT_MAX with 4294967295 in Htop_bound.
    lia.
  }
  Exists retval (retval * UINT_MOD + Znth (nn0_bare - 1) l_out 0) 0 (@nil Z) l_out.
  split_pure_spatial.
  -
    cancel (UIntArray.full np0_bare nn0_bare l_out).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_nil; lia.
    + replace (nn0_bare - 2 + 1) with (nn0_bare - 1) by ring;
      assert (Hsub : sublist (nn0_bare - 1) nn0_bare l_out =
                     Znth (nn0_bare - 1) l_out 0 :: nil)
        by (replace (sublist (nn0_bare - 1) nn0_bare l_out)
              with (sublist (nn0_bare - 1) (nn0_bare - 1 + 1) l_out)
              by (f_equal; ring);
            apply sublist_single; rewrite PreH1; lia);
      replace (nn0_bare - (nn0_bare - 1)) with 1 by ring;
      change (UINT_MOD ^ 1) with UINT_MOD;
      rewrite Hsub; simpl; rewrite list_to_Z_cons; rewrite list_to_Z_nil; ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_2_3 : mpn_div_qr_2_preinv_entail_wit_2_3.
Proof.
  pre_process.
  Exists 0 (Znth (nn0_bare - 1) l_np_bare 0) 0 (@nil Z) l_np_bare.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg qp0_bare (nn0_bare - 1)).
    replace (nn0_bare - 2 + 1) with (nn0_bare - 1) by ring.
    rewrite (UIntArray.seg_empty qp0_bare (nn0_bare - 1) (nn0_bare - 1)).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel (UIntArray.undef_seg qp0_bare 0 (nn0_bare - 1)).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
    split_pure_spatial.
    + cancel emp.
    + apply derivable1s_coq_prop_r; reflexivity.
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_nil; lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17); lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17);
      change UINT_MOD with 4294967296 in Hbound; lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17); lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17);
      change UINT_MOD with 4294967296 in Hbound;
      change UINT_MOD with 4294967296 in PreH8;
      change (4294967296 ÷ 2) with 2147483648 in PreH8;
      change UINT_MOD with 4294967296; lia.
    + replace (nn0_bare - 2 + 1) with (nn0_bare - 1) by ring;
      assert (Hsub : sublist (nn0_bare - 1) nn0_bare l_np_bare =
                     Znth (nn0_bare - 1) l_np_bare 0 :: nil)
        by (replace (sublist (nn0_bare - 1) nn0_bare l_np_bare)
              with (sublist (nn0_bare - 1) (nn0_bare - 1 + 1) l_np_bare)
              by (f_equal; ring);
            apply sublist_single; rewrite PreH16; lia);
      rewrite Hsub; simpl; rewrite list_to_Z_cons; rewrite list_to_Z_nil; ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_2_4 : mpn_div_qr_2_preinv_entail_wit_2_4.
Proof.
  pre_process.
  Exists 0 (Znth (nn0_bare - 1) l_np_bare 0) 0 (@nil Z) l_np_bare.
  split_pure_spatial.
  -
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_nil; lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17); lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17);
      change UINT_MOD with 4294967296 in Hbound; lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17); lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_np_bare (nn0_bare - 1)) as Hbound;
      specialize (Hbound ltac:(rewrite PreH16; lia) PreH17);
      change UINT_MOD with 4294967296 in Hbound;
      change UINT_MOD with 4294967296 in PreH8;
      change (4294967296 ÷ 2) with 2147483648 in PreH8;
      change UINT_MOD with 4294967296; lia.
    + replace (nn0_bare - 2 + 1) with (nn0_bare - 1) by ring;
      assert (Hsub : sublist (nn0_bare - 1) nn0_bare l_np_bare =
                     Znth (nn0_bare - 1) l_np_bare 0 :: nil)
        by (replace (sublist (nn0_bare - 1) nn0_bare l_np_bare)
              with (sublist (nn0_bare - 1) (nn0_bare - 1 + 1) l_np_bare)
              by (f_equal; ring);
            apply sublist_single; rewrite PreH16; lia);
      rewrite Hsub; simpl; rewrite list_to_Z_cons; rewrite list_to_Z_nil; ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_5_1 : mpn_div_qr_2_preinv_entail_wit_5_1.
Proof.
  pre_process.
  Exists carry_2 (rv1 * UINT_MOD + rv0) (qv + qv_done_2 * UINT_MOD) (qv :: l_done_2) l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.seg_single qp0_bare i qv).
    replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare i (i + 1) (nn0_bare - 1) (qv :: nil) l_done_2).
    + dump_pre_spatial; lia.
    + simpl.
      rewrite PreH43.
      cancel (UIntArray.undef_seg qp0_bare 0 i).
      cancel (UIntArray.seg qp0_bare i (nn0_bare - 1) (qv :: l_done_2)).
      cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_cons; unfold Z.succ; rewrite PreH27; lia.
    + split.
      * split; [exact PreH1 | change UINT_MOD with 4294967296; change UINT_MAX with 4294967295 in PreH2; lia].
      * exact PreH29.
    + rewrite list_to_Z_cons; rewrite PreH30; ring.
    + apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; [exact PreH3 | change UINT_MOD with 4294967296; lia] | exact PreH5].
    + replace (i - 1 + 1) with i by ring.
      rewrite (mpn_lshift_list_to_Z_suffix_cons UINT_MOD l_cur_2 i nn0_bare) by (try rewrite PreH26; lia).
      assert (Hpow : UINT_MOD ^ (nn0_bare - i) = UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))).
      { replace (nn0_bare - i) with (Z.succ (nn0_bare - (i + 1))) by lia.
        rewrite Z.pow_succ_r by lia.
        ring. }
      rewrite Hpow.
      replace (carry_2 * (UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))) +
               (Znth i l_cur_2 0 + UINT_MOD * list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)))
        with (UINT_MOD * (carry_2 * UINT_MOD ^ (nn0_bare - (i + 1)) +
                          list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)) +
              Znth i l_cur_2 0) by ring.
      rewrite PreH40.
      rewrite <- PreH31.
      replace (UINT_MOD * (qv_done_2 * (d1_orig * UINT_MOD + d0_orig) + (r1 * UINT_MOD + r0)) +
               Znth i l_cur_2 0)
        with (qv_done_2 * UINT_MOD * (d1_orig * UINT_MOD + d0_orig) +
              (r1 * UINT_MOD ^ 2 + r0 * UINT_MOD + Znth i l_cur_2 0)) by ring.
      rewrite PreH8.
      ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_5_2 : mpn_div_qr_2_preinv_entail_wit_5_2.
Proof.
  unfold mpn_div_qr_2_preinv_entail_wit_5_2.
  left; intros.
  Exists carry_2 (rv1 * UINT_MOD + rv0) (qv + qv_done_2 * UINT_MOD) (qv :: l_done_2) l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.seg_single qp0_bare i qv).
    replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare i (i + 1) (nn0_bare - 1) (qv :: nil) l_done_2).
    + dump_pre_spatial; lia.
    + simpl.
      cancel (UIntArray.undef_seg qp0_bare 0 i).
      cancel (UIntArray.seg qp0_bare i (nn0_bare - 1) (qv :: l_done_2)).
      cancel (UIntArray.full np0_bare nn0_bare l_cur_2).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
      cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_cons; unfold Z.succ; rewrite PreH27; lia.
    + split.
      * split; [exact PreH1 | change UINT_MOD with 4294967296; change UINT_MAX with 4294967295 in PreH2; lia].
      * exact PreH29.
    + rewrite list_to_Z_cons; rewrite PreH30; ring.
    + apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; [exact PreH3 | change UINT_MOD with 4294967296; lia] | exact PreH5].
    + replace (i - 1 + 1) with i by ring.
      rewrite (mpn_lshift_list_to_Z_suffix_cons UINT_MOD l_cur_2 i nn0_bare) by (try rewrite PreH26; lia).
      assert (Hpow : UINT_MOD ^ (nn0_bare - i) = UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))).
      { replace (nn0_bare - i) with (Z.succ (nn0_bare - (i + 1))) by lia.
        rewrite Z.pow_succ_r by lia.
        ring. }
      rewrite Hpow.
      replace (carry_2 * (UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))) +
               (Znth i l_cur_2 0 + UINT_MOD * list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)))
        with (UINT_MOD * (carry_2 * UINT_MOD ^ (nn0_bare - (i + 1)) +
                          list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)) +
              Znth i l_cur_2 0) by ring.
      rewrite PreH40.
      rewrite <- PreH31.
      replace (UINT_MOD * (qv_done_2 * (d1_orig * UINT_MOD + d0_orig) + (r1 * UINT_MOD + r0)) +
               Znth i l_cur_2 0)
        with (qv_done_2 * UINT_MOD * (d1_orig * UINT_MOD + d0_orig) +
              (r1 * UINT_MOD ^ 2 + r0 * UINT_MOD + Znth i l_cur_2 0)) by ring.
      rewrite PreH8.
      ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_5_3 : mpn_div_qr_2_preinv_entail_wit_5_3.
Proof.
  pre_process.
  Exists carry_2 (rv1 * UINT_MOD + rv0) (qv + qv_done_2 * UINT_MOD) (qv :: l_done_2) l_cur_2.
  split_pure_spatial.
  -
    rewrite PreH43.
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_cons; unfold Z.succ; rewrite PreH27; lia.
    + split.
      * split; [exact PreH1 | change UINT_MOD with 4294967296; change UINT_MAX with 4294967295 in PreH2; lia].
      * exact PreH29.
    + rewrite list_to_Z_cons; rewrite PreH30; ring.
    + apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; [exact PreH3 | change UINT_MOD with 4294967296; lia] | exact PreH5].
    + replace (i - 1 + 1) with i by ring.
      rewrite (mpn_lshift_list_to_Z_suffix_cons UINT_MOD l_cur_2 i nn0_bare) by (try rewrite PreH26; lia).
      assert (Hpow : UINT_MOD ^ (nn0_bare - i) = UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))).
      { replace (nn0_bare - i) with (Z.succ (nn0_bare - (i + 1))) by lia.
        rewrite Z.pow_succ_r by lia.
        ring. }
      rewrite Hpow.
      replace (carry_2 * (UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))) +
               (Znth i l_cur_2 0 + UINT_MOD * list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)))
        with (UINT_MOD * (carry_2 * UINT_MOD ^ (nn0_bare - (i + 1)) +
                          list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)) +
              Znth i l_cur_2 0) by ring.
      rewrite PreH40.
      rewrite <- PreH31.
      replace (UINT_MOD * (qv_done_2 * (d1_orig * UINT_MOD + d0_orig) + (r1 * UINT_MOD + r0)) +
               Znth i l_cur_2 0)
        with (qv_done_2 * UINT_MOD * (d1_orig * UINT_MOD + d0_orig) +
              (r1 * UINT_MOD ^ 2 + r0 * UINT_MOD + Znth i l_cur_2 0)) by ring.
      rewrite PreH8.
      ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_entail_wit_5_4 : mpn_div_qr_2_preinv_entail_wit_5_4.
Proof.
  pre_process.
  Exists carry_2 (rv1 * UINT_MOD + rv0) (qv + qv_done_2 * UINT_MOD) (qv :: l_done_2) l_cur_2.
  split_pure_spatial.
  -
    cancel (UIntArray.full np0_bare nn0_bare l_cur_2).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0_orig).
    cancel (&(inv0_bare # "gmp_div_inverse" ->ₛ"di") # UInt |-> di_orig).
  -
    split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_cons; unfold Z.succ; rewrite PreH27; lia.
    + split.
      * split; [exact PreH1 | change UINT_MOD with 4294967296; change UINT_MAX with 4294967295 in PreH2; lia].
      * exact PreH29.
    + rewrite list_to_Z_cons; rewrite PreH30; ring.
    + apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; [exact PreH3 | change UINT_MOD with 4294967296; lia] | exact PreH5].
    + replace (i - 1 + 1) with i by ring.
      rewrite (mpn_lshift_list_to_Z_suffix_cons UINT_MOD l_cur_2 i nn0_bare) by (try rewrite PreH26; lia).
      assert (Hpow : UINT_MOD ^ (nn0_bare - i) = UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))).
      { replace (nn0_bare - i) with (Z.succ (nn0_bare - (i + 1))) by lia.
        rewrite Z.pow_succ_r by lia.
        ring. }
      rewrite Hpow.
      replace (carry_2 * (UINT_MOD * UINT_MOD ^ (nn0_bare - (i + 1))) +
               (Znth i l_cur_2 0 + UINT_MOD * list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)))
        with (UINT_MOD * (carry_2 * UINT_MOD ^ (nn0_bare - (i + 1)) +
                          list_to_Z UINT_MOD (sublist (i + 1) nn0_bare l_cur_2)) +
              Znth i l_cur_2 0) by ring.
      rewrite PreH40.
      rewrite <- PreH31.
      replace (UINT_MOD * (qv_done_2 * (d1_orig * UINT_MOD + d0_orig) + (r1 * UINT_MOD + r0)) +
               Znth i l_cur_2 0)
        with (qv_done_2 * UINT_MOD * (d1_orig * UINT_MOD + d0_orig) +
              (r1 * UINT_MOD ^ 2 + r0 * UINT_MOD + Znth i l_cur_2 0)) by ring.
      rewrite PreH8.
      ring.
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_return_wit_1 : mpn_div_qr_2_preinv_return_wit_1.
Proof.
  pre_process.
  assert (Hvalid : gmp_div_inverse_valid 2 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try lia.
    - change UINT_MOD with 4294967296 in PreH5.
      change (4294967296 ÷ 2) with 2147483648 in PreH5.
      lia.
    - rewrite <- PreH4.
      change UINT_MOD with 4294967296.
      change UINT_MAX with 4294967295 in *.
      change (4294967296 ^ 2) with 18446744073709551616.
      nia.
    - right; split; [lia|].
      change (2 - 2) with 0.
      rewrite Z.pow_0_r, Z.div_1_r.
      exact PreH4.
    - exact PreH5.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH11.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH12.
  }
  set (lo := Z.lor (Z.shiftr r0 shift_orig)
             (unsigned_last_nbits (Z.shiftl r1 (32 - shift_orig)) 32)).
  set (hi := Z.shiftr r1 shift_orig).
  set (rv := (r1 * UINT_MOD + r0) / 2 ^ shift_orig).
  Exists rv qv_done (sublist 2 nn0_bare l_cur) (lo :: hi :: nil) l_done.
  split_pure_spatial.
  -
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    destruct (Z.eq_dec 2 1) as [Heq|Hneq]; [lia|].
    assert (Hi : i = -1) by lia.
    rewrite Hi in *.
    assert (Hhead := sublist_replace_two_head l_cur lo hi ltac:(rewrite PreH19; lia)).
    assert (Htail := sublist_replace_two_tail l_cur lo hi nn0_bare ltac:(rewrite PreH19; lia)).
    sep_apply UIntArray.full_to_seg.
    sep_apply (UIntArray.seg_split_to_seg np0_bare 0 2 nn0_bare
      (replace_Znth 0 lo (replace_Znth 1 hi l_cur))).
    2: { lia. }
    replace (2 - 0) with 2 by lia.
    replace (nn0_bare - 0) with nn0_bare by lia.
    rewrite Hhead, Htail.
    cancel.
    split_pure_spatial.
    + cancel.
    + apply derivable1s_coq_prop_r; exact Hvalid.
  -
    split_pures.
    all: try (apply derivable1s_coq_prop_r; assumption).
    all: try (apply derivable1s_coq_prop_r; reflexivity).
    all: try (apply derivable1s_coq_prop_r; lia).
    1: (apply derivable1s_coq_prop_r;
        rewrite Zlength_sublist by (rewrite PreH19; lia); lia).
    1: (apply derivable1s_coq_prop_r; simpl; split;
        [ subst lo; apply mpn_rshift_join_limb_bound;
          [ change UINT_MOD with 4294967296; lia | lia ]
        | split;
          [ subst hi; rewrite Z.shiftr_div_pow2 by lia; split;
            [ apply Z.div_pos; lia
            | apply Z.div_lt_upper_bound;
              [ apply Z.pow_pos_nonneg; lia
              | change UINT_MOD with 4294967296; nia ] ]
          | exact I ] ]).
    1: (apply derivable1s_coq_prop_r;
        apply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH21]).
    1: (apply derivable1s_coq_prop_r;
        subst lo hi rv; apply mpn_rshift_two_limb_value;
        [change UINT_MOD with 4294967296; lia |
         change UINT_MOD with 4294967296; lia | lia]).
    1: (apply derivable1s_coq_prop_r;
        assert (Hi : i = -1) by lia;
        assert (Hloop : carry * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur =
                        qv_done * (d1_orig * UINT_MOD + d0_orig) + remv);
        [ rewrite Hi in PreH33;
          replace (-1 + 1) with 0 in PreH33 by lia;
          replace (nn0_bare - 0) with nn0_bare in PreH33 by lia;
          rewrite (sublist_self l_cur nn0_bare) in PreH33 by (symmetry; exact PreH19);
          exact PreH33
        | ];
        assert (Hscaled : list_to_Z UINT_MOD l_np_bare * 2 ^ shift_orig =
                          qv_done * d_orig_bare * 2 ^ shift_orig + remv);
        [ replace (list_to_Z UINT_MOD l_np_bare * 2 ^ shift_orig)
            with (list_to_Z UINT_MOD l_cur + carry * UINT_MOD ^ nn0_bare)
            by (rewrite PreH35; ring);
          replace (list_to_Z UINT_MOD l_cur + carry * UINT_MOD ^ nn0_bare)
            with (carry * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur) by ring;
          rewrite Hloop;
          rewrite PreH4;
          ring
        | ];
        assert (Hquot : list_to_Z UINT_MOD l_np_bare - qv_done * d_orig_bare =
                         remv / 2 ^ shift_orig);
        [ apply Z.div_unique_exact;
          [ apply Z.pow_nonzero; lia
          | replace (2 ^ shift_orig *
                       (list_to_Z UINT_MOD l_np_bare - qv_done * d_orig_bare))
              with (list_to_Z UINT_MOD l_np_bare * 2 ^ shift_orig -
                    qv_done * d_orig_bare * 2 ^ shift_orig) by ring;
            rewrite Hscaled;
            ring ]
        | subst rv; rewrite PreH24; rewrite <- Hquot; ring ]).
    1: (apply derivable1s_coq_prop_r;
        subst rv; rewrite PreH24; apply Z.div_pos;
        [exact PreH31 | apply Z.pow_pos_nonneg; lia]).
    1: (apply derivable1s_coq_prop_r;
        subst rv; rewrite PreH24; apply Z.div_lt_upper_bound;
        [ apply Z.pow_pos_nonneg; lia
        | replace (2 ^ shift_orig * d_orig_bare) with (d_orig_bare * 2 ^ shift_orig) by ring;
          rewrite <- PreH4; exact PreH32 ]).
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_return_wit_2 : mpn_div_qr_2_preinv_return_wit_2.
Proof.
  pre_process.
  assert (Hvalid : gmp_div_inverse_valid 2 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try lia.
    - change UINT_MOD with 4294967296 in PreH5.
      change (4294967296 ÷ 2) with 2147483648 in PreH5.
      lia.
    - rewrite <- PreH4.
      change UINT_MOD with 4294967296.
      change UINT_MAX with 4294967295 in *.
      change (4294967296 ^ 2) with 18446744073709551616.
      nia.
    - right; split; [lia|].
      change (2 - 2) with 0.
      rewrite Z.pow_0_r, Z.div_1_r.
      exact PreH4.
    - exact PreH5.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH11.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH12.
  }
  set (lo := Z.lor (Z.shiftr r0 shift_orig)
             (unsigned_last_nbits (Z.shiftl r1 (32 - shift_orig)) 32)).
  set (hi := Z.shiftr r1 shift_orig).
  set (rv := (r1 * UINT_MOD + r0) / 2 ^ shift_orig).
  Exists rv qv_done (sublist 2 nn0_bare l_cur) (lo :: hi :: nil) l_done.
  split_pure_spatial.
  -
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    destruct (Z.eq_dec 2 1) as [Heq|Hneq]; [lia|].
    assert (Hi : i = -1) by lia.
    rewrite Hi in *.
    assert (Hhead := sublist_replace_two_head l_cur lo hi ltac:(rewrite PreH19; lia)).
    assert (Htail := sublist_replace_two_tail l_cur lo hi nn0_bare ltac:(rewrite PreH19; lia)).
    sep_apply UIntArray.full_to_seg.
    sep_apply (UIntArray.seg_split_to_seg np0_bare 0 2 nn0_bare
      (replace_Znth 0 lo (replace_Znth 1 hi l_cur))).
    2: { lia. }
    replace (2 - 0) with 2 by lia.
    replace (nn0_bare - 0) with nn0_bare by lia.
    rewrite Hhead, Htail.
    replace (-1 + 1) with 0 by lia.
    sep_apply_l_atomic (UIntArray.seg_to_full qp0_bare 0 (nn0_bare - 1) l_done).
    replace (qp0_bare + 0 * sizeof(UINT)) with qp0_bare by lia.
    replace (nn0_bare - 1 - 0) with (nn0_bare - 1) by lia.
    cancel.
    split_pure_spatial.
    + cancel.
    + apply derivable1s_coq_prop_r; exact Hvalid.
  -
    split_pures.
    all: try (apply derivable1s_coq_prop_r; assumption).
    all: try (apply derivable1s_coq_prop_r; reflexivity).
    1: (apply derivable1s_coq_prop_r;
        rewrite PreH20; assert (Hi : i = -1) by lia; lia).
    1: (apply derivable1s_coq_prop_r;
        rewrite Zlength_sublist by (rewrite PreH19; lia); lia).
    1: (apply derivable1s_coq_prop_r; simpl; split;
        [ subst lo; apply mpn_rshift_join_limb_bound;
          [ change UINT_MOD with 4294967296; lia | lia ]
        | split;
          [ subst hi; rewrite Z.shiftr_div_pow2 by lia; split;
            [ apply Z.div_pos; lia
            | apply Z.div_lt_upper_bound;
              [ apply Z.pow_pos_nonneg; lia
              | change UINT_MOD with 4294967296; nia ] ]
          | exact I ] ]).
    1: (apply derivable1s_coq_prop_r;
        apply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH21]).
    1: (apply derivable1s_coq_prop_r;
        subst lo hi rv; apply mpn_rshift_two_limb_value;
        [change UINT_MOD with 4294967296; lia |
         change UINT_MOD with 4294967296; lia | lia]).
    1: (apply derivable1s_coq_prop_r;
        assert (Hi : i = -1) by lia;
        assert (Hloop : carry * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur =
                        qv_done * (d1_orig * UINT_MOD + d0_orig) + remv);
        [ rewrite Hi in PreH33;
          replace (-1 + 1) with 0 in PreH33 by lia;
          replace (nn0_bare - 0) with nn0_bare in PreH33 by lia;
          rewrite (sublist_self l_cur nn0_bare) in PreH33 by (symmetry; exact PreH19);
          exact PreH33
        | ];
        assert (Hscaled : list_to_Z UINT_MOD l_np_bare * 2 ^ shift_orig =
                          qv_done * d_orig_bare * 2 ^ shift_orig + remv);
        [ replace (list_to_Z UINT_MOD l_np_bare * 2 ^ shift_orig)
            with (list_to_Z UINT_MOD l_cur + carry * UINT_MOD ^ nn0_bare)
            by (rewrite PreH35; ring);
          replace (list_to_Z UINT_MOD l_cur + carry * UINT_MOD ^ nn0_bare)
            with (carry * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur) by ring;
          rewrite Hloop;
          rewrite PreH4;
          ring
        | ];
        assert (Hquot : list_to_Z UINT_MOD l_np_bare - qv_done * d_orig_bare =
                         remv / 2 ^ shift_orig);
        [ apply Z.div_unique_exact;
          [ apply Z.pow_nonzero; lia
          | replace (2 ^ shift_orig *
                       (list_to_Z UINT_MOD l_np_bare - qv_done * d_orig_bare))
              with (list_to_Z UINT_MOD l_np_bare * 2 ^ shift_orig -
                    qv_done * d_orig_bare * 2 ^ shift_orig) by ring;
            rewrite Hscaled;
            ring ]
        | subst rv; rewrite PreH24; rewrite <- Hquot; ring ]).
    1: (apply derivable1s_coq_prop_r;
        subst rv; rewrite PreH24; apply Z.div_pos;
        [exact PreH31 | apply Z.pow_pos_nonneg; lia]).
    1: (apply derivable1s_coq_prop_r;
        subst rv; rewrite PreH24; apply Z.div_lt_upper_bound;
        [ apply Z.pow_pos_nonneg; lia
        | replace (2 ^ shift_orig * d_orig_bare) with (d_orig_bare * 2 ^ shift_orig) by ring;
          rewrite <- PreH4; exact PreH32 ]).
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_return_wit_3 : mpn_div_qr_2_preinv_return_wit_3.
Proof.
  pre_process.
  assert (Hvalid : gmp_div_inverse_valid 2 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try lia.
    - change UINT_MOD with 4294967296 in PreH5.
      change (4294967296 ÷ 2) with 2147483648 in PreH5.
      lia.
    - rewrite <- PreH4.
      change UINT_MOD with 4294967296.
      change UINT_MAX with 4294967295 in *.
      change (4294967296 ^ 2) with 18446744073709551616.
      nia.
    - right; split; [lia|].
      change (2 - 2) with 0.
      rewrite Z.pow_0_r, Z.div_1_r.
      exact PreH4.
    - exact PreH5.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH11.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH12.
  }
  Exists (r1 * UINT_MOD + r0) qv_done (sublist 2 nn0_bare l_cur) (r0 :: r1 :: nil) l_done.
  split_pure_spatial.
  -
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    destruct (Z.eq_dec 2 1) as [Heq|Hneq]; [lia|].
    assert (Hi : i = -1) by lia.
    rewrite Hi in *.
    assert (Hhead := sublist_replace_two_head l_cur r0 r1 ltac:(rewrite PreH19; lia)).
    assert (Htail := sublist_replace_two_tail l_cur r0 r1 nn0_bare ltac:(rewrite PreH19; lia)).
    sep_apply UIntArray.full_to_seg.
    sep_apply (UIntArray.seg_split_to_seg np0_bare 0 2 nn0_bare
      (replace_Znth 0 r0 (replace_Znth 1 r1 l_cur))).
    2: { lia. }
    replace (2 - 0) with 2 by lia.
    replace (nn0_bare - 0) with nn0_bare by lia.
    rewrite Hhead, Htail.
    cancel.
    split_pure_spatial.
    + cancel.
    + apply derivable1s_coq_prop_r; exact Hvalid.
  -
    split_pures.
    all: try (apply derivable1s_coq_prop_r; assumption).
    all: try (apply derivable1s_coq_prop_r; reflexivity).
    1: (apply derivable1s_coq_prop_r; rewrite PreH20; lia).
    1: (apply derivable1s_coq_prop_r;
        rewrite Zlength_sublist by (rewrite PreH19; lia); lia).
    1: (apply derivable1s_coq_prop_r; simpl; repeat split; try exact I;
        try (change UINT_MOD with 4294967296;
             change UINT_MAX with 4294967295 in *; lia)).
    1: (apply derivable1s_coq_prop_r;
        apply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH21]).
    1: (apply derivable1s_coq_prop_r;
        rewrite list_to_Z_cons; rewrite list_to_Z_cons; rewrite list_to_Z_nil; ring).
    1: (apply derivable1s_coq_prop_r;
        assert (Hi : i = -1) by lia;
        assert (Hden : d1_orig * UINT_MOD + d0_orig = d_orig_bare);
        [ rewrite PreH34 in PreH4;
          rewrite Z.pow_0_r in PreH4;
          replace (d_orig_bare * 1) with d_orig_bare in PreH4 by ring;
          exact PreH4
        | ];
        rewrite Hi in PreH33;
        replace (-1 + 1) with 0 in PreH33 by lia;
        rewrite PreH35 in PreH33;
        rewrite Z.mul_0_l, Z.add_0_l in PreH33;
        rewrite (sublist_self l_cur nn0_bare) in PreH33 by (symmetry; exact PreH19);
        rewrite PreH36 in PreH33;
        rewrite Hden in PreH33;
        rewrite <- PreH24 in PreH33;
        ring_simplify in PreH33;
        replace (qv_done * d_orig_bare + (r1 * UINT_MOD + r0))
          with (qv_done * d_orig_bare + r1 * UINT_MOD + r0) by ring;
        exact PreH33).
    1: (apply derivable1s_coq_prop_r; rewrite PreH24; exact PreH31).
    1: (apply derivable1s_coq_prop_r;
        assert (Hden : d1_orig * UINT_MOD + d0_orig = d_orig_bare);
        [ rewrite PreH34 in PreH4;
          rewrite Z.pow_0_r in PreH4;
          replace (d_orig_bare * 1) with d_orig_bare in PreH4 by ring;
          exact PreH4
        | rewrite PreH24; rewrite <- Hden; exact PreH32 ]).
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_return_wit_4 : mpn_div_qr_2_preinv_return_wit_4.
Proof.
  pre_process.
  assert (Hvalid : gmp_div_inverse_valid 2 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try lia.
    - change UINT_MOD with 4294967296 in PreH5.
      change (4294967296 ÷ 2) with 2147483648 in PreH5.
      lia.
    - rewrite <- PreH4.
      change UINT_MOD with 4294967296.
      change UINT_MAX with 4294967295 in *.
      change (4294967296 ^ 2) with 18446744073709551616.
      nia.
    - right; split; [lia|].
      change (2 - 2) with 0.
      rewrite Z.pow_0_r, Z.div_1_r.
      exact PreH4.
    - exact PreH5.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH11.
    - destruct (Z.eq_dec 2 1) as [Hbad|_]; [lia|].
      replace (d1_orig * UINT_MOD + d0_orig)
        with (UINT_MOD * d1_orig + d0_orig) by ring.
      exact PreH12.
  }
  Exists (r1 * UINT_MOD + r0) qv_done (sublist 2 nn0_bare l_cur) (r0 :: r1 :: nil) l_done.
  split_pure_spatial.
  -
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    destruct (Z.eq_dec 2 1) as [Heq|Hneq]; [lia|].
    assert (Hi : i = -1) by lia.
    rewrite Hi in *.
    assert (Hhead := sublist_replace_two_head l_cur r0 r1 ltac:(rewrite PreH19; lia)).
    assert (Htail := sublist_replace_two_tail l_cur r0 r1 nn0_bare ltac:(rewrite PreH19; lia)).
    sep_apply UIntArray.full_to_seg.
    sep_apply (UIntArray.seg_split_to_seg np0_bare 0 2 nn0_bare
      (replace_Znth 0 r0 (replace_Znth 1 r1 l_cur))).
    2: { lia. }
    replace (2 - 0) with 2 by lia.
    replace (nn0_bare - 0) with nn0_bare by lia.
    rewrite Hhead, Htail.
    replace (-1 + 1) with 0 by lia.
    sep_apply_l_atomic (UIntArray.seg_to_full qp0_bare 0 (nn0_bare - 1) l_done).
    replace (qp0_bare + 0 * sizeof(UINT)) with qp0_bare by lia.
    replace (nn0_bare - 1 - 0) with (nn0_bare - 1) by lia.
    cancel.
    split_pure_spatial.
    + cancel.
    + apply derivable1s_coq_prop_r; exact Hvalid.
  -
    split_pures.
    all: try (apply derivable1s_coq_prop_r; assumption).
    all: try (apply derivable1s_coq_prop_r; reflexivity).
    1: (apply derivable1s_coq_prop_r; rewrite PreH20; lia).
    1: (apply derivable1s_coq_prop_r;
        rewrite Zlength_sublist by (rewrite PreH19; lia); lia).
    1: (apply derivable1s_coq_prop_r; simpl; repeat split; try exact I;
        try (change UINT_MOD with 4294967296;
             change UINT_MAX with 4294967295 in *; lia)).
    1: (apply derivable1s_coq_prop_r;
        apply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH21]).
    1: (apply derivable1s_coq_prop_r;
        rewrite list_to_Z_cons; rewrite list_to_Z_cons; rewrite list_to_Z_nil; ring).
    1: (apply derivable1s_coq_prop_r;
        assert (Hi : i = -1) by lia;
        assert (Hden : d1_orig * UINT_MOD + d0_orig = d_orig_bare);
        [ rewrite PreH34 in PreH4;
          rewrite Z.pow_0_r in PreH4;
          replace (d_orig_bare * 1) with d_orig_bare in PreH4 by ring;
          exact PreH4
        | ];
        rewrite Hi in PreH33;
        replace (-1 + 1) with 0 in PreH33 by lia;
        rewrite PreH35 in PreH33;
        rewrite Z.mul_0_l, Z.add_0_l in PreH33;
        rewrite (sublist_self l_cur nn0_bare) in PreH33 by (symmetry; exact PreH19);
        rewrite PreH36 in PreH33;
        rewrite Hden in PreH33;
        rewrite <- PreH24 in PreH33;
        ring_simplify in PreH33;
        replace (qv_done * d_orig_bare + (r1 * UINT_MOD + r0))
          with (qv_done * d_orig_bare + r1 * UINT_MOD + r0) by ring;
        exact PreH33).
    1: (apply derivable1s_coq_prop_r; rewrite PreH24; exact PreH31).
    1: (apply derivable1s_coq_prop_r;
        assert (Hden : d1_orig * UINT_MOD + d0_orig = d_orig_bare);
        [ rewrite PreH34 in PreH4;
          rewrite Z.pow_0_r in PreH4;
          replace (d_orig_bare * 1) with d_orig_bare in PreH4 by ring;
          exact PreH4
        | rewrite PreH24; rewrite <- Hden; exact PreH32 ]).
Qed. 

Lemma proof_of_mpn_div_qr_2_preinv_derive_optional_by_bare : mpn_div_qr_2_preinv_derive_optional_by_bare.
Proof.
  pre_process.
  unfold optional_q_undef.
  Split.
  - Intros_p Hnull.
    Exists qp_pre np_pre nn_pre inv_pre l_np_optional d_orig_optional.
    Right.
    split_pure_spatial.
    + cancel (UIntArray.full np_pre nn_pre l_np_optional).
      cancel (store_div_inverse inv_pre 2 d_orig_optional).
      apply derivable1_wand_sepcon_adjoint.
      Split.
      * Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        Intros.
        Intros.
        Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
        unfold optional_q_full.
        Left.
        split_pure_spatial.
        -- rewrite H0, H1, H2.
           cancel (UIntArray.seg np_pre 0 2 l_rem_2).
           cancel (UIntArray.seg np_pre 2 nn_pre l_tail_2).
           cancel (store_div_inverse inv_pre 2 d_orig_optional).
        -- split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
      * Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        Intros.
        Intros.
        entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
  - Intros_p Hnonnull.
    Exists qp_pre np_pre nn_pre inv_pre l_np_optional d_orig_optional.
    Left.
    split_pure_spatial.
    + cancel (UIntArray.undef_full qp_pre (nn_pre - 1)).
      cancel (UIntArray.full np_pre nn_pre l_np_optional).
      cancel (store_div_inverse inv_pre 2 d_orig_optional).
      apply derivable1_wand_sepcon_adjoint.
      Split.
      * Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        Intros.
        Intros.
        entailer!.
      * Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        Intros.
        Intros.
        Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
        unfold optional_q_full.
        Right.
        split_pure_spatial.
        -- rewrite H, H0, H1, H2.
           cancel (UIntArray.full qp_pre (nn_pre - 1) l_q_2).
           cancel (UIntArray.seg np_pre 0 2 l_rem_2).
           cancel (UIntArray.seg np_pre 2 nn_pre l_tail_2).
           cancel (store_div_inverse inv_pre 2 d_orig_optional).
        -- split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
Qed. 
