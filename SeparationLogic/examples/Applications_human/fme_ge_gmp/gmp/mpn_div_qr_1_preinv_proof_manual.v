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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_1_preinv_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_1_preinv_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_1_1 : mpn_div_qr_1_preinv_entail_wit_1_1.
Proof.
  pre_process.
  
  unfold store_div_inverse, div_inverse_store.
  Intros shift d1 d0 di.
  Exists di d0 d1 shift.
  rewrite PreH1, PreH2, PreH3, PreH4.
  split_pure_spatial.
  - entailer!.
  - unfold gmp_div_inverse_valid, div_inverse_den in H.
    destruct H as [Hdn [Hdpos [Hshift [Hd1 [Hd0 [Hdi [Hsmall [Hrepr [Hhalf [Hlo Hhi]]]]]]]]]].
    destruct Hrepr as [[Hdn_eq Hrepr] | [Hdn_gt Hrepr]]; [|lia].
    destruct (Z.eq_dec 1 1) as [Heq|Hneq]; [|lia].
    change (UINT_MOD ^ 1) with UINT_MOD in Hsmall.
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_1_2 : mpn_div_qr_1_preinv_entail_wit_1_2.
Proof.
  pre_process.
  
  unfold store_div_inverse, div_inverse_store.
  Intros shift d1 d0 di.
  Exists di d0 d1 shift.
  rewrite PreH1, PreH2, PreH3, PreH4.
  split_pure_spatial.
  - entailer!.
  - unfold gmp_div_inverse_valid, div_inverse_den in H.
    destruct H as [Hdn [Hdpos [Hshift [Hd1 [Hd0 [Hdi [Hsmall [Hrepr [Hhalf [Hlo Hhi]]]]]]]]]].
    destruct Hrepr as [[Hdn_eq Hrepr] | [Hdn_gt Hrepr]]; [|lia].
    destruct (Z.eq_dec 1 1) as [Heq|Hneq]; [|lia].
    change (UINT_MOD ^ 1) with UINT_MOD in Hsmall.
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_2_1 : mpn_div_qr_1_preinv_entail_wit_2_1.
Proof.
  unfold mpn_div_qr_1_preinv_entail_wit_2_1.
  left.
  intros.
  prop_apply_p (UIntArray_undef_full_full_base_neq retval np0_bare nn0_bare l_np_bare ltac:(lia) ltac:(assumption)).
  Intros.
  Exists retval di_orig_2 d0_orig_2 d1_orig_2 shift_orig_2.
  entailer!.
  all: try (split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!).
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_2_2 : mpn_div_qr_1_preinv_entail_wit_2_2.
Proof.
  unfold mpn_div_qr_1_preinv_entail_wit_2_2.
  left.
  intros.
  prop_apply_p (UIntArray_undef_full_full_base_neq qp0_bare np0_bare nn0_bare l_np_bare ltac:(lia) ltac:(assumption)).
  Intros.
  Exists di_orig_2 d0_orig_2 d1_orig_2 shift_orig_2.
  entailer!.
  all: try (split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!).
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_3_1 : mpn_div_qr_1_preinv_entail_wit_3_1.
Proof.
  pre_process.
  Exists retval 0 (@nil Z) l_out d0_orig_2 shift_orig_2.
  assert (Hretval_nonneg : 0 <= retval).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig_2) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (Hnotneg : ~ retval < 0).
    {
      intro Hneg.
      assert (Hle : retval <= -1) by lia.
      assert (Hmul : retval * P <= -1 * P).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      replace (-1 * P) with (- P) in Hmul by ring.
      assert (Hlhs_neg : B + retval * P < P + (- P)).
      { apply Z.add_lt_le_mono; [exact Hout_lt | exact Hmul]. }
      replace (P + - P) with 0 in Hlhs_neg by ring.
      assert (Hrhs_nonneg : 0 <= A * S).
      { apply Z.mul_nonneg_nonneg; lia. }
      rewrite PreH3 in Hlhs_neg.
      lia.
    }
    lia.
  }
  assert (Hretval_lt_d1 : retval < d1_orig).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    rewrite PreH19 in Hnp_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig_2) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (HretP_le : retval * P <= A * S) by (rewrite <- PreH3; lia).
    assert (HAS_lt : A * S < P * S).
    { apply (proj1 (Z.mul_lt_mono_pos_r S A P HS)); exact Hnp_lt. }
    assert (Hret_lt_S : retval < S).
    {
      apply (proj2 (Z.mul_lt_mono_pos_r P retval S HU)).
      replace (S * P) with (P * S) by ring.
      eapply Z.le_lt_trans; [exact HretP_le | exact HAS_lt].
    }
    rewrite PreH9.
    assert (HS_le : S <= d_orig_bare * S).
    { replace S with (1 * S) at 1 by ring; apply Z.mul_le_mono_nonneg_r; lia. }
    eapply Z.lt_le_trans; [exact Hret_lt_S | exact HS_le].
  }
  split_pure_spatial.
  - rewrite PreH23.
    cancel (UIntArray.full tp nn0_bare l_out).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((( &( "tn" ) )) # Int  |-> nn0_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try entailer!.
    + rewrite Zlength_nil. lia.
    + rewrite list_to_Z_nil.
      replace (nn0_bare - 1 + 1) with nn0_bare by ring.
      assert (Hout : sublist 0 nn0_bare l_out = l_out).
      { rewrite <- PreH1. apply sublist_self. lia. }
      rewrite Hout.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_3_2 : mpn_div_qr_1_preinv_entail_wit_3_2.
Proof.
  pre_process.
  Exists tn_4 retval 0 (@nil Z) l_out d0_orig_2 shift_orig_2.
  assert (Hretval_nonneg : 0 <= retval).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig_2) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (Hnotneg : ~ retval < 0).
    {
      intro Hneg.
      assert (Hle : retval <= -1) by lia.
      assert (Hmul : retval * P <= -1 * P).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      replace (-1 * P) with (- P) in Hmul by ring.
      assert (Hlhs_neg : B + retval * P < P + (- P)).
      { apply Z.add_lt_le_mono; [exact Hout_lt | exact Hmul]. }
      replace (P + - P) with 0 in Hlhs_neg by ring.
      assert (Hrhs_nonneg : 0 <= A * S).
      { apply Z.mul_nonneg_nonneg; lia. }
      rewrite PreH3 in Hlhs_neg.
      lia.
    }
    lia.
  }
  assert (Hretval_lt_d1 : retval < d1_orig).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as [Hout_nonneg Hout_lt].
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np_bare PreH20) as [Hnp_nonneg Hnp_lt].
    rewrite PreH1 in Hout_lt.
    rewrite PreH19 in Hnp_lt.
    set (P := UINT_MOD ^ nn0_bare) in *.
    set (S := 2 ^ shift_orig_2) in *.
    set (A := list_to_Z UINT_MOD l_np_bare) in *.
    set (B := list_to_Z UINT_MOD l_out) in *.
    assert (HU : 0 < P) by (subst P; apply Z.pow_pos_nonneg; [exact UINT_MOD_pos | lia]).
    assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
    assert (HretP_le : retval * P <= A * S) by (rewrite <- PreH3; lia).
    assert (HAS_lt : A * S < P * S).
    { apply (proj1 (Z.mul_lt_mono_pos_r S A P HS)); exact Hnp_lt. }
    assert (Hret_lt_S : retval < S).
    {
      apply (proj2 (Z.mul_lt_mono_pos_r P retval S HU)).
      replace (S * P) with (P * S) by ring.
      eapply Z.le_lt_trans; [exact HretP_le | exact HAS_lt].
    }
    rewrite PreH9.
    assert (HS_le : S <= d_orig_bare * S).
    { replace S with (1 * S) at 1 by ring; apply Z.mul_le_mono_nonneg_r; lia. }
    eapply Z.lt_le_trans; [exact Hret_lt_S | exact HS_le].
  }
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.full_to_seg qp0_bare nn0_bare l_out).
    replace ((nn0_bare - 1) + 1) with nn0_bare by lia.
    assert (Hout : sublist 0 nn0_bare l_out = l_out).
    { rewrite <- PreH1. apply sublist_self. lia. }
    rewrite Hout.
    rewrite (UIntArray.seg_empty qp0_bare nn0_bare).
    cancel (UIntArray.seg qp0_bare 0 nn0_bare l_out).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((( &( "tn" ) )) # Int  |-> tn_4).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
    entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try entailer!.
    + rewrite Zlength_nil. lia.
    + rewrite list_to_Z_nil.
      replace (nn0_bare - 1 + 1) with nn0_bare by ring.
      assert (Hout : sublist 0 nn0_bare l_out = l_out).
      { rewrite <- PreH1. apply sublist_self. lia. }
      rewrite Hout.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_3_3 : mpn_div_qr_1_preinv_entail_wit_3_3.
Proof.
  pre_process.
  Exists 0 0 0 (@nil Z) l_np_bare d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg qp0_bare nn0_bare).
    replace ((nn0_bare - 1) + 1) with nn0_bare by lia.
    rewrite (UIntArray.seg_empty qp0_bare nn0_bare).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel (UIntArray.undef_seg qp0_bare 0 nn0_bare).
    cancel ((( &( "tn" ) )) # Int  |-> 0).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
    entailer!.
  - assert (Hshift : shift_orig_2 = 0) by lia.
    assert (Hd1_pos : 0 < d1_orig).
    {
      change UINT_MOD with 4294967296 in PreH9.
      lia.
    }
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try entailer!.
    + rewrite Zlength_nil. lia.
    + rewrite list_to_Z_nil.
      replace (nn0_bare - 1 + 1) with nn0_bare by ring.
      assert (Hnp : sublist 0 nn0_bare l_np_bare = l_np_bare).
      { rewrite <- PreH17. apply sublist_self. lia. }
      rewrite Hnp.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_3_4 : mpn_div_qr_1_preinv_entail_wit_3_4.
Proof.
  pre_process.
  Right.
  Exists 0 0 0 (@nil Z) l_np_bare d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((( &( "tn" ) )) # Int  |-> 0).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - assert (Hshift : shift_orig_2 = 0) by lia.
    assert (Hd1_pos : 0 < d1_orig).
    {
      change UINT_MOD with 4294967296 in PreH9.
      lia.
    }
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try entailer!.
    + rewrite Zlength_nil. lia.
    + rewrite list_to_Z_nil.
      replace (nn0_bare - 1 + 1) with nn0_bare by ring.
      assert (Hnp : sublist 0 nn0_bare l_np_bare = l_np_bare).
      { rewrite <- PreH17. apply sublist_self. lia. }
      rewrite Hnp.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_4_1 : mpn_div_qr_1_preinv_entail_wit_4_1.
Proof.
  pre_process.
  
  Exists r carry_2 qv_done_2 l_done_2 l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - rewrite PreH39.
    cancel (UIntArray.seg qp0_bare 0 (nn + 1) (sublist 0 (nn + 1) l_cur_2)).
    cancel (UIntArray.seg qp0_bare (nn + 1) nn0_bare l_done_2).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial;
      try solve [ assumption | reflexivity
                | match goal with
                  | |- _ <= _ => lia
                  | |- _ < _ => lia
                  | |- _ >= _ => lia
                  | |- _ > _ => lia
                  | |- _ <> _ => lia
                  end ].
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_4_2 : mpn_div_qr_1_preinv_entail_wit_4_2.
Proof.
  pre_process.
  
  Exists r 0 qv_done_2 l_done_2 l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - rewrite PreH37.
    cancel (UIntArray.full np nn0_bare l_cur_2).
    cancel (UIntArray.undef_seg qp0_bare 0 (nn + 1)).
    cancel (UIntArray.seg qp0_bare (nn + 1) nn0_bare l_done_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> 0).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial;
      try solve [ replace (0 * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur_2)
                    with (carry_2 * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur_2)
                    by (rewrite PreH38; ring);
                  rewrite PreH36; ring
                | exact PreH6
                | assumption
                | reflexivity
                | match goal with |- 0 <= nn => lia end
                | match goal with |- 0 <= 4294967295 => lia end ].
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_5_1 : mpn_div_qr_1_preinv_entail_wit_5_1.
Proof.
  pre_process.
  Exists tn_4 carry_2 (list_to_Z UINT_MOD (qv :: l_done_2))
         (qv :: l_done_2) l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_split_to_seg qp0_bare nn (nn + 1)
      (replace_Znth nn qv (sublist 0 (nn + 1) l_cur_2))).
    + dump_pre_spatial.
      split; [exact PreH14 | apply Z.le_succ_diag_r].
    + replace (nn - 1 + 1) with nn by lia.
      assert (Hsplit :
        sublist 0 (nn + 1) l_cur_2 =
        sublist 0 nn l_cur_2 ++ sublist nn (nn + 1) l_cur_2).
      {
        apply (@sublist_split Z 0 (nn + 1) nn l_cur_2).
        - split; [apply Z.le_refl | exact PreH14].
        - split; [apply Z.le_succ_diag_r | rewrite PreH19; lia].
      }
      assert (Hlenpre : Zlength (sublist 0 nn l_cur_2) = nn).
      {
        rewrite Zlength_sublist.
        - ring.
        - split.
          + split; [apply Z.le_refl | exact PreH14].
          + rewrite PreH19; apply Z.lt_le_incl; exact PreH15.
      }
      assert (Hprefix :
        sublist 0 nn
          (replace_Znth nn qv (sublist 0 (nn + 1) l_cur_2)) =
        sublist 0 nn l_cur_2).
      {
        rewrite Hsplit.
        rewrite replace_Znth_app_r by (rewrite Hlenpre; lia).
        rewrite replace_Znth_nothing by (rewrite Hlenpre; lia).
        rewrite <- Hlenpre at 1.
        rewrite sublist_app_exact1.
        reflexivity.
      }
      assert (Hsingle :
        sublist nn (nn + 1)
          (replace_Znth nn qv (sublist 0 (nn + 1) l_cur_2)) =
        qv :: nil).
      {
        rewrite Hsplit.
        rewrite replace_Znth_app_r by (rewrite Hlenpre; lia).
        rewrite replace_Znth_nothing by (rewrite Hlenpre; lia).
        rewrite Hlenpre.
        replace (nn - nn) with 0 by lia.
        rewrite (sublist_split_app_r nn (nn + 1) nn
                  (sublist 0 nn l_cur_2)
                  (replace_Znth 0 qv (sublist nn (nn + 1) l_cur_2)))
          by (try exact Hlenpre; lia).
        replace (nn - nn) with 0 by lia.
        replace (nn + 1 - nn) with 1 by lia.
        rewrite replace_Znth_sublist_head
          by (split; [exact PreH14 | split; [apply Z.lt_succ_diag_r | rewrite PreH19; lia]]).
        rewrite sublist_cons_head.
        reflexivity.
      }
      rewrite Hprefix.
      rewrite Hsingle.
      sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare nn (nn + 1)
        nn0_bare (qv :: nil) l_done_2).
      * dump_pre_spatial.
        split; [apply Z.le_succ_diag_r | lia].
      * simpl.
        rewrite PreH36.
        cancel (UIntArray.seg qp0_bare 0 nn (sublist 0 nn l_cur_2)).
        cancel (UIntArray.seg qp0_bare nn nn0_bare (qv :: l_done_2)).
        cancel ((( &( "tn" ) )) # Int  |-> tn_4).
        cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
        cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
        cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
        cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
        cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  -
    split_pures; dump_pre_spatial;
      try solve [ assumption | reflexivity
                | match goal with
                  | |- _ <= _ => lia
                  | |- _ < _ => lia
                  | |- _ >= _ => lia
                  | |- _ > _ => lia
                  | |- _ <> _ => lia
                  end ].
    + rewrite Zlength_cons.
      unfold Z.succ.
      rewrite PreH20.
      ring.
    + split.
      * change UINT_MOD with 4294967296.
        change UINT_MAX with 4294967295 in PreH30.
        lia.
      * exact PreH23.
    + replace (nn - 1 + 1) with nn by ring.
      rewrite list_to_Z_cons.
      assert (Happ :
        list_to_Z UINT_MOD (sublist 0 (nn + 1) l_cur_2) =
        list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
        Znth nn l_cur_2 0 * UINT_MOD ^ nn).
      {
        apply list_to_Z_list_append.
        - exact UINT_MOD_pos.
        - lia.
        - exact PreH22.
      }
      replace (nn + 1) with (Z.succ nn) in PreH34 by ring.
      rewrite Z.pow_succ_r in PreH34 by lia.
      replace (Z.succ nn) with (nn + 1) in PreH34 by ring.
      rewrite Happ in PreH34.
      rewrite PreH34.
      assert (Hstep :
        r_old * (UINT_MOD * UINT_MOD ^ nn) + Znth nn l_cur_2 0 * UINT_MOD ^ nn =
        qv * d1_orig * UINT_MOD ^ nn + rv * UINT_MOD ^ nn).
      {
        replace (qv * d1_orig * UINT_MOD ^ nn + rv * UINT_MOD ^ nn)
          with ((qv * d1_orig + rv) * UINT_MOD ^ nn) by ring.
        rewrite <- PreH40.
        rewrite Znth_sublist by lia.
        replace (nn - 0 + 0) with nn by lia.
        ring.
      }
      replace (list_to_Z UINT_MOD l_done_2 * (UINT_MOD * UINT_MOD ^ nn) * d1_orig +
               r_old * (UINT_MOD * UINT_MOD ^ nn) +
               (list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
                Znth nn l_cur_2 0 * UINT_MOD ^ nn))
        with ((r_old * (UINT_MOD * UINT_MOD ^ nn) + Znth nn l_cur_2 0 * UINT_MOD ^ nn) +
              list_to_Z UINT_MOD l_done_2 * (UINT_MOD * UINT_MOD ^ nn) * d1_orig +
              list_to_Z UINT_MOD (sublist 0 nn l_cur_2)) by ring.
      rewrite Hstep.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_5_2 : mpn_div_qr_1_preinv_entail_wit_5_2.
Proof.
  pre_process.
  Exists tn_4 0 (list_to_Z UINT_MOD (qv :: l_done_2))
         (qv :: l_done_2) l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.seg_single qp0_bare nn qv).
    replace (nn + 1 - 1) with nn by lia.
    replace (nn - 1 + 1) with nn by lia.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare nn (nn + 1)
      nn0_bare (qv :: nil) l_done_2).
    + dump_pre_spatial; lia.
    + simpl.
      cancel (UIntArray.undef_seg qp0_bare 0 nn).
      cancel (UIntArray.seg qp0_bare nn nn0_bare (qv :: l_done_2)).
      cancel ((( &( "tn" ) )) # Int  |-> tn_4).
      cancel (UIntArray.full np nn0_bare l_cur_2).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  -
    split_pures; dump_pre_spatial;
      try solve [ assumption | reflexivity
                | match goal with
                  | |- _ <= _ => lia
                  | |- _ < _ => lia
                  | |- _ >= _ => lia
                  | |- _ > _ => lia
                  | |- _ <> _ => lia
                  end ].
    + rewrite Zlength_cons.
      unfold Z.succ.
      rewrite PreH20.
      ring.
    + split.
      * change UINT_MOD with 4294967296.
        change UINT_MAX with 4294967295 in PreH30.
        lia.
      * exact PreH23.
    + rewrite list_to_Z_cons.
      replace (nn - 1 + 1) with nn by ring.
      assert (Happ :
        list_to_Z UINT_MOD (sublist 0 (nn + 1) l_cur_2) =
        list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
        Znth nn l_cur_2 0 * UINT_MOD ^ nn).
      {
        apply list_to_Z_list_append.
        - exact UINT_MOD_pos.
        - lia.
        - exact PreH22.
      }
      replace (nn + 1) with (Z.succ nn) in PreH34 by ring.
      rewrite Z.pow_succ_r in PreH34 by lia.
      replace (Z.succ nn) with (nn + 1) in PreH34 by ring.
      rewrite Happ in PreH34.
      replace (carry_2 * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur_2)
        with (list_to_Z UINT_MOD l_cur_2) in PreH34 by (rewrite PreH36; ring).
      rewrite PreH34.
      replace (list_to_Z UINT_MOD l_done_2 * (UINT_MOD * UINT_MOD ^ nn) * d1_orig +
               r_old * (UINT_MOD * UINT_MOD ^ nn) +
               (list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
                Znth nn l_cur_2 0 * UINT_MOD ^ nn))
        with (list_to_Z UINT_MOD l_done_2 * UINT_MOD * UINT_MOD ^ nn * d1_orig +
              (r_old * UINT_MOD + Znth nn l_cur_2 0) * UINT_MOD ^ nn +
              list_to_Z UINT_MOD (sublist 0 nn l_cur_2)) by ring.
      rewrite PreH41.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_5_3 : mpn_div_qr_1_preinv_entail_wit_5_3.
Proof.
  pre_process.
  Exists carry_2 (list_to_Z UINT_MOD (qv :: l_done_2))
         (qv :: l_done_2) l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - cancel (UIntArray.full np nn0_bare l_cur_2).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial;
      try solve [ assumption | reflexivity
                | match goal with
                  | |- _ <= _ => lia
                  | |- _ < _ => lia
                  | |- _ >= _ => lia
                  | |- _ > _ => lia
                  | |- _ <> _ => lia
                  end ].
    + rewrite Zlength_cons.
      unfold Z.succ.
      rewrite PreH27.
      ring.
    + split.
      * change UINT_MOD with 4294967296.
        change UINT_MAX with 4294967295 in PreH3.
        lia.
      * exact PreH30.
    + replace (nn - 1 + 1) with nn by ring.
      rewrite list_to_Z_cons.
      assert (Happ :
        list_to_Z UINT_MOD (sublist 0 (nn + 1) l_cur_2) =
        list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
        Znth nn l_cur_2 0 * UINT_MOD ^ nn).
      {
        apply list_to_Z_list_append.
        - exact UINT_MOD_pos.
        - lia.
        - exact PreH29.
      }
      replace (nn + 1) with (Z.succ nn) in PreH36 by ring.
      rewrite Z.pow_succ_r in PreH36 by lia.
      replace (Z.succ nn) with (nn + 1) in PreH36 by ring.
      rewrite Happ in PreH36.
      rewrite PreH36.
      assert (Hstep :
        r * (UINT_MOD * UINT_MOD ^ nn) + Znth nn l_cur_2 0 * UINT_MOD ^ nn =
        qv * d1_orig * UINT_MOD ^ nn + rv * UINT_MOD ^ nn).
      {
        replace (qv * d1_orig * UINT_MOD ^ nn + rv * UINT_MOD ^ nn)
          with ((qv * d1_orig + rv) * UINT_MOD ^ nn) by ring.
        rewrite <- PreH6.
        ring.
      }
      replace (list_to_Z UINT_MOD l_done_2 * (UINT_MOD * UINT_MOD ^ nn) * d1_orig +
               r * (UINT_MOD * UINT_MOD ^ nn) +
               (list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
                Znth nn l_cur_2 0 * UINT_MOD ^ nn))
        with ((r * (UINT_MOD * UINT_MOD ^ nn) + Znth nn l_cur_2 0 * UINT_MOD ^ nn) +
              list_to_Z UINT_MOD l_done_2 * (UINT_MOD * UINT_MOD ^ nn) * d1_orig +
              list_to_Z UINT_MOD (sublist 0 nn l_cur_2)) by ring.
      rewrite Hstep.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_5_4 : mpn_div_qr_1_preinv_entail_wit_5_4.
Proof.
  pre_process.
  Right.
  Exists tn_4 0 (list_to_Z UINT_MOD (qv :: l_done_2))
         (qv :: l_done_2) l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - cancel (UIntArray.full np nn0_bare l_cur_2).
    cancel ((( &( "tn" ) )) # Int  |-> tn_4).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial;
      try solve [ assumption | reflexivity
                | match goal with
                  | |- _ <= _ => lia
                  | |- _ < _ => lia
                  | |- _ >= _ => lia
                  | |- _ > _ => lia
                  | |- _ <> _ => lia
                  end ].
    + rewrite Zlength_cons.
      unfold Z.succ.
      rewrite PreH27.
      ring.
    + split.
      * change UINT_MOD with 4294967296.
        change UINT_MAX with 4294967295 in PreH3.
        lia.
      * exact PreH30.
    + rewrite list_to_Z_cons.
      replace (nn - 1 + 1) with nn by ring.
      assert (Happ :
        list_to_Z UINT_MOD (sublist 0 (nn + 1) l_cur_2) =
        list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
        Znth nn l_cur_2 0 * UINT_MOD ^ nn).
      {
        apply list_to_Z_list_append.
        - exact UINT_MOD_pos.
        - lia.
        - exact PreH29.
      }
      replace (nn + 1) with (Z.succ nn) in PreH36 by ring.
      rewrite Z.pow_succ_r in PreH36 by lia.
      replace (Z.succ nn) with (nn + 1) in PreH36 by ring.
      rewrite Happ in PreH36.
      replace (carry_2 * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur_2)
        with (list_to_Z UINT_MOD l_cur_2) in PreH36 by (rewrite PreH38; ring).
      rewrite PreH36.
      replace (list_to_Z UINT_MOD l_done_2 * (UINT_MOD * UINT_MOD ^ nn) * d1_orig +
               r * (UINT_MOD * UINT_MOD ^ nn) +
               (list_to_Z UINT_MOD (sublist 0 nn l_cur_2) +
                Znth nn l_cur_2 0 * UINT_MOD ^ nn))
        with (list_to_Z UINT_MOD l_done_2 * UINT_MOD * UINT_MOD ^ nn * d1_orig +
              (r * UINT_MOD + Znth nn l_cur_2 0) * UINT_MOD ^ nn +
              list_to_Z UINT_MOD (sublist 0 nn l_cur_2)) by ring.
      rewrite PreH6.
      ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_6_4 : mpn_div_qr_1_preinv_entail_wit_6_4.
Proof.
  pre_process.
  Right.
  Exists tn_4 tp_4 np_4 0 qv_done l_done l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - rewrite PreH34, PreH33.
    cancel ((( &( "np" ) )) # Ptr  |-> np0_bare).
    cancel ((( &( "tp" ) )) # Ptr  |-> tp_4).
    cancel ((( &( "tn" ) )) # Int  |-> tn_4).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - assert (Hnn : nn = -1) by lia.
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try entailer!.
    rewrite Hnn in PreH30.
    replace (-1 + 1) with 0 in PreH30 by ring.
    rewrite Z.pow_0_r in PreH30.
    rewrite (Zsublist_nil l_cur_2 0 0) in PreH30 by lia.
    rewrite list_to_Z_nil in PreH30.
    rewrite PreH32 in PreH30.
    rewrite PreH25 in PreH30.
    rewrite PreH30.
    ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_6_3 : mpn_div_qr_1_preinv_entail_wit_6_3.
Proof.
  pre_process.
  Right.
  Exists tn_4 tp_4 np_4 carry_2 qv_done l_done l_cur_2 d0_orig_2 shift_orig_2.
  assert (Hnn : nn = -1) by lia.
  rewrite Hnn.
  replace (-1 + 1) with 0 by ring.
  rewrite UIntArray.undef_seg_empty.
  sep_apply_l_atomic (UIntArray.seg_to_full qp0_bare 0 nn0_bare l_done).
  replace (qp0_bare + 0 * sizeof(UINT)) with qp0_bare by lia.
  replace (nn0_bare - 0) with nn0_bare by lia.
  split_pure_spatial.
  - rewrite PreH34, PreH33.
    cancel ((( &( "np" ) )) # Ptr  |-> np0_bare).
    cancel ((( &( "tp" ) )) # Ptr  |-> tp_4).
    cancel ((( &( "tn" ) )) # Int  |-> tn_4).
    cancel (UIntArray.full qp0_bare nn0_bare l_done).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
    rewrite Hnn in PreH30.
    replace (-1 + 1) with 0 in PreH30 by ring.
    rewrite Z.pow_0_r in PreH30.
    rewrite (Zsublist_nil l_cur_2 0 0) in PreH30 by lia.
    rewrite list_to_Z_nil in PreH30.
    rewrite PreH32 in PreH30.
    rewrite PreH33 in PreH30.
    rewrite PreH25 in PreH30.
    rewrite PreH32, PreH33.
    rewrite PreH30.
    ring.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_6_2 : mpn_div_qr_1_preinv_entail_wit_6_2.
Proof.
  pre_process.
  Left.
  Exists tn_4 carry_2 qv_done l_done l_cur_2 d0_orig_2 shift_orig_2.
  assert (Hnn : nn = -1) by lia.
  assert (Hquot : carry_2 * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur_2 = qv_done * d1_orig + r).
  {
    rewrite Hnn in PreH30.
    replace (-1 + 1) with 0 in PreH30 by ring.
    rewrite Z.pow_0_r in PreH30.
    rewrite (Zsublist_nil l_cur_2 0 0) in PreH30 by lia.
    rewrite list_to_Z_nil in PreH30.
    rewrite PreH25 in PreH30.
    rewrite PreH30.
    ring.
  }
  rewrite Hnn.
  replace (-1 + 1) with 0 by ring.
  rewrite (Zsublist_nil l_cur_2 0 0) by lia.
  rewrite (UIntArray.seg_empty np_4 0 0).
  Intros_p Hempty.
  sep_apply_l_atomic (UIntArray.seg_to_full qp0_bare 0 nn0_bare l_done).
  replace (qp0_bare + 0 * sizeof(UINT)) with qp0_bare by lia.
  replace (nn0_bare - 0) with nn0_bare by lia.
  split_pure_spatial.
  - rewrite PreH33, PreH34, PreH35.
    cancel ((( &( "np" ) )) # Ptr  |-> qp0_bare).
    cancel ((( &( "tp" ) )) # Ptr  |-> qp0_bare).
    cancel ((( &( "tn" ) )) # Int  |-> 0).
    cancel (UIntArray.full qp0_bare nn0_bare l_done).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_entail_wit_6_1 : mpn_div_qr_1_preinv_entail_wit_6_1.
Proof.
  unfold mpn_div_qr_1_preinv_entail_wit_6_1.
  left.
  intros.
  Exists 0 0 tp_4 np_4 carry_2 qv_done l_done l_cur_2 d0_orig_2 shift_orig_2.
  split_pure_spatial.
  - rewrite PreH33.
    sep_apply_l_atomic (UIntArray_full_to_empty_mpd_store_Z_compact_undef_seg tp_4 nn0_bare l_cur_2).
    cancel ((( &( "np" ) )) # Ptr  |-> tp_4).
    cancel ((( &( "tp" ) )) # Ptr  |-> tp_4).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    cancel (mpd_store_Z_compact UINT_MOD tp_4 0 0).
    cancel (UIntArray.undef_seg tp_4 0 nn0_bare).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig_2).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
    cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
  - assert (Hnn : nn = -1) by lia.
    assert (Hquot : carry_2 * UINT_MOD ^ nn0_bare + list_to_Z UINT_MOD l_cur_2 = qv_done * d1_orig + r).
    {
      rewrite Hnn in PreH30.
      replace (-1 + 1) with 0 in PreH30 by ring.
      rewrite Z.pow_0_r in PreH30.
      rewrite (Zsublist_nil l_cur_2 0 0) in PreH30 by lia.
      rewrite list_to_Z_nil in PreH30.
      rewrite PreH25 in PreH30.
      rewrite PreH30.
      ring.
    }
    split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_return_wit_1 : mpn_div_qr_1_preinv_return_wit_1.
Proof.
  pre_process.
  
  Exists qv_2 l_q_2.
  assert (Hvalid : gmp_div_inverse_valid 1 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    destruct (Z.eq_dec 1 1) as [_ | Hneq]; [| lia].
    change (UINT_MOD ^ 1) with UINT_MOD.
    repeat split; try lia; try exact PreH5; try exact PreH6; try exact PreH12; try exact PreH13.
  }
  assert (Hd1 : d1_orig = d_orig_bare).
  {
    rewrite PreH27 in PreH4.
    rewrite Z.pow_0_r in PreH4.
    lia.
  }
  split_pure_spatial.
  - cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    split_pure_spatial.
    + cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
    + apply derivable1s_coq_prop_r.
      exact Hvalid.
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
    + rewrite PreH27, Z.shiftr_0_r.
      rewrite <- PreH29.
      rewrite PreH28 in PreH24.
      rewrite Z.mul_0_l, Z.add_0_l in PreH24.
      rewrite Hd1 in PreH24.
      exact PreH24.
    + rewrite PreH27, Z.shiftr_0_r.
      exact PreH25.
    + rewrite PreH27, Z.shiftr_0_r.
      rewrite Hd1 in PreH26.
      exact PreH26.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_return_wit_2 : mpn_div_qr_1_preinv_return_wit_2.
Proof.
  pre_process.
  
  Exists qv_2 l_q_2.
  assert (Hvalid : gmp_div_inverse_valid 1 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    destruct (Z.eq_dec 1 1) as [_ | Hneq]; [| lia].
    change (UINT_MOD ^ 1) with UINT_MOD.
    repeat split; try lia; try exact PreH5; try exact PreH6; try exact PreH12; try exact PreH13.
  }
  assert (Hd1 : d1_orig = d_orig_bare).
  {
    rewrite PreH27 in PreH4.
    rewrite Z.pow_0_r in PreH4.
    lia.
  }
  split_pure_spatial.
  - cancel (UIntArray.full qp0_bare nn0_bare l_q_2).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    split_pure_spatial.
    + cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
    + apply derivable1s_coq_prop_r.
      exact Hvalid.
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
    + rewrite PreH27, Z.shiftr_0_r.
      rewrite <- PreH29.
      rewrite PreH28 in PreH24.
      rewrite Z.mul_0_l, Z.add_0_l in PreH24.
      rewrite Hd1 in PreH24.
      exact PreH24.
    + rewrite PreH27, Z.shiftr_0_r.
      exact PreH25.
    + rewrite PreH27, Z.shiftr_0_r.
      rewrite Hd1 in PreH26.
      exact PreH26.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_return_wit_3 : mpn_div_qr_1_preinv_return_wit_3.
Proof.
  pre_process.
  
  Exists qv_2 l_q_2.
  assert (Hvalid : gmp_div_inverse_valid 1 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    destruct (Z.eq_dec 1 1) as [_ | Hneq]; [| lia].
    change (UINT_MOD ^ 1) with UINT_MOD.
    repeat split; try lia; try exact PreH5; try exact PreH6; try exact PreH12; try exact PreH13.
  }
  set (S := 2 ^ shift_orig) in *.
  set (N := list_to_Z UINT_MOD l_np_bare) in *.
  assert (HS : 0 < S).
  {
    subst S.
    apply Z.pow_pos_nonneg; lia.
  }
  assert (Hnorm : N * S = qv_2 * (d_orig_bare * S) + r).
  {
    rewrite <- PreH30.
    rewrite PreH24.
    rewrite PreH4.
    ring.
  }
  assert (Hr_div : r / S = N - qv_2 * d_orig_bare).
  {
    assert (Hr : r = (N - qv_2 * d_orig_bare) * S) by nia.
    rewrite Hr.
    rewrite Z.div_mul by lia.
    ring.
  }
  split_pure_spatial.
  - cancel (UIntArray.full qp0_bare nn0_bare l_q_2).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    split_pure_spatial.
    + cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
    + apply derivable1s_coq_prop_r.
      exact Hvalid.
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
    + subst N S.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Hr_div.
      ring.
    + rewrite Z.shiftr_div_pow2 by lia.
      fold S.
      apply Z.div_pos; lia.
    + rewrite Z.shiftr_div_pow2 by lia.
      fold S.
      apply Z.div_lt_upper_bound; try lia.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_return_wit_4 : mpn_div_qr_1_preinv_return_wit_4.
Proof.
  pre_process.
  
  Exists qv_2 l_q_2.
  assert (Hvalid : gmp_div_inverse_valid 1 d_orig_bare shift_orig d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    destruct (Z.eq_dec 1 1) as [_ | Hneq]; [| lia].
    change (UINT_MOD ^ 1) with UINT_MOD.
    repeat split; try lia; try exact PreH5; try exact PreH6; try exact PreH12; try exact PreH13.
  }
  set (S := 2 ^ shift_orig) in *.
  set (N := list_to_Z UINT_MOD l_np_bare) in *.
  assert (HS : 0 < S).
  {
    subst S.
    apply Z.pow_pos_nonneg; lia.
  }
  assert (Hnorm : N * S = qv_2 * (d_orig_bare * S) + r).
  {
    rewrite <- PreH30.
    rewrite PreH24.
    rewrite PreH4.
    ring.
  }
  assert (Hr_div : r / S = N - qv_2 * d_orig_bare).
  {
    assert (Hr : r = (N - qv_2 * d_orig_bare) * S) by nia.
    rewrite Hr.
    rewrite Z.div_mul by lia.
    ring.
  }
  split_pure_spatial.
  - cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
    unfold store_div_inverse, div_inverse_store.
    Exists shift_orig d1_orig d0_orig di_orig.
    split_pure_spatial.
    + cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"shift")) # UInt  |-> shift_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d1")) # UInt  |-> d1_orig).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"d0")) # UInt  |->_).
      cancel ((&((inv0_bare)  # "gmp_div_inverse" ->ₛ"di")) # UInt  |-> di_orig).
    + apply derivable1s_coq_prop_r.
      exact Hvalid.
  - split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
    + subst N S.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Hr_div.
      ring.
    + rewrite Z.shiftr_div_pow2 by lia.
      fold S.
      apply Z.div_pos; lia.
    + rewrite Z.shiftr_div_pow2 by lia.
      fold S.
      apply Z.div_lt_upper_bound; try lia.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_partial_solve_wit_8_pure : mpn_div_qr_1_preinv_partial_solve_wit_8_pure.
Proof.
  unfold mpn_div_qr_1_preinv_partial_solve_wit_8_pure.
  right.
  intros.
  split_pures.
  - dump_pre_spatial.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH32) as [Hlo Hhi].
    exact Hlo.
  - dump_pre_spatial.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH32) as [Hlo Hhi].
    change UINT_MAX with 4294967295.
    change UINT_MOD with 4294967296 in Hhi.
    lia.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_partial_solve_wit_9_pure : mpn_div_qr_1_preinv_partial_solve_wit_9_pure.
Proof.
  unfold mpn_div_qr_1_preinv_partial_solve_wit_9_pure.
  right.
  intros.
  split_pures.
  - dump_pre_spatial.
    rewrite Znth_sublist by lia.
    match goal with
    | |- context [Znth ?i l_cur 0] => replace i with nn by lia
    end.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH33) as [Hlo Hhi].
    exact Hlo.
  - dump_pre_spatial.
    rewrite Znth_sublist by lia.
    match goal with
    | |- context [Znth ?i l_cur 0] => replace i with nn by lia
    end.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH33) as [Hlo Hhi].
    change UINT_MAX with 4294967295.
    change UINT_MOD with 4294967296 in Hhi.
    lia.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_partial_solve_wit_10_pure : mpn_div_qr_1_preinv_partial_solve_wit_10_pure.
Proof.
  unfold mpn_div_qr_1_preinv_partial_solve_wit_10_pure.
  right.
  intros.
  split_pures.
  - dump_pre_spatial.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH33) as [Hlo Hhi].
    exact Hlo.
  - dump_pre_spatial.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH33) as [Hlo Hhi].
    change UINT_MAX with 4294967295.
    change UINT_MOD with 4294967296 in Hhi.
    lia.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_partial_solve_wit_11_pure : mpn_div_qr_1_preinv_partial_solve_wit_11_pure.
Proof.
  unfold mpn_div_qr_1_preinv_partial_solve_wit_11_pure.
  right.
  intros.
  split_pures.
  - dump_pre_spatial.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH33) as [Hlo Hhi].
    exact Hlo.
  - dump_pre_spatial.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos l_cur nn ltac:(lia) PreH33) as [Hlo Hhi].
    change UINT_MAX with 4294967295.
    change UINT_MOD with 4294967296 in Hhi.
    lia.
Qed.

Lemma proof_of_mpn_div_qr_1_preinv_derive_optional_by_bare : mpn_div_qr_1_preinv_derive_optional_by_bare.
Proof.
  pre_process.
  unfold optional_q_undef.
  Split.
  - Intros_p Hnull.
    Exists qp_pre np_pre nn_pre inv_pre l_np_optional d_orig_optional.
    Right.
    split_pure_spatial.
    + cancel (UIntArray.full np_pre nn_pre l_np_optional).
      cancel (store_div_inverse inv_pre 1 d_orig_optional).
      apply derivable1_wand_sepcon_adjoint.
      Split.
      * Intros qv_2.
        Intros l_q_2.
        Intros retval_2.
        Intros.
        Intros.
        entailer!.
      * Intros qv_2.
        Intros l_q_2.
        Intros retval_2.
        Intros.
        Intros.
        Exists qv_2 l_q_2 retval_2.
        unfold optional_q_full.
        Left.
        split_pure_spatial.
        -- rewrite H0, H1, H2.
           cancel (UIntArray.full np_pre nn_pre l_np_optional).
           cancel (store_div_inverse inv_pre 1 d_orig_optional).
        -- split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
  - Intros_p Hnonnull.
    prop_apply_p (UIntArray_undef_full_full_base_neq qp_pre np_pre nn_pre l_np_optional ltac:(lia) ltac:(assumption)).
    Intros.
    Exists qp_pre np_pre nn_pre inv_pre l_np_optional d_orig_optional.
    Left.
    split_pure_spatial.
    + cancel (UIntArray.undef_full qp_pre nn_pre).
      cancel (UIntArray.full np_pre nn_pre l_np_optional).
      cancel (store_div_inverse inv_pre 1 d_orig_optional).
      apply derivable1_wand_sepcon_adjoint.
      Split.
      * Intros qv_2.
        Intros l_q_2.
        Intros retval_2.
        Intros.
        Intros.
        Exists qv_2 l_q_2 retval_2.
        unfold optional_q_full.
        Right.
        split_pure_spatial.
        -- rewrite H, H0, H1, H2.
           cancel (UIntArray.full qp_pre nn_pre l_q_2).
           cancel (UIntArray.full np_pre nn_pre l_np_optional).
           cancel (store_div_inverse inv_pre 1 d_orig_optional).
        -- split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
      * Intros qv_2.
        Intros l_q_2.
        Intros retval_2.
        Intros.
        Intros.
        entailer!.
    + split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; entailer!.
Qed.
