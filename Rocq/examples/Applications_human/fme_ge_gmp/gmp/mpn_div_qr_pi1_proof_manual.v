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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_pi1_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_pi1_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_pi1_entail_wit_1_1 : mpn_div_qr_pi1_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists (n1_pre * UINT_MOD ^ nn_pre + list_to_Z UINT_MOD l_np_bare) 0 (@nil Z) l_np_bare.
  split_pure_spatial.
  -
    rewrite <- PreH1, <- PreH2, <- PreH3, <- PreH4, <- PreH5.
    sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg qp0_bare (nn0_bare - dn0_bare + 1)).
    rewrite (UIntArray.seg_empty qp0_bare (nn0_bare - dn0_bare + 1) (nn0_bare - dn0_bare + 1)).
    cancel.
    split_pure_spatial; [cancel | dump_pre_spatial; reflexivity].
  -
    split_pures.
    all: try (dump_pre_spatial; subst; rewrite ?Zlength_nil, ?list_to_Z_nil;
              try rewrite (sublist_self l_np_bare nn_pre) by lia; try ring; try lia).
    exact PreH12.
    exact PreH13.
    replace (Zlength l_dp_bare + (Zlength l_np_bare - Zlength l_dp_bare)) with (Zlength l_np_bare) by ring.
    rewrite (sublist_self l_np_bare (Zlength l_np_bare)) by reflexivity.
    ring.
    pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_np_bare PreH12) as Hpos.
    pose proof (Z.pow_nonneg UINT_MOD (Zlength l_np_bare) ltac:(unfold UINT_MOD; lia)) as Hpow.
    nia.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_1_2 : mpn_div_qr_pi1_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists (n1_pre * UINT_MOD ^ nn_pre + list_to_Z UINT_MOD l_np_bare) 0 (@nil Z) l_np_bare.
  split_pure_spatial.
  -
    rewrite <- PreH1, <- PreH2, <- PreH3, <- PreH4, <- PreH5.
    cancel (UIntArray.full dp0_bare dn0_bare l_dp_bare).
    cancel ((( &( "dn") )) # Int |-> dn0_bare).
    cancel ((( &( "dp") )) # Ptr |-> dp0_bare).
    cancel ((( &( "nn") )) # Int |-> nn0_bare).
    cancel ((( &( "np") )) # Ptr |-> np0_bare).
    cancel ((( &( "qp") )) # Ptr |-> qp0_bare).
    cancel (UIntArray.full np0_bare nn0_bare l_np_bare).
  -
    split_pures.
    all: try (dump_pre_spatial; subst; rewrite ?Zlength_nil, ?list_to_Z_nil;
              try rewrite (sublist_self l_np_bare nn_pre) by lia; try ring; try lia).
    exact PreH12.
    exact PreH13.
    replace (Zlength l_dp_bare + (Zlength l_np_bare - Zlength l_dp_bare)) with (Zlength l_np_bare) by ring.
    rewrite (sublist_self l_np_bare (Zlength l_np_bare)) by reflexivity.
    ring.
    pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_np_bare PreH12) as Hpos.
    pose proof (Z.pow_nonneg UINT_MOD (Zlength l_np_bare) ltac:(unfold UINT_MOD; lia)) as Hpow.
    nia.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_2_1 : mpn_div_qr_pi1_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv_2 qv_done_2
    (sublist (i + dn0_bare) nn0_bare l_cur_2)
    (sublist i (i + dn0_bare) l_cur_2)
    (sublist 0 i l_cur_2)
    l_done_2 l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_to_seg np0_bare nn0_bare l_cur_2).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np0_bare 0 i nn0_bare l_cur_2).
    + dump_pre_spatial; lia.
    + replace (i - 0) with i by ring.
      replace (nn0_bare - 0) with nn0_bare by ring.
      sep_apply_l_atomic (UIntArray.seg_split_to_seg np0_bare i (i + dn0_bare) nn0_bare (sublist i nn0_bare l_cur_2)).
      * dump_pre_spatial; lia.
      * replace (i + dn0_bare - i) with dn0_bare by ring.
        rewrite (Zsublist_Zsublist dn0_bare nn0_bare 0 i l_cur_2) by lia.
        replace (nn0_bare - i) with (nn0_bare - i) by ring.
        rewrite (Zsublist_Zsublist (nn0_bare - i) nn0_bare dn0_bare i l_cur_2) by lia.
        replace (0 + i) with i by ring.
        replace (dn0_bare + i) with (i + dn0_bare) by ring.
        replace (nn0_bare - i + i) with nn0_bare by ring.
        sep_apply_l_atomic (UIntArray.seg_to_full np0_bare i (i + dn0_bare) (sublist i (i + dn0_bare) l_cur_2)).
        replace (i + dn0_bare - i) with dn0_bare by ring.
        cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; subst;
              rewrite ?Zlength_sublist, ?PreH9; try lia; try ring;
              try assumption; try reflexivity).
    all: try (dump_pre_spatial; eapply list_within_bound_sublist;
              [lia | rewrite PreH9; lia | exact PreH12]).
    eapply list_within_bound_sublist; [lia | lia | exact PreH12].
    eapply list_within_bound_sublist; [lia | lia | exact PreH12].
    eapply list_within_bound_sublist; [lia | lia | exact PreH12].
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_2_2 : mpn_div_qr_pi1_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv_2 qv_done_2
    (sublist (i + dn0_bare) nn0_bare l_cur_2)
    (sublist i (i + dn0_bare) l_cur_2)
    (sublist 0 i l_cur_2)
    l_done_2 l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_to_seg np0_bare nn0_bare l_cur_2).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np0_bare 0 i nn0_bare l_cur_2).
    + dump_pre_spatial; lia.
    + replace (i - 0) with i by ring.
      replace (nn0_bare - 0) with nn0_bare by ring.
      sep_apply_l_atomic (UIntArray.seg_split_to_seg np0_bare i (i + dn0_bare) nn0_bare (sublist i nn0_bare l_cur_2)).
      * dump_pre_spatial; lia.
      * replace (i + dn0_bare - i) with dn0_bare by ring.
        rewrite (Zsublist_Zsublist dn0_bare nn0_bare 0 i l_cur_2) by lia.
        replace (nn0_bare - i) with (nn0_bare - i) by ring.
        rewrite (Zsublist_Zsublist (nn0_bare - i) nn0_bare dn0_bare i l_cur_2) by lia.
        replace (0 + i) with i by ring.
        replace (dn0_bare + i) with (i + dn0_bare) by ring.
        replace (nn0_bare - i + i) with nn0_bare by ring.
        sep_apply_l_atomic (UIntArray.seg_to_full np0_bare i (i + dn0_bare) (sublist i (i + dn0_bare) l_cur_2)).
        replace (i + dn0_bare - i) with dn0_bare by ring.
        cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; subst;
              rewrite ?Zlength_sublist, ?PreH9; try lia; try ring;
              try assumption; try reflexivity).
    all: try (dump_pre_spatial; eapply list_within_bound_sublist;
              [lia | rewrite PreH9; lia | exact PreH12]).
    eapply list_within_bound_sublist; [lia | lia | exact PreH12].
    eapply list_within_bound_sublist; [lia | lia | exact PreH12].
    eapply list_within_bound_sublist; [lia | lia | exact PreH12].
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_4_4 : mpn_div_qr_pi1_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv_2 n1 qv_done_2
    (sublist (dn0_bare - 2) dn0_bare l_dp_bare)
    (sublist 0 (dn0_bare - 2) l_dp_bare)
    (sublist (dn0_bare - 2) dn0_bare l_mid_2)
    (sublist 0 (dn0_bare - 2) l_mid_2)
    l_high_2 l_mid_2 l_low_2 l_done_2 l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_to_seg np_i dn0_bare l_mid_2).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np_i 0 (dn0_bare - 2) dn0_bare l_mid_2).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      replace (dn0_bare - 0) with dn0_bare by ring.
      sep_apply_l_atomic (UIntArray.seg_to_full np_i 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_mid_2)).
      replace (np_i + 0 * sizeof(UINT)) with np_i by lia.
      replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      sep_apply_l_atomic (UIntArray.full_to_seg dp0_bare dn0_bare l_dp_bare).
      sep_apply_l_atomic (UIntArray.seg_split_to_seg dp0_bare 0 (dn0_bare - 2) dn0_bare l_dp_bare).
      * dump_pre_spatial; lia.
      * replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        replace (dn0_bare - 0) with dn0_bare by ring.
        sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_dp_bare)).
        replace (dp0_bare + 0 * sizeof(UINT)) with dp0_bare by lia.
        replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial.
    clear -PreH13 PreH25.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH13 PreH25.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH13 PreH19.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH13 PreH19.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH25; lia | exact PreH31].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH25; lia | exact PreH31].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH28].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH28].
    dump_pre_spatial.
    set (a := Znth (dn0_bare - 1) l_mid_2 0) in *.
    set (c := Znth (dn0_bare - 2) l_mid_2 0) in *.
    assert (HA : 0 <= a < UINT_MOD).
    { subst a. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 1)); [rewrite PreH25; lia | exact PreH31]. }
    assert (HC : 0 <= c < UINT_MOD).
    { subst c. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 2)); [rewrite PreH25; lia | exact PreH31]. }
    change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD) in PreH8.
    assert (Hbase : UINT_MOD = 4294967296) by reflexivity.
    clear PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 l_dp_bare l_np_bare l_cur_2 l_done_2 l_low_2 l_high_2 np_i n1_orig_bare nn0_bare dp0_bare np0_bare qp0_bare remv_2 qv_done_2 dinv.
    assert (HDpos : 0 < d1 * UINT_MOD + d0) by (rewrite Hbase in *; nia).
    assert (Hq_lt_base : qv < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (Hd0_lt_base : d0 < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (HA_lt_d0 : a < d0).
    {
      destruct (Z_lt_ge_dec a d0) as [Hlt | Hge].
      - exact Hlt.
      - assert (Hgt : a >= d0 + 1) by lia.
        assert (Hupper : qv * (d1 * UINT_MOD + d0) + rv1 * UINT_MOD + rv0 <
                         UINT_MOD * (d1 * UINT_MOD + d0)) by nia.
        assert (Hlower : n1 * (UINT_MOD * UINT_MOD) + a * UINT_MOD + c >=
                         UINT_MOD * (d1 * UINT_MOD + d0)) by (subst n1; nia).
        lia.
    }
    subst n1.
    nia.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_4_3 : mpn_div_qr_pi1_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv_2 n1 qv_done_2
    (sublist (dn0_bare - 2) dn0_bare l_dp_bare)
    (sublist 0 (dn0_bare - 2) l_dp_bare)
    (sublist (dn0_bare - 2) dn0_bare l_mid_2)
    (sublist 0 (dn0_bare - 2) l_mid_2)
    l_high_2 l_mid_2 l_low_2 l_done_2 l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_to_seg np_i dn0_bare l_mid_2).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np_i 0 (dn0_bare - 2) dn0_bare l_mid_2).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      replace (dn0_bare - 0) with dn0_bare by ring.
      sep_apply_l_atomic (UIntArray.seg_to_full np_i 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_mid_2)).
      replace (np_i + 0 * sizeof(UINT)) with np_i by lia.
      replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      sep_apply_l_atomic (UIntArray.full_to_seg dp0_bare dn0_bare l_dp_bare).
      sep_apply_l_atomic (UIntArray.seg_split_to_seg dp0_bare 0 (dn0_bare - 2) dn0_bare l_dp_bare).
      * dump_pre_spatial; lia.
      * replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        replace (dn0_bare - 0) with dn0_bare by ring.
        sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_dp_bare)).
        replace (dp0_bare + 0 * sizeof(UINT)) with dp0_bare by lia.
        replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial.
    clear -PreH13 PreH25.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH13 PreH25.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH13 PreH19.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH13 PreH19.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH25; lia | exact PreH31].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH25; lia | exact PreH31].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH28].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH19; lia | exact PreH28].
    dump_pre_spatial.
    set (a := Znth (dn0_bare - 1) l_mid_2 0) in *.
    set (c := Znth (dn0_bare - 2) l_mid_2 0) in *.
    assert (HA : 0 <= a < UINT_MOD).
    { subst a. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 1)); [rewrite PreH25; lia | exact PreH31]. }
    assert (HC : 0 <= c < UINT_MOD).
    { subst c. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 2)); [rewrite PreH25; lia | exact PreH31]. }
    change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD) in PreH8.
    assert (Hbase : UINT_MOD = 4294967296) by reflexivity.
    clear PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 l_dp_bare l_np_bare l_cur_2 l_done_2 l_low_2 l_high_2 np_i n1_orig_bare nn0_bare dp0_bare np0_bare qp0_bare remv_2 qv_done_2 dinv.
    assert (HDpos : 0 < d1 * UINT_MOD + d0) by (rewrite Hbase in *; nia).
    assert (Hq_lt_base : qv < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (Hd0_lt_base : d0 < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (HA_lt_d0 : a < d0).
    {
      destruct (Z_lt_ge_dec a d0) as [Hlt | Hge].
      - exact Hlt.
      - assert (Hgt : a >= d0 + 1) by lia.
        assert (Hupper : qv * (d1 * UINT_MOD + d0) + rv1 * UINT_MOD + rv0 <
                         UINT_MOD * (d1 * UINT_MOD + d0)) by nia.
        assert (Hlower : n1 * (UINT_MOD * UINT_MOD) + a * UINT_MOD + c >=
                         UINT_MOD * (d1 * UINT_MOD + d0)) by (subst n1; nia).
        lia.
    }
    subst n1.
    nia.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_4_2 : mpn_div_qr_pi1_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv_2 n1 qv_done_2
    (sublist (dn0_bare - 2) dn0_bare l_dp_bare)
    (sublist 0 (dn0_bare - 2) l_dp_bare)
    (sublist (dn0_bare - 2) dn0_bare l_mid_2)
    (sublist 0 (dn0_bare - 2) l_mid_2)
    l_high_2 l_mid_2 l_low_2 l_done_2 l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_to_seg np_i dn0_bare l_mid_2).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np_i 0 (dn0_bare - 2) dn0_bare l_mid_2).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      replace (dn0_bare - 0) with dn0_bare by ring.
      sep_apply_l_atomic (UIntArray.seg_to_full np_i 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_mid_2)).
      replace (np_i + 0 * sizeof(UINT)) with np_i by lia.
      replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      sep_apply_l_atomic (UIntArray.full_to_seg dp0_bare dn0_bare l_dp_bare).
      sep_apply_l_atomic (UIntArray.seg_split_to_seg dp0_bare 0 (dn0_bare - 2) dn0_bare l_dp_bare).
      * dump_pre_spatial; lia.
      * replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        replace (dn0_bare - 0) with dn0_bare by ring.
        sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_dp_bare)).
        replace (dp0_bare + 0 * sizeof(UINT)) with dp0_bare by lia.
        replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial.
    clear -PreH12 PreH24.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH12 PreH24.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH12 PreH18.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH12 PreH18.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH24; lia | exact PreH30].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH24; lia | exact PreH30].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH18; lia | exact PreH27].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH18; lia | exact PreH27].
    dump_pre_spatial.
    set (a := Znth (dn0_bare - 1) l_mid_2 0) in *.
    set (c := Znth (dn0_bare - 2) l_mid_2 0) in *.
    assert (HA : 0 <= a < UINT_MOD).
    { subst a. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 1)); [rewrite PreH24; lia | exact PreH30]. }
    assert (HC : 0 <= c < UINT_MOD).
    { subst c. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 2)); [rewrite PreH24; lia | exact PreH30]. }
    change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD) in PreH8.
    assert (Hbase : UINT_MOD = 4294967296) by reflexivity.
    clear PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 l_dp_bare l_np_bare l_cur_2 l_done_2 l_low_2 l_high_2 np_i n1_orig_bare nn0_bare dp0_bare np0_bare qp0_bare remv_2 qv_done_2 dinv.
    assert (HDpos : 0 < d1 * UINT_MOD + d0) by (rewrite Hbase in *; nia).
    assert (Hq_lt_base : qv < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (Hd0_lt_base : d0 < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (Hn1_lt_d1 : n1 < d1).
    {
      destruct (Z_lt_ge_dec n1 d1) as [Hlt | Hge].
      - exact Hlt.
      - assert (Hgt : n1 >= d1 + 1) by lia.
        assert (Hupper : qv * (d1 * UINT_MOD + d0) + rv1 * UINT_MOD + rv0 <
                         UINT_MOD * (d1 * UINT_MOD + d0)) by nia.
        assert (Hlower : n1 * (UINT_MOD * UINT_MOD) + a * UINT_MOD + c >=
                         (d1 + 1) * (UINT_MOD * UINT_MOD)) by nia.
        assert (Hbase_upper : UINT_MOD * (d1 * UINT_MOD + d0) <
                              (d1 + 1) * (UINT_MOD * UINT_MOD)) by nia.
        lia.
    }
    nia.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_4_1 : mpn_div_qr_pi1_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv_2 n1 qv_done_2
    (sublist (dn0_bare - 2) dn0_bare l_dp_bare)
    (sublist 0 (dn0_bare - 2) l_dp_bare)
    (sublist (dn0_bare - 2) dn0_bare l_mid_2)
    (sublist 0 (dn0_bare - 2) l_mid_2)
    l_high_2 l_mid_2 l_low_2 l_done_2 l_cur_2.
  split_pure_spatial.
  -
    sep_apply_l_atomic (UIntArray.full_to_seg np_i dn0_bare l_mid_2).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np_i 0 (dn0_bare - 2) dn0_bare l_mid_2).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      replace (dn0_bare - 0) with dn0_bare by ring.
      sep_apply_l_atomic (UIntArray.seg_to_full np_i 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_mid_2)).
      replace (np_i + 0 * sizeof(UINT)) with np_i by lia.
      replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
      sep_apply_l_atomic (UIntArray.full_to_seg dp0_bare dn0_bare l_dp_bare).
      sep_apply_l_atomic (UIntArray.seg_split_to_seg dp0_bare 0 (dn0_bare - 2) dn0_bare l_dp_bare).
      * dump_pre_spatial; lia.
      * replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        replace (dn0_bare - 0) with dn0_bare by ring.
        sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare 0 (dn0_bare - 2) (sublist 0 (dn0_bare - 2) l_dp_bare)).
        replace (dp0_bare + 0 * sizeof(UINT)) with dp0_bare by lia.
        replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
        cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial.
    clear -PreH12 PreH24.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH12 PreH24.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH12 PreH18.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    clear -PreH12 PreH18.
    rewrite Zlength_sublist by lia.
    lia.
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH24; lia | exact PreH30].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH24; lia | exact PreH30].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH18; lia | exact PreH27].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH18; lia | exact PreH27].
    dump_pre_spatial.
    set (a := Znth (dn0_bare - 1) l_mid_2 0) in *.
    set (c := Znth (dn0_bare - 2) l_mid_2 0) in *.
    assert (HA : 0 <= a < UINT_MOD).
    { subst a. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 1)); [rewrite PreH24; lia | exact PreH30]. }
    assert (HC : 0 <= c < UINT_MOD).
    { subst c. apply (list_within_bound_Znth_bound UINT_MOD l_mid_2 (dn0_bare - 2)); [rewrite PreH24; lia | exact PreH30]. }
    change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD) in PreH8.
    assert (Hbase : UINT_MOD = 4294967296) by reflexivity.
    clear PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 l_dp_bare l_np_bare l_cur_2 l_done_2 l_low_2 l_high_2 np_i n1_orig_bare nn0_bare dp0_bare np0_bare qp0_bare remv_2 qv_done_2 dinv.
    assert (HDpos : 0 < d1 * UINT_MOD + d0) by (rewrite Hbase in *; nia).
    assert (Hq_lt_base : qv < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (Hd0_lt_base : d0 < UINT_MOD) by (rewrite Hbase in *; lia).
    assert (Hn1_lt_d1 : n1 < d1).
    {
      destruct (Z_lt_ge_dec n1 d1) as [Hlt | Hge].
      - exact Hlt.
      - assert (Hgt : n1 >= d1 + 1) by lia.
        assert (Hupper : qv * (d1 * UINT_MOD + d0) + rv1 * UINT_MOD + rv0 <
                         UINT_MOD * (d1 * UINT_MOD + d0)) by nia.
        assert (Hlower : n1 * (UINT_MOD * UINT_MOD) + a * UINT_MOD + c >=
                         (d1 + 1) * (UINT_MOD * UINT_MOD)) by nia.
        assert (Hbase_upper : UINT_MOD * (d1 * UINT_MOD + d0) <
                              (d1 + 1) * (UINT_MOD * UINT_MOD)) by nia.
        lia.
    }
    nia.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_6_1 : mpn_div_qr_pi1_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_repl := replace_Znth 0 (unsigned_last_nbits (n0 - retval) 32) l_mid_high_2).
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact PreH41. }
  assert (Hlrepl_bound : list_within_bound UINT_MOD l_repl).
  { subst l_repl.
    rewrite PreH34.
    rewrite replace_Znth_sublist_head.
    2: { rewrite PreH38. lia. }
    simpl.
    split.
    - pose proof (unsigned_Lastnbits_range (n0 - retval) 32 ltac:(lia)) as Hrange.
      change (2 ^ 32) with UINT_MOD in Hrange.
      lia.
    - eapply list_within_bound_sublist; [lia | rewrite PreH38; lia | exact PreH48]. }
  Exists remv_2. Exists n0. Exists n1. Exists n1_in_2. Exists retval.
  Exists (list_to_Z UINT_MOD (l_dp_low_2 ++ sublist 0 1 l_dp_high_2)).
  Exists (list_to_Z UINT_MOD (l_out_2 ++ sublist 0 1 l_repl)).
  Exists val_out_2. Exists qv_done_2.
  Exists (sublist 1 2 l_dp_high_2).
  Exists (l_dp_low_2 ++ sublist 0 1 l_dp_high_2).
  Exists (sublist 1 2 l_repl).
  Exists l_out_2.
  Exists (l_out_2 ++ sublist 0 1 l_repl).
  Exists l_dp_high_2. Exists l_dp_low_2. Exists l_mid_high_2. Exists l_mid_low_2.
  Exists l_high_2. Exists l_mid_2. Exists l_low_2. Exists l_done_2. Exists l_cur_2.
  split_pure_spatial.
  - replace (dn0_bare - 2 - (dn0_bare - 2)) with 0 by ring.
    fold l_repl.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np_i (dn0_bare - 2) (dn0_bare - 1) dn0_bare l_repl).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 1 - (dn0_bare - 2)) with 1 by ring.
      replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
      sep_apply_l_atomic (UIntArray.full_to_seg np_i (dn0_bare - 2) l_out_2).
      sep_apply_l_atomic (UIntArray.seg_merge_to_full np_i 0 (dn0_bare - 2) (dn0_bare - 1) l_out_2 (sublist 0 1 l_repl)).
      * dump_pre_spatial; lia.
      * replace (np_i + 0 * sizeof(UINT)) with np_i by lia.
        replace (dn0_bare - 1 - 0) with (dn0_bare - 1) by ring.
        sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_exact np_i (dn0_bare - 1) (l_out_2 ++ sublist 0 1 l_repl) (list_to_Z UINT_MOD (l_out_2 ++ sublist 0 1 l_repl))).
        { dump_pre_spatial.
          rewrite Zlength_app.
          rewrite PreH16.
          pose proof (Zlength_sublist 0 1 l_repl) as Hsub_len.
          assert (Hsub_pre : 0 <= 0 <= 1 /\ 1 <= Zlength l_repl).
          { rewrite Hlrepl_len. lia. }
          specialize (Hsub_len Hsub_pre).
          rewrite Hsub_len.
          lia. }
        { dump_pre_spatial; reflexivity. }
        { dump_pre_spatial.
          apply list_within_bound_concat.
          exact PreH17.
          eapply list_within_bound_sublist; [lia | rewrite Hlrepl_len; lia | exact Hlrepl_bound]. }
        sep_apply_l_atomic (UIntArray.full_to_seg dp0_bare (dn0_bare - 2) l_dp_low_2).
        sep_apply_l_atomic (UIntArray.seg_split_to_seg dp0_bare (dn0_bare - 2) (dn0_bare - 1) dn0_bare l_dp_high_2).
        { dump_pre_spatial; lia. }
        replace (dn0_bare - 1 - (dn0_bare - 2)) with 1 by ring.
        replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
        sep_apply_l_atomic (UIntArray.seg_merge_to_full dp0_bare 0 (dn0_bare - 2) (dn0_bare - 1) l_dp_low_2 (sublist 0 1 l_dp_high_2)).
        { dump_pre_spatial; lia. }
        replace (dp0_bare + 0 * sizeof(UINT)) with dp0_bare by lia.
        replace (dn0_bare - 1 - 0) with (dn0_bare - 1) by ring.
        sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_exact dp0_bare (dn0_bare - 1) (l_dp_low_2 ++ sublist 0 1 l_dp_high_2) (list_to_Z UINT_MOD (l_dp_low_2 ++ sublist 0 1 l_dp_high_2))).
        { dump_pre_spatial.
          rewrite Zlength_app.
          rewrite PreH42.
          pose proof (Zlength_sublist 0 1 l_dp_high_2) as Hsub_len_dp.
          assert (Hsub_pre_dp : 0 <= 0 <= 1 /\ 1 <= Zlength l_dp_high_2).
          { rewrite PreH43. lia. }
          specialize (Hsub_len_dp Hsub_pre_dp).
          rewrite Hsub_len_dp.
          lia. }
        { dump_pre_spatial; reflexivity. }
        { dump_pre_spatial.
          apply list_within_bound_concat.
          exact PreH52.
          eapply list_within_bound_sublist; [lia | rewrite PreH43; lia | exact PreH53]. }
        cancel.
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial; clear -PreH22; lia.
    dump_pre_spatial.
    clear -PreH22 PreH23 PreH24.
    apply Z.le_trans with (m := dn0_bare).
    replace dn0_bare with ((dn0_bare - 1) + 1) at 2 by ring.
    nia.
    apply Z.le_trans with (m := nn0_bare); assumption.
    dump_pre_spatial.
    rewrite Zlength_app.
    rewrite PreH16.
    pose proof (Zlength_sublist 0 1 l_repl) as Hsub_len_np0.
    assert (Hsub_pre_np0 : 0 <= 0 <= 1 /\ 1 <= Zlength l_repl).
    { rewrite Hlrepl_len. lia. }
    specialize (Hsub_len_np0 Hsub_pre_np0).
    rewrite Hsub_len_np0.
    lia.
    dump_pre_spatial.
    pose proof (Zlength_sublist 1 2 l_repl) as Hsub_len_np1.
    assert (Hsub_pre_np1 : 0 <= 1 <= 2 /\ 2 <= Zlength l_repl).
    { rewrite Hlrepl_len. lia. }
    specialize (Hsub_len_np1 Hsub_pre_np1).
    rewrite Hsub_len_np1.
    lia.
    dump_pre_spatial.
    rewrite Zlength_app.
    rewrite PreH42.
    pose proof (Zlength_sublist 0 1 l_dp_high_2) as Hsub_len_dp0.
    assert (Hsub_pre_dp0 : 0 <= 0 <= 1 /\ 1 <= Zlength l_dp_high_2).
    { rewrite PreH43. lia. }
    specialize (Hsub_len_dp0 Hsub_pre_dp0).
    rewrite Hsub_len_dp0.
    lia.
    dump_pre_spatial.
    pose proof (Zlength_sublist 1 2 l_dp_high_2) as Hsub_len_dp1.
    assert (Hsub_pre_dp1 : 0 <= 1 <= 2 /\ 2 <= Zlength l_dp_high_2).
    { rewrite PreH43. lia. }
    specialize (Hsub_len_dp1 Hsub_pre_dp1).
    rewrite Hsub_len_dp1.
    lia.
    dump_pre_spatial.
    apply list_within_bound_concat.
    exact PreH17.
    eapply list_within_bound_sublist; [lia | rewrite Hlrepl_len; lia | exact Hlrepl_bound].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite Hlrepl_len; lia | exact Hlrepl_bound].
    dump_pre_spatial.
    apply list_within_bound_concat.
    exact PreH52.
    eapply list_within_bound_sublist; [lia | rewrite PreH43; lia | exact PreH53].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH43; lia | exact PreH53].
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_6_2 : mpn_div_qr_pi1_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_repl := replace_Znth 0 (unsigned_last_nbits (n0 - retval) 32) l_mid_high_2).
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact PreH41. }
  assert (Hlrepl_bound : list_within_bound UINT_MOD l_repl).
  { subst l_repl.
    rewrite PreH34.
    rewrite replace_Znth_sublist_head.
    2: { rewrite PreH38. lia. }
    simpl.
    split.
    - pose proof (unsigned_Lastnbits_range (n0 - retval) 32 ltac:(lia)) as Hrange.
      change (2 ^ 32) with UINT_MOD in Hrange.
      lia.
    - eapply list_within_bound_sublist; [lia | rewrite PreH38; lia | exact PreH48]. }
  Exists remv_2. Exists n0. Exists n1. Exists n1_in_2. Exists retval.
  Exists (list_to_Z UINT_MOD (l_dp_low_2 ++ sublist 0 1 l_dp_high_2)).
  Exists (list_to_Z UINT_MOD (l_out_2 ++ sublist 0 1 l_repl)).
  Exists val_out_2. Exists qv_done_2.
  Exists (sublist 1 2 l_dp_high_2).
  Exists (l_dp_low_2 ++ sublist 0 1 l_dp_high_2).
  Exists (sublist 1 2 l_repl).
  Exists l_out_2.
  Exists (l_out_2 ++ sublist 0 1 l_repl).
  Exists l_dp_high_2. Exists l_dp_low_2. Exists l_mid_high_2. Exists l_mid_low_2.
  Exists l_high_2. Exists l_mid_2. Exists l_low_2. Exists l_done_2. Exists l_cur_2.
  split_pure_spatial.
  - replace (dn0_bare - 2 - (dn0_bare - 2)) with 0 by ring.
    fold l_repl.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np_i (dn0_bare - 2) (dn0_bare - 1) dn0_bare l_repl).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 1 - (dn0_bare - 2)) with 1 by ring.
      replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
      sep_apply_l_atomic (UIntArray.full_to_seg np_i (dn0_bare - 2) l_out_2).
      sep_apply_l_atomic (UIntArray.seg_merge_to_full np_i 0 (dn0_bare - 2) (dn0_bare - 1) l_out_2 (sublist 0 1 l_repl)).
      * dump_pre_spatial; lia.
      * replace (np_i + 0 * sizeof(UINT)) with np_i by lia.
        replace (dn0_bare - 1 - 0) with (dn0_bare - 1) by ring.
        sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_exact np_i (dn0_bare - 1) (l_out_2 ++ sublist 0 1 l_repl) (list_to_Z UINT_MOD (l_out_2 ++ sublist 0 1 l_repl))).
        { dump_pre_spatial.
          rewrite Zlength_app.
          rewrite PreH16.
          pose proof (Zlength_sublist 0 1 l_repl) as Hsub_len.
          assert (Hsub_pre : 0 <= 0 <= 1 /\ 1 <= Zlength l_repl).
          { rewrite Hlrepl_len. lia. }
          specialize (Hsub_len Hsub_pre).
          rewrite Hsub_len.
          lia. }
        { dump_pre_spatial; reflexivity. }
        { dump_pre_spatial.
          apply list_within_bound_concat.
          exact PreH17.
          eapply list_within_bound_sublist; [lia | rewrite Hlrepl_len; lia | exact Hlrepl_bound]. }
        sep_apply_l_atomic (UIntArray.full_to_seg dp0_bare (dn0_bare - 2) l_dp_low_2).
        sep_apply_l_atomic (UIntArray.seg_split_to_seg dp0_bare (dn0_bare - 2) (dn0_bare - 1) dn0_bare l_dp_high_2).
        { dump_pre_spatial; lia. }
        replace (dn0_bare - 1 - (dn0_bare - 2)) with 1 by ring.
        replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
        sep_apply_l_atomic (UIntArray.seg_merge_to_full dp0_bare 0 (dn0_bare - 2) (dn0_bare - 1) l_dp_low_2 (sublist 0 1 l_dp_high_2)).
        { dump_pre_spatial; lia. }
        replace (dp0_bare + 0 * sizeof(UINT)) with dp0_bare by lia.
        replace (dn0_bare - 1 - 0) with (dn0_bare - 1) by ring.
        sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_exact dp0_bare (dn0_bare - 1) (l_dp_low_2 ++ sublist 0 1 l_dp_high_2) (list_to_Z UINT_MOD (l_dp_low_2 ++ sublist 0 1 l_dp_high_2))).
        { dump_pre_spatial.
          rewrite Zlength_app.
          rewrite PreH42.
          pose proof (Zlength_sublist 0 1 l_dp_high_2) as Hsub_len_dp.
          assert (Hsub_pre_dp : 0 <= 0 <= 1 /\ 1 <= Zlength l_dp_high_2).
          { rewrite PreH43. lia. }
          specialize (Hsub_len_dp Hsub_pre_dp).
          rewrite Hsub_len_dp.
          lia. }
        { dump_pre_spatial; reflexivity. }
        { dump_pre_spatial.
          apply list_within_bound_concat.
          exact PreH52.
          eapply list_within_bound_sublist; [lia | rewrite PreH43; lia | exact PreH53]. }
        cancel.
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial; clear -PreH22; lia.
    dump_pre_spatial.
    clear -PreH22 PreH23 PreH24.
    apply Z.le_trans with (m := dn0_bare).
    replace dn0_bare with ((dn0_bare - 1) + 1) at 2 by ring.
    nia.
    apply Z.le_trans with (m := nn0_bare); assumption.
    dump_pre_spatial.
    rewrite Zlength_app.
    rewrite PreH16.
    pose proof (Zlength_sublist 0 1 l_repl) as Hsub_len_np0.
    assert (Hsub_pre_np0 : 0 <= 0 <= 1 /\ 1 <= Zlength l_repl).
    { rewrite Hlrepl_len. lia. }
    specialize (Hsub_len_np0 Hsub_pre_np0).
    rewrite Hsub_len_np0.
    lia.
    dump_pre_spatial.
    pose proof (Zlength_sublist 1 2 l_repl) as Hsub_len_np1.
    assert (Hsub_pre_np1 : 0 <= 1 <= 2 /\ 2 <= Zlength l_repl).
    { rewrite Hlrepl_len. lia. }
    specialize (Hsub_len_np1 Hsub_pre_np1).
    rewrite Hsub_len_np1.
    lia.
    dump_pre_spatial.
    rewrite Zlength_app.
    rewrite PreH42.
    pose proof (Zlength_sublist 0 1 l_dp_high_2) as Hsub_len_dp0.
    assert (Hsub_pre_dp0 : 0 <= 0 <= 1 /\ 1 <= Zlength l_dp_high_2).
    { rewrite PreH43. lia. }
    specialize (Hsub_len_dp0 Hsub_pre_dp0).
    rewrite Hsub_len_dp0.
    lia.
    dump_pre_spatial.
    pose proof (Zlength_sublist 1 2 l_dp_high_2) as Hsub_len_dp1.
    assert (Hsub_pre_dp1 : 0 <= 1 <= 2 /\ 2 <= Zlength l_dp_high_2).
    { rewrite PreH43. lia. }
    specialize (Hsub_len_dp1 Hsub_pre_dp1).
    rewrite Hsub_len_dp1.
    lia.
    dump_pre_spatial.
    apply list_within_bound_concat.
    exact PreH17.
    eapply list_within_bound_sublist; [lia | rewrite Hlrepl_len; lia | exact Hlrepl_bound].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite Hlrepl_len; lia | exact Hlrepl_bound].
    dump_pre_spatial.
    apply list_within_bound_concat.
    exact PreH52.
    eapply list_within_bound_sublist; [lia | rewrite PreH43; lia | exact PreH53].
    dump_pre_spatial.
    eapply list_within_bound_sublist; [lia | rewrite PreH43; lia | exact PreH53].
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_1 : mpn_div_qr_pi1_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists (Znth (dn0_bare - 1) l_out 0 * UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_high))).
  Exists (4294967295 + qv_done_2 * UINT_MOD).
  Exists (4294967295 :: l_done_2).
  Exists (l_low ++ l_out ++ l_high).
  split_pure_spatial.
  - replace (i - 1 + 1) with i by lia.
      sep_apply_l_atomic (UIntArray.seg_single qp0_bare i 4294967295).
      sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare i (i + 1) (nn0_bare - dn0_bare + 1) (4294967295 :: nil) l_done_2).
      * dump_pre_spatial; lia.
      * simpl.
        sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
        replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
        replace (i - 0) with i by ring.
        rewrite PreH59.
        sep_apply_l_atomic (UIntArray.full_to_seg (np0_bare + i * sizeof(UINT)) dn0_bare l_out).
        sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) 0 dn0_bare l_out).
        replace (np0_bare + i * sizeof(UINT) + 0 * sizeof(UINT)) with (np0_bare + i * sizeof(UINT)) by lia.
        replace (dn0_bare - 0) with dn0_bare by ring.
        rewrite logic_equiv_sepcon_swap.
        replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare l_out) with
          (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) l_out) by (f_equal; ring).
        sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low l_out).
        { dump_pre_spatial; lia. }
        sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
        replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
        rewrite logic_equiv_sepcon_swap.
        sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ l_out) l_high).
        { dump_pre_spatial; lia. }
        rewrite app_assoc.
        cancel.
        sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) 4294967295).
        cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH20.
    + dump_pre_spatial; exact PreH21.
    + dump_pre_spatial; exact PreH22.
    + dump_pre_spatial; exact PreH23.
    + dump_pre_spatial; exact PreH24.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH33, PreH1, PreH35; lia.
    + dump_pre_spatial; exact PreH28.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH29; lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH39.
      * apply list_within_bound_concat; [exact PreH2 | exact PreH41].
    + dump_pre_spatial; exact PreH37.
    + dump_pre_spatial.
      simpl.
      split.
      * unfold UINT_MOD; lia.
      * exact PreH38.
    + dump_pre_spatial; exact PreH42.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH43.
      unfold UINT_MOD; ring.
    + dump_pre_spatial; exact PreH44.
    + dump_pre_spatial.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_out (dn0_bare - 1)) as Hbound.
      specialize (Hbound ltac:(rewrite PreH1; clear -PreH22; lia) PreH2).
      destruct Hbound as [Hlow _].
      exact Hlow.
    + dump_pre_spatial.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_out (dn0_bare - 1)) as Hbound.
      specialize (Hbound ltac:(rewrite PreH1; clear -PreH22; lia) PreH2).
      destruct Hbound as [_ Hhigh].
      change UINT_MAX with 4294967295.
      unfold UINT_MOD in Hhigh; lia.
    + dump_pre_spatial; exact PreH47.
    + dump_pre_spatial; exact PreH48.
    + dump_pre_spatial; exact PreH49.
    + dump_pre_spatial; exact PreH50.
    + dump_pre_spatial; exact PreH51.
    + dump_pre_spatial; exact PreH52.
    + dump_pre_spatial; exact PreH53.
    + dump_pre_spatial; exact PreH54.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial.
      apply Z.add_nonneg_nonneg.
      * apply Z.mul_nonneg_nonneg.
        -- pose proof (list_within_bound_Znth_bound UINT_MOD l_out (dn0_bare - 1)) as Hbound.
           specialize (Hbound ltac:(rewrite PreH1; clear -PreH22; lia) PreH2).
           destruct Hbound as [Hlow _].
           exact Hlow.
        -- apply Z.pow_nonneg; unfold UINT_MOD; lia.
      * pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos
                      (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_high))) as Hbound.
        assert (Hsub_bound:
          list_within_bound UINT_MOD
            (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_high))).
        {
          apply list_within_bound_sublist.
          - clear -PreH22 PreH25; lia.
          - rewrite !Zlength_app, PreH33, PreH1, PreH35.
            clear -PreH22 PreH23 PreH25 PreH26; lia.
          - apply list_within_bound_concat.
            + exact PreH39.
            + apply list_within_bound_concat; [exact PreH2 | exact PreH41].
        }
        specialize (Hbound Hsub_bound).
        destruct Hbound as [Hnonneg _].
        exact Hnonneg.
    + dump_pre_spatial.
      pose proof (mpn_div_qr_pi1_qmax_transition
        l_cur_2 l_low l_mid l_high l_out l_dp_bare dn0_bare nn0_bare i n1 dval_bare
        val_out retval remv_2
        PreH22 PreH25 PreH26 PreH27 PreH33 PreH34 PreH35 PreH1 PreH28
        PreH30 PreH31 PreH32 PreH36 PreH39 PreH40 PreH41 PreH2 PreH37
        PreH3 PreH4 PreH42 PreH44 (eq_trans PreH19 PreH20)
        (eq_trans PreH18 PreH21)
        ltac:(rewrite PreH19; exact PreH47)
        ltac:(rewrite PreH19; exact PreH48)
        PreH55 PreH56 PreH57) as [_ [_ Hrem_lt]].
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      pose proof (mpn_div_qr_pi1_qmax_transition
        l_cur_2 l_low l_mid l_high l_out l_dp_bare dn0_bare nn0_bare i n1 dval_bare
        val_out retval remv_2
        PreH22 PreH25 PreH26 PreH27 PreH33 PreH34 PreH35 PreH1 PreH28
        PreH30 PreH31 PreH32 PreH36 PreH39 PreH40 PreH41 PreH2 PreH37
        PreH3 PreH4 PreH42 PreH44 (eq_trans PreH19 PreH20)
        (eq_trans PreH18 PreH21)
        ltac:(rewrite PreH19; exact PreH47)
        ltac:(rewrite PreH19; exact PreH48)
        PreH55 PreH56 PreH57) as [Hrem_eq _].
      rewrite PreH58.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      {
        replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring.
      }
      rewrite Hpow.
      unfold UINT_MOD.
      ring.
    + dump_pre_spatial; exact PreH60.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_2 : mpn_div_qr_pi1_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold mpd_store_Z, mpd_store_list.
  Intros data_np data_dp.
  destruct H as [Hdata_np_val Hdata_np_bound].
  destruct H1 as [Hdata_dp_val Hdata_dp_bound].
  assert (Hmid_bound : list_within_bound UINT_MOD l_mid).
  { rewrite PreH15. eapply list_within_bound_sublist; [lia | rewrite PreH11; lia | exact PreH37]. }
  assert (Hmidlow_bound : list_within_bound UINT_MOD l_mid_low).
  { rewrite PreH17. eapply list_within_bound_sublist; [lia | rewrite PreH26; lia | exact Hmid_bound]. }
  assert (Hdata_np_len : Zlength data_np = dn0_bare - 1) by (symmetry; exact H0).
  assert (Hdata_dp_len : Zlength data_dp = dn0_bare - 1) by (symmetry; exact H2).
  assert (Hdata_dp_eq : data_dp = l_dp_add).
  {
    apply (list_to_Z_reverse_same_length_injection UINT_MOD
      ltac:(unfold UINT_MOD; lia) data_dp l_dp_add).
    - rewrite Hdata_dp_val, PreH54. reflexivity.
    - exact Hdata_dp_bound.
    - exact PreH48.
    - rewrite Hdata_dp_len, PreH35. reflexivity.
  }
  assert (Hretval_nonneg : 0 <= retval).
  {
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) l_np_add PreH46)
      as [Hnpadd_nonneg Hnpadd_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_np Hdata_np_bound)
      as [Hr_nonneg Hr_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_dp Hdata_dp_bound)
      as [Hdp_nonneg Hdp_lt].
    rewrite PreH33 in Hnpadd_lt.
    rewrite Hdata_np_len in Hr_lt.
    rewrite Hdata_dp_len in Hdp_lt.
    rewrite PreH53 in Hnpadd_nonneg, Hnpadd_lt.
    rewrite Hdata_np_val in Hr_nonneg, Hr_lt.
    rewrite Hdata_dp_val in Hdp_nonneg, Hdp_lt.
    set (P := UINT_MOD ^ (dn0_bare - 1)) in *.
    assert (HposP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    destruct (Z_lt_ge_dec retval 0) as [Hretneg | Hretge]; [| lia].
    assert (Hretle : retval <= -1) by lia.
    assert (Hmul : retval * P <= -1 * P).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    replace (-1 * P) with (- P) in Hmul by ring.
    assert (Hleft_neg : val_r_out + retval * P < 0) by (clear -Hr_lt Hmul; lia).
    assert (Hright_nonneg : 0 <= val_np_add + val_dp_add).
    { apply Z.add_nonneg_nonneg; [exact Hnpadd_nonneg | rewrite <- PreH54; exact Hdp_nonneg]. }
    rewrite PreH53, PreH54 in PreH1.
    clear -PreH1 Hleft_neg Hright_nonneg; lia.
  }
  assert (Hretval_le1 : retval <= 1).
  {
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) l_np_add PreH46)
      as [Hnpadd_nonneg Hnpadd_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_np Hdata_np_bound)
      as [Hr_nonneg Hr_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_dp Hdata_dp_bound)
      as [Hdp_nonneg Hdp_lt].
    rewrite PreH33 in Hnpadd_lt.
    rewrite Hdata_np_len in Hr_lt.
    rewrite Hdata_dp_len in Hdp_lt.
    rewrite PreH53 in Hnpadd_nonneg, Hnpadd_lt.
    rewrite Hdata_np_val in Hr_nonneg, Hr_lt.
    rewrite Hdata_dp_val in Hdp_nonneg, Hdp_lt.
    set (P := UINT_MOD ^ (dn0_bare - 1)) in *.
    assert (HposP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    destruct (Z_le_gt_dec retval 1) as [Hretle | Hretgt]; [lia |].
    assert (Hretge : 2 <= retval) by lia.
    assert (Hmul : 2 * P <= retval * P).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hleft_big : 2 * P <= val_r_out + retval * P) by (clear -Hr_nonneg Hmul; lia).
    assert (Hdp_lt_val : val_dp_add < P) by (rewrite <- PreH54; exact Hdp_lt).
    assert (Hright_lt : val_np_add + val_dp_add < 2 * P) by (clear -Hnpadd_lt Hdp_lt_val; lia).
    rewrite PreH53, PreH54 in PreH1.
    clear -PreH1 Hleft_big Hright_lt; lia.
  }
  assert (Hadd_val :
    val_r_out + retval * UINT_MOD ^ (dn0_bare - 1) =
    val_np_add + val_dp_add).
  { rewrite <- PreH53, <- PreH54. exact PreH1. }
  pose proof (mpn_div_qr_pi1_addback_transition
    l_cur_2 l_low l_mid l_high l_mid_low l_mid_high l_out data_np
    l_np_add l_np_tail l_dp_bare l_dp_low l_dp_high l_dp_add l_dp_tail
    dn0_bare nn0_bare i q n1 n0 n1_in n1_before n0_before d1 d0 dval_bare
    val_out retval_2 val_np_add val_dp_add val_r_out retval remv_2
    PreH4 PreH9 PreH10 PreH11 PreH25 PreH26 PreH27 PreH28 PreH29 PreH32
    Hdata_np_len PreH34 PreH12 PreH30 PreH31 PreH35 PreH36
    PreH14 PreH15 PreH16 PreH17 PreH18 PreH21 PreH22 PreH19 PreH20 PreH23 PreH24
    PreH40 Hmid_bound PreH41 Hmidlow_bound PreH42 PreH45 Hdata_np_bound PreH47 PreH38
    PreH43 PreH44 PreH48 PreH49 PreH52 Hdata_np_val PreH53 PreH54 Hadd_val PreH55
    PreH50 PreH2 PreH3 Hretval_nonneg Hretval_le1 PreH59 PreH60 PreH61 PreH62
    PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH71 PreH72 PreH73 PreH74
    PreH80 PreH81 PreH82)
    as [Hq_dec [Hrem_eq [Hrem_nonneg Hrem_lt]]].
  Exists (unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
          UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD
            (sublist 0 (dn0_bare + (i - 1)) (l_low ++ data_np ++ l_np_tail ++ l_high))).
  Exists (unsigned_last_nbits (q - 1) 32 + qv_done_2 * UINT_MOD).
  Exists (unsigned_last_nbits (q - 1) 32 :: l_done_2).
  Exists (l_low ++ data_np ++ l_np_tail ++ l_high).
  split_pure_spatial.
  - replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic (UIntArray.seg_single qp0_bare i (unsigned_last_nbits (q - 1) 32)).
    sep_apply_l_atomic
      (UIntArray.seg_merge_to_seg qp0_bare i (i + 1) (nn0_bare - dn0_bare + 1)
        (unsigned_last_nbits (q - 1) 32 :: nil) l_done_2).
    { dump_pre_spatial. clear -PreH9 PreH10. lia. }
    simpl.
    replace (UIntArray.full np_i (Zlength data_np) data_np) with
      (UIntArray.full np_i (dn0_bare - 1) data_np) by (f_equal; lia).
    sep_apply_l_atomic (UIntArray.seg_to_full np_i (dn0_bare - 1) dn0_bare l_np_tail).
    rewrite logic_equiv_sepcon_swap.
    sep_lift_L ((UIntArray.full np_i (dn0_bare - 1) data_np) ::
      (UIntArray.full (np_i + (dn0_bare - 1) * sizeof(UINT))
        (dn0_bare - (dn0_bare - 1)) l_np_tail) :: nil).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np_i (dn0_bare - 1) dn0_bare data_np l_np_tail).
    { dump_pre_spatial. clear -PreH4. lia. }
    rewrite PreH86.
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare (data_np ++ l_np_tail)) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) (data_np ++ l_np_tail))
      by (f_equal; ring).
    sep_apply_l_atomic
      (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low (data_np ++ l_np_tail)).
    { dump_pre_spatial. clear -PreH4 PreH9. lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    sep_apply_l_atomic
      (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ data_np ++ l_np_tail) l_high).
    { dump_pre_spatial. clear -PreH4 PreH9 PreH10. lia. }
    rewrite app_assoc.
    subst data_dp.
    replace (UIntArray.full dp0_bare (Zlength l_dp_add) l_dp_add) with
      (UIntArray.full dp0_bare (dn0_bare - 1) l_dp_add) by (f_equal; lia).
    sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare (dn0_bare - 1) dn0_bare l_dp_tail).
    rewrite logic_equiv_sepcon_swap.
    sep_lift_L ((UIntArray.full dp0_bare (dn0_bare - 1) l_dp_add) ::
      (UIntArray.full (dp0_bare + (dn0_bare - 1) * sizeof(UINT))
        (dn0_bare - (dn0_bare - 1)) l_dp_tail) :: nil).
    sep_apply_l_atomic (UIntArray.full_merge_to_full dp0_bare (dn0_bare - 1) dn0_bare l_dp_add l_dp_tail).
    { dump_pre_spatial. clear -PreH4. lia. }
    assert (Hdp_high_join : sublist 0 1 l_dp_high ++ sublist 1 2 l_dp_high = l_dp_high).
    {
      pose proof (sublist_split 0 2 1 l_dp_high
        ltac:(lia)
        ltac:(rewrite PreH31; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH31; lia).
      reflexivity.
    }
    assert (Hdp_join : l_dp_add ++ l_dp_tail = l_dp_bare).
    {
      rewrite PreH23, PreH24.
      rewrite <- app_assoc.
      rewrite Hdp_high_join.
      rewrite PreH19, PreH20.
      pose proof (sublist_split 0 dn0_bare (dn0_bare - 2) l_dp_bare
        ltac:(clear -PreH4; lia)
        ltac:(rewrite PreH12; clear -PreH4; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH12; clear -PreH4; lia).
      reflexivity.
    }
    rewrite Hdp_join.
    repeat rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) (unsigned_last_nbits (q - 1) 32)).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy")) cy).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy1")) cy1).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH2.
    + dump_pre_spatial; exact PreH3.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH7.
    + dump_pre_spatial; exact PreH8.
    + dump_pre_spatial. clear -PreH9. lia.
    + dump_pre_spatial. clear -PreH10. lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH25, Hdata_np_len, PreH34, PreH27. clear. lia.
    + dump_pre_spatial; exact PreH12.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH13. clear. lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH40.
      * apply list_within_bound_concat.
        -- exact Hdata_np_bound.
        -- apply list_within_bound_concat; [exact PreH47 | exact PreH41].
    + dump_pre_spatial; exact PreH38.
    + dump_pre_spatial.
      simpl; split.
      * pose proof (unsigned_Lastnbits_range (q - 1) 32 ltac:(lia)) as Hrange.
        change (2 ^ 32) with UINT_MOD in Hrange.
        unfold UINT_MOD in *; lia.
      * exact PreH39.
    + dump_pre_spatial; exact PreH50.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH51.
      ring.
    + dump_pre_spatial; exact PreH56.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n1 + d1) 32 + retval) 32 ltac:(lia)) as Hrange.
      change (2 ^ 32) with UINT_MOD in Hrange.
      unfold UINT_MOD in *; lia.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n1 + d1) 32 + retval) 32 ltac:(lia)) as Hrange.
      change (2 ^ 32) with UINT_MOD in Hrange.
      unfold UINT_MOD in *; lia.
    + dump_pre_spatial; exact PreH71.
    + dump_pre_spatial; exact PreH72.
    + dump_pre_spatial; exact PreH73.
    + dump_pre_spatial; exact PreH74.
    + dump_pre_spatial; exact PreH75.
    + dump_pre_spatial; exact PreH76.
    + dump_pre_spatial; exact PreH77.
    + dump_pre_spatial; exact PreH78.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial; exact Hrem_nonneg.
    + dump_pre_spatial.
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      rewrite PreH85.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
      rewrite Hpow.
      ring.
    + dump_pre_spatial; exact PreH87.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_3 : mpn_div_qr_pi1_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_repl := replace_Znth 0 (n0 - retval) l_mid_high).
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact PreH41. }
  assert (Hlrepl_bound : list_within_bound UINT_MOD l_repl).
  { subst l_repl.
    rewrite PreH34.
    rewrite replace_Znth_sublist_head.
    { simpl.
      split.
      - unfold UINT_MOD in *; lia.
      - eapply list_within_bound_sublist; [lia | rewrite PreH38; lia | exact PreH48]. }
    { rewrite PreH38. lia. } }
  pose proof (mpn_div_qr_pi1_submul_no_borrow_transition
    l_cur_2 l_low l_mid l_high l_mid_low l_mid_high l_out
    l_dp_bare l_dp_low l_dp_high dn0_bare nn0_bare i q n1 n0 n1_in d1 d0 dval_bare val_out retval remv_2
    PreH22 PreH25 PreH26 PreH27 PreH37 PreH38 PreH39 PreH40 PreH41 PreH16 PreH28 PreH42 PreH43
    PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
    PreH47 PreH48 PreH49 PreH50 PreH51 PreH17 PreH45 PreH52 PreH53
    PreH18 PreH19 PreH54 PreH20 PreH21 PreH61 PreH3 PreH2 PreH74 PreH75 PreH76) as [Hrem_eq [Hrem_nonneg Hrem_lt]].
  fold l_repl in Hrem_eq, Hrem_nonneg, Hrem_lt.
  Exists (n1 * UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_repl ++ l_high))).
  Exists (q + qv_done_2 * UINT_MOD).
  Exists (q :: l_done_2).
  Exists (l_low ++ l_out ++ l_repl ++ l_high).
  split_pure_spatial.
  - replace (dn0_bare - 2 - (dn0_bare - 2)) with 0 by ring.
    fold l_repl.
    replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic (UIntArray.seg_single qp0_bare i q).
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare i (i + 1) (nn0_bare - dn0_bare + 1) (q :: nil) l_done_2).
    { dump_pre_spatial. clear -PreH26. lia. }
    simpl.
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite PreH80.
    sep_apply_l_atomic (UIntArray.full_to_seg (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) l_out).
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) 0 (dn0_bare - 2) l_out).
    replace (np0_bare + i * sizeof(UINT) + 0 * sizeof(UINT)) with (np0_bare + i * sizeof(UINT)) by lia.
    replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_repl).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) 2 l_repl) with
      (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_repl) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_out l_repl).
    { dump_pre_spatial. clear -PreH22. lia. }
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare (l_out ++ l_repl)) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) (l_out ++ l_repl)) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low (l_out ++ l_repl)).
    { dump_pre_spatial. clear -PreH22 PreH25. lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ l_out ++ l_repl) l_high).
    { dump_pre_spatial. clear -PreH22 PreH25 PreH26. lia. }
    rewrite app_assoc.
    sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_high).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) 2 l_dp_high) with
      (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_dp_high) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_low l_dp_high).
    { dump_pre_spatial. clear -PreH22. lia. }
    assert (Hdp_join : l_dp_low ++ l_dp_high = l_dp_bare).
    { rewrite PreH35, PreH36.
      pose proof (sublist_split 0 dn0_bare (dn0_bare - 2) l_dp_bare
        ltac:(clear -PreH22; lia)
        ltac:(rewrite PreH28; clear -PreH22; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH28; clear -PreH22; lia).
      reflexivity. }
    rewrite Hdp_join.
    repeat rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) q).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy")) 0).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy1")) 0).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH20.
    + dump_pre_spatial; exact PreH21.
    + dump_pre_spatial; exact PreH22.
    + dump_pre_spatial; exact PreH23.
    + dump_pre_spatial; exact PreH24.
    + dump_pre_spatial. clear -PreH25. lia.
    + dump_pre_spatial. clear -PreH26. lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH37, PreH16, Hlrepl_len, PreH39. clear. lia.
    + dump_pre_spatial; exact PreH28.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH29. clear. lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH47.
      * apply list_within_bound_concat.
        -- exact PreH17.
        -- apply list_within_bound_concat; [exact Hlrepl_bound | exact PreH49].
    + dump_pre_spatial; exact PreH45.
    + dump_pre_spatial.
      simpl; split; [unfold UINT_MOD in *; lia | exact PreH46].
    + dump_pre_spatial; exact PreH54.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH55.
      unfold UINT_MOD; ring.
    + dump_pre_spatial; exact PreH56.
    + dump_pre_spatial. clear -PreH61. lia.
    + dump_pre_spatial. clear -PreH62. lia.
    + dump_pre_spatial; exact PreH65.
    + dump_pre_spatial; exact PreH66.
    + dump_pre_spatial; exact PreH67.
    + dump_pre_spatial; exact PreH68.
    + dump_pre_spatial; exact PreH69.
    + dump_pre_spatial; exact PreH70.
    + dump_pre_spatial; exact PreH71.
    + dump_pre_spatial; exact PreH72.
    + dump_pre_spatial.
      ring_simplify (n1 - 0); reflexivity.
    + dump_pre_spatial; exact Hrem_nonneg.
    + dump_pre_spatial.
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      rewrite PreH79.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
      rewrite Hpow.
      ring.
    + dump_pre_spatial; exact PreH81.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_4 : mpn_div_qr_pi1_entail_wit_9_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hborrow_eq : unsigned_last_nbits (n0 - retval) 32 = n0 + UINT_MOD - retval).
  { rewrite (u32_sub_borrow_eq n0 retval); try (unfold UINT_MOD in *; lia). }
  set (l_repl := replace_Znth 0 (unsigned_last_nbits (n0 - retval) 32) l_mid_high).
  assert (Hrepl_eq : l_repl = replace_Znth 0 (n0 + UINT_MOD - retval) l_mid_high).
  { subst l_repl. rewrite Hborrow_eq. reflexivity. }
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact PreH41. }
  assert (Hlrepl_bound : list_within_bound UINT_MOD l_repl).
  { subst l_repl.
    rewrite Hborrow_eq.
    rewrite PreH34.
    rewrite replace_Znth_sublist_head.
    { simpl.
      split.
      - unfold UINT_MOD in *; lia.
      - eapply list_within_bound_sublist; [lia | rewrite PreH38; lia | exact PreH48]. }
    { rewrite PreH38. lia. } }
  assert (Hwindow :
    n1_in * UINT_MOD ^ 2 + Znth (dn0_bare - 1) l_mid 0 * UINT_MOD +
      Znth (dn0_bare - 2) l_mid 0 =
    q * (d1 * UINT_MOD + d0) + (n1 - 1) * UINT_MOD + (n0 + UINT_MOD)).
  { rewrite PreH74. ring. }
  assert (Hpair_lt :
    (n1 - 1) * UINT_MOD + (n0 + UINT_MOD) < d1 * UINT_MOD + d0).
  { replace ((n1 - 1) * UINT_MOD + (n0 + UINT_MOD))
      with (n1 * UINT_MOD + n0) by ring.
    exact PreH75. }
  pose proof (mpn_div_qr_pi1_submul_no_borrow_transition
    l_cur_2 l_low l_mid l_high l_mid_low l_mid_high l_out
    l_dp_bare l_dp_low l_dp_high dn0_bare nn0_bare i q (n1 - 1) (n0 + UINT_MOD) n1_in d1 d0 dval_bare val_out retval remv_2
    PreH22 PreH25 PreH26 PreH27 PreH37 PreH38 PreH39 PreH40 PreH41 PreH16 PreH28 PreH42 PreH43
    PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
    PreH47 PreH48 PreH49 PreH50 PreH51 PreH17 PreH45 PreH52 PreH53
    PreH18 PreH19 PreH54 PreH20 PreH21
    ltac:(clear -PreH1; lia) PreH3 ltac:(unfold UINT_MOD in *; lia)
    Hwindow Hpair_lt PreH76) as [Hrem_eq [Hrem_nonneg Hrem_lt]].
  rewrite <- Hrepl_eq in Hrem_eq, Hrem_nonneg, Hrem_lt.
  Exists ((n1 - 1) * UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_repl ++ l_high))).
  Exists (q + qv_done_2 * UINT_MOD).
  Exists (q :: l_done_2).
  Exists (l_low ++ l_out ++ l_repl ++ l_high).
  split_pure_spatial.
  - replace (dn0_bare - 2 - (dn0_bare - 2)) with 0 by ring.
    fold l_repl.
    replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic (UIntArray.seg_single qp0_bare i q).
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg qp0_bare i (i + 1) (nn0_bare - dn0_bare + 1) (q :: nil) l_done_2).
    { dump_pre_spatial. clear -PreH26. lia. }
    simpl.
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite PreH80.
    sep_apply_l_atomic (UIntArray.full_to_seg (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) l_out).
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) 0 (dn0_bare - 2) l_out).
    replace (np0_bare + i * sizeof(UINT) + 0 * sizeof(UINT)) with (np0_bare + i * sizeof(UINT)) by lia.
    replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_repl).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) 2 l_repl) with
      (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_repl) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_out l_repl).
    { dump_pre_spatial. clear -PreH22. lia. }
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare (l_out ++ l_repl)) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) (l_out ++ l_repl)) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low (l_out ++ l_repl)).
    { dump_pre_spatial. clear -PreH22 PreH25. lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ l_out ++ l_repl) l_high).
    { dump_pre_spatial. clear -PreH22 PreH25 PreH26. lia. }
    rewrite app_assoc.
    sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_high).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) 2 l_dp_high) with
      (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_dp_high) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_low l_dp_high).
    { dump_pre_spatial. clear -PreH22. lia. }
    assert (Hdp_join : l_dp_low ++ l_dp_high = l_dp_bare).
    { rewrite PreH35, PreH36.
      pose proof (sublist_split 0 dn0_bare (dn0_bare - 2) l_dp_bare
        ltac:(clear -PreH22; lia)
        ltac:(rewrite PreH28; clear -PreH22; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH28; clear -PreH22; lia).
      reflexivity. }
    rewrite Hdp_join.
    repeat rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) q).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy")) 0).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy1")) 1).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH20.
    + dump_pre_spatial; exact PreH21.
    + dump_pre_spatial; exact PreH22.
    + dump_pre_spatial; exact PreH23.
    + dump_pre_spatial; exact PreH24.
    + dump_pre_spatial. clear -PreH25. lia.
    + dump_pre_spatial. clear -PreH26. lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH37, PreH16, Hlrepl_len, PreH39. clear. lia.
    + dump_pre_spatial; exact PreH28.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH29. clear. lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH47.
      * apply list_within_bound_concat.
        -- exact PreH17.
        -- apply list_within_bound_concat; [exact Hlrepl_bound | exact PreH49].
    + dump_pre_spatial; exact PreH45.
    + dump_pre_spatial.
      simpl; split; [unfold UINT_MOD in *; lia | exact PreH46].
    + dump_pre_spatial; exact PreH54.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH55.
      unfold UINT_MOD; ring.
    + dump_pre_spatial; exact PreH56.
    + dump_pre_spatial. clear -PreH1. lia.
    + dump_pre_spatial. clear -PreH1 PreH62. lia.
    + dump_pre_spatial; exact PreH65.
    + dump_pre_spatial; exact PreH66.
    + dump_pre_spatial; exact PreH67.
    + dump_pre_spatial; exact PreH68.
    + dump_pre_spatial; exact PreH69.
    + dump_pre_spatial; exact PreH70.
    + dump_pre_spatial; exact PreH71.
    + dump_pre_spatial; exact PreH72.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial; exact Hrem_nonneg.
    + dump_pre_spatial.
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      rewrite PreH79.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
      rewrite Hpow.
      ring.
    + dump_pre_spatial; exact PreH81.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_5 : mpn_div_qr_pi1_entail_wit_9_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists (Znth (dn0_bare - 1) l_out 0 * UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_high))).
  Exists (4294967295 + qv_done_2 * UINT_MOD).
  Exists (4294967295 :: l_done_2).
  Exists (l_low ++ l_out ++ l_high).
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite PreH59.
    sep_apply_l_atomic (UIntArray.full_to_seg (np0_bare + i * sizeof(UINT)) dn0_bare l_out).
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) 0 dn0_bare l_out).
    replace (np0_bare + i * sizeof(UINT) + 0 * sizeof(UINT)) with (np0_bare + i * sizeof(UINT)) by lia.
    replace (dn0_bare - 0) with dn0_bare by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare l_out) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) l_out) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low l_out).
    { dump_pre_spatial; lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    rewrite logic_equiv_sepcon_swap.
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ l_out) l_high).
    { dump_pre_spatial; lia. }
    rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) 4294967295).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH20.
    + dump_pre_spatial; exact PreH21.
    + dump_pre_spatial; exact PreH22.
    + dump_pre_spatial; exact PreH23.
    + dump_pre_spatial; exact PreH24.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH33, PreH1, PreH35; lia.
    + dump_pre_spatial; exact PreH28.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH29; lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH39.
      * apply list_within_bound_concat; [exact PreH2 | exact PreH41].
    + dump_pre_spatial; exact PreH37.
    + dump_pre_spatial.
      simpl.
      split.
      * unfold UINT_MOD; lia.
      * exact PreH38.
    + dump_pre_spatial; exact PreH42.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH43.
      unfold UINT_MOD; ring.
    + dump_pre_spatial; exact PreH44.
    + dump_pre_spatial.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_out (dn0_bare - 1)) as Hbound.
      specialize (Hbound ltac:(rewrite PreH1; clear -PreH22; lia) PreH2).
      destruct Hbound as [Hlow _].
      exact Hlow.
    + dump_pre_spatial.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_out (dn0_bare - 1)) as Hbound.
      specialize (Hbound ltac:(rewrite PreH1; clear -PreH22; lia) PreH2).
      destruct Hbound as [_ Hhigh].
      change UINT_MAX with 4294967295.
      unfold UINT_MOD in Hhigh; lia.
    + dump_pre_spatial; exact PreH47.
    + dump_pre_spatial; exact PreH48.
    + dump_pre_spatial; exact PreH49.
    + dump_pre_spatial; exact PreH50.
    + dump_pre_spatial; exact PreH51.
    + dump_pre_spatial; exact PreH52.
    + dump_pre_spatial; exact PreH53.
    + dump_pre_spatial; exact PreH54.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial.
      apply Z.add_nonneg_nonneg.
      * apply Z.mul_nonneg_nonneg.
        -- pose proof (list_within_bound_Znth_bound UINT_MOD l_out (dn0_bare - 1)) as Hbound.
           specialize (Hbound ltac:(rewrite PreH1; clear -PreH22; lia) PreH2).
           destruct Hbound as [Hlow _].
           exact Hlow.
        -- apply Z.pow_nonneg; unfold UINT_MOD; lia.
      * pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos
                      (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_high))) as Hbound.
        assert (Hsub_bound:
          list_within_bound UINT_MOD
            (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_high))).
        {
          apply list_within_bound_sublist.
          - clear -PreH22 PreH25; lia.
          - rewrite !Zlength_app, PreH33, PreH1, PreH35.
            clear -PreH22 PreH23 PreH25 PreH26; lia.
          - apply list_within_bound_concat.
            + exact PreH39.
            + apply list_within_bound_concat; [exact PreH2 | exact PreH41].
        }
        specialize (Hbound Hsub_bound).
        destruct Hbound as [Hnonneg _].
        exact Hnonneg.
    + dump_pre_spatial.
      pose proof (mpn_div_qr_pi1_qmax_transition
        l_cur_2 l_low l_mid l_high l_out l_dp_bare dn0_bare nn0_bare i n1 dval_bare
        val_out retval remv_2
        PreH22 PreH25 PreH26 PreH27 PreH33 PreH34 PreH35 PreH1 PreH28
        PreH30 PreH31 PreH32 PreH36 PreH39 PreH40 PreH41 PreH2 PreH37
        PreH3 PreH4 PreH42 PreH44 (eq_trans PreH19 PreH20)
        (eq_trans PreH18 PreH21)
        ltac:(rewrite PreH19; exact PreH47)
        ltac:(rewrite PreH19; exact PreH48)
        PreH55 PreH56 PreH57) as [_ [_ Hrem_lt]].
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      pose proof (mpn_div_qr_pi1_qmax_transition
        l_cur_2 l_low l_mid l_high l_out l_dp_bare dn0_bare nn0_bare i n1 dval_bare
        val_out retval remv_2
        PreH22 PreH25 PreH26 PreH27 PreH33 PreH34 PreH35 PreH1 PreH28
        PreH30 PreH31 PreH32 PreH36 PreH39 PreH40 PreH41 PreH2 PreH37
        PreH3 PreH4 PreH42 PreH44 (eq_trans PreH19 PreH20)
        (eq_trans PreH18 PreH21)
        ltac:(rewrite PreH19; exact PreH47)
        ltac:(rewrite PreH19; exact PreH48)
        PreH55 PreH56 PreH57) as [Hrem_eq _].
      rewrite PreH58.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      {
        replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring.
      }
      rewrite Hpow.
      unfold UINT_MOD.
      ring.
    + dump_pre_spatial; exact PreH60.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_6 : mpn_div_qr_pi1_entail_wit_9_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold mpd_store_Z, mpd_store_list.
  Intros data_np data_dp.
  destruct H as [Hdata_np_val Hdata_np_bound].
  destruct H1 as [Hdata_dp_val Hdata_dp_bound].
  assert (Hmid_bound : list_within_bound UINT_MOD l_mid).
  { rewrite PreH16. eapply list_within_bound_sublist; [lia | rewrite PreH12; lia | exact PreH38]. }
  assert (Hmidlow_bound : list_within_bound UINT_MOD l_mid_low).
  { rewrite PreH18. eapply list_within_bound_sublist; [lia | rewrite PreH27; lia | exact Hmid_bound]. }
  assert (Hdata_np_len : Zlength data_np = dn0_bare - 1) by (symmetry; exact H0).
  assert (Hdata_dp_len : Zlength data_dp = dn0_bare - 1) by (symmetry; exact H2).
  assert (Hdata_dp_eq : data_dp = l_dp_add).
  {
    apply (list_to_Z_reverse_same_length_injection UINT_MOD
      ltac:(unfold UINT_MOD; lia) data_dp l_dp_add).
    - rewrite Hdata_dp_val, PreH55. reflexivity.
    - exact Hdata_dp_bound.
    - exact PreH49.
    - rewrite Hdata_dp_len, PreH36. reflexivity.
  }
  assert (Hretval_nonneg : 0 <= retval).
  {
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) l_np_add PreH47)
      as [Hnpadd_nonneg Hnpadd_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_np Hdata_np_bound)
      as [Hr_nonneg Hr_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_dp Hdata_dp_bound)
      as [Hdp_nonneg Hdp_lt].
    rewrite PreH34 in Hnpadd_lt.
    rewrite Hdata_np_len in Hr_lt.
    rewrite Hdata_dp_len in Hdp_lt.
    rewrite PreH54 in Hnpadd_nonneg, Hnpadd_lt.
    rewrite Hdata_np_val in Hr_nonneg, Hr_lt.
    rewrite Hdata_dp_val in Hdp_nonneg, Hdp_lt.
    set (P := UINT_MOD ^ (dn0_bare - 1)) in *.
    assert (HposP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    destruct (Z_lt_ge_dec retval 0) as [Hretneg | Hretge]; [| lia].
    assert (Hretle : retval <= -1) by lia.
    assert (Hmul : retval * P <= -1 * P).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    replace (-1 * P) with (- P) in Hmul by ring.
    assert (Hleft_neg : val_r_out + retval * P < 0) by (clear -Hr_lt Hmul; lia).
    assert (Hright_nonneg : 0 <= val_np_add + val_dp_add).
    { apply Z.add_nonneg_nonneg; [exact Hnpadd_nonneg | rewrite <- PreH55; exact Hdp_nonneg]. }
    rewrite PreH54, PreH55 in PreH1.
    clear -PreH1 Hleft_neg Hright_nonneg; lia.
  }
  assert (Hretval_le1 : retval <= 1).
  {
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) l_np_add PreH47)
      as [Hnpadd_nonneg Hnpadd_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_np Hdata_np_bound)
      as [Hr_nonneg Hr_lt].
    pose proof (list_to_Z_bound UINT_MOD ltac:(unfold UINT_MOD; lia) data_dp Hdata_dp_bound)
      as [Hdp_nonneg Hdp_lt].
    rewrite PreH34 in Hnpadd_lt.
    rewrite Hdata_np_len in Hr_lt.
    rewrite Hdata_dp_len in Hdp_lt.
    rewrite PreH54 in Hnpadd_nonneg, Hnpadd_lt.
    rewrite Hdata_np_val in Hr_nonneg, Hr_lt.
    rewrite Hdata_dp_val in Hdp_nonneg, Hdp_lt.
    set (P := UINT_MOD ^ (dn0_bare - 1)) in *.
    assert (HposP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    destruct (Z_le_gt_dec retval 1) as [Hretle | Hretgt]; [lia |].
    assert (Hretge : 2 <= retval) by lia.
    assert (Hmul : 2 * P <= retval * P).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hleft_big : 2 * P <= val_r_out + retval * P) by (clear -Hr_nonneg Hmul; lia).
    assert (Hdp_lt_val : val_dp_add < P) by (rewrite <- PreH55; exact Hdp_lt).
    assert (Hright_lt : val_np_add + val_dp_add < 2 * P) by (clear -Hnpadd_lt Hdp_lt_val; lia).
    rewrite PreH54, PreH55 in PreH1.
    clear -PreH1 Hleft_big Hright_lt; lia.
  }
  assert (Hadd_val :
    val_r_out + retval * UINT_MOD ^ (dn0_bare - 1) =
    val_np_add + val_dp_add).
  { rewrite <- PreH54, <- PreH55. exact PreH1. }
  pose proof (mpn_div_qr_pi1_addback_transition
    l_cur_2 l_low l_mid l_high l_mid_low l_mid_high l_out data_np
    l_np_add l_np_tail l_dp_bare l_dp_low l_dp_high l_dp_add l_dp_tail
    dn0_bare nn0_bare i q n1 n0 n1_in n1_before n0_before d1 d0 dval_bare
    val_out retval_2 val_np_add val_dp_add val_r_out retval remv_2
    PreH5 PreH10 PreH11 PreH12 PreH26 PreH27 PreH28 PreH29 PreH30 PreH33
    Hdata_np_len PreH35 PreH13 PreH31 PreH32 PreH36 PreH37
    PreH15 PreH16 PreH17 PreH18 PreH19 PreH22 PreH23 PreH20 PreH21 PreH24 PreH25
    PreH41 Hmid_bound PreH42 Hmidlow_bound PreH43 PreH46 Hdata_np_bound PreH48 PreH39
    PreH44 PreH45 PreH49 PreH50 PreH53 Hdata_np_val PreH54 PreH55 Hadd_val PreH56
    PreH51 PreH3 PreH4 Hretval_nonneg Hretval_le1 PreH60 PreH61 PreH62 PreH63
    PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH72 PreH73 PreH74 PreH75
    PreH81 PreH82 PreH83)
    as [Hq_dec [Hrem_eq [Hrem_nonneg Hrem_lt]]].
  Exists (unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
          UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD
            (sublist 0 (dn0_bare + (i - 1)) (l_low ++ data_np ++ l_np_tail ++ l_high))).
  Exists (unsigned_last_nbits (q - 1) 32 + qv_done_2 * UINT_MOD).
  Exists (unsigned_last_nbits (q - 1) 32 :: l_done_2).
  Exists (l_low ++ data_np ++ l_np_tail ++ l_high).
  split_pure_spatial.
  - simpl.
    replace (UIntArray.full np_i (Zlength data_np) data_np) with
      (UIntArray.full np_i (dn0_bare - 1) data_np) by (f_equal; lia).
    sep_apply_l_atomic (UIntArray.seg_to_full np_i (dn0_bare - 1) dn0_bare l_np_tail).
    rewrite logic_equiv_sepcon_swap.
    sep_lift_L ((UIntArray.full np_i (dn0_bare - 1) data_np) ::
      (UIntArray.full (np_i + (dn0_bare - 1) * sizeof(UINT))
        (dn0_bare - (dn0_bare - 1)) l_np_tail) :: nil).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np_i (dn0_bare - 1) dn0_bare data_np l_np_tail).
    { dump_pre_spatial. clear -PreH5. lia. }
    rewrite PreH87.
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare (data_np ++ l_np_tail)) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) (data_np ++ l_np_tail))
      by (f_equal; ring).
    sep_apply_l_atomic
      (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low (data_np ++ l_np_tail)).
    { dump_pre_spatial. clear -PreH5 PreH10. lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    sep_apply_l_atomic
      (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ data_np ++ l_np_tail) l_high).
    { dump_pre_spatial. clear -PreH5 PreH10 PreH11. lia. }
    rewrite app_assoc.
    subst data_dp.
    replace (UIntArray.full dp0_bare (Zlength l_dp_add) l_dp_add) with
      (UIntArray.full dp0_bare (dn0_bare - 1) l_dp_add) by (f_equal; lia).
    sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare (dn0_bare - 1) dn0_bare l_dp_tail).
    rewrite logic_equiv_sepcon_swap.
    sep_lift_L ((UIntArray.full dp0_bare (dn0_bare - 1) l_dp_add) ::
      (UIntArray.full (dp0_bare + (dn0_bare - 1) * sizeof(UINT))
        (dn0_bare - (dn0_bare - 1)) l_dp_tail) :: nil).
    sep_apply_l_atomic (UIntArray.full_merge_to_full dp0_bare (dn0_bare - 1) dn0_bare l_dp_add l_dp_tail).
    { dump_pre_spatial. clear -PreH5. lia. }
    assert (Hdp_high_join : sublist 0 1 l_dp_high ++ sublist 1 2 l_dp_high = l_dp_high).
    {
      pose proof (sublist_split 0 2 1 l_dp_high
        ltac:(lia)
        ltac:(rewrite PreH32; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH32; lia).
      reflexivity.
    }
    assert (Hdp_join : l_dp_add ++ l_dp_tail = l_dp_bare).
    {
      rewrite PreH24, PreH25.
      rewrite <- app_assoc.
      rewrite Hdp_high_join.
      rewrite PreH20, PreH21.
      pose proof (sublist_split 0 dn0_bare (dn0_bare - 2) l_dp_bare
        ltac:(clear -PreH5; lia)
        ltac:(rewrite PreH13; clear -PreH5; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH13; clear -PreH5; lia).
      reflexivity.
    }
    rewrite Hdp_join.
    repeat rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) (unsigned_last_nbits (q - 1) 32)).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy")) cy).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy1")) cy1).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH3.
    + dump_pre_spatial; exact PreH4.
    + dump_pre_spatial; exact PreH5.
    + dump_pre_spatial; exact PreH8.
    + dump_pre_spatial; exact PreH9.
    + dump_pre_spatial. clear -PreH10. lia.
    + dump_pre_spatial. clear -PreH11. lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH26, Hdata_np_len, PreH35, PreH28. clear. lia.
    + dump_pre_spatial; exact PreH13.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH14. clear. lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH41.
      * apply list_within_bound_concat.
        -- exact Hdata_np_bound.
        -- apply list_within_bound_concat; [exact PreH48 | exact PreH42].
    + dump_pre_spatial; exact PreH39.
    + dump_pre_spatial.
      simpl; split.
      * pose proof (unsigned_Lastnbits_range (q - 1) 32 ltac:(lia)) as Hrange.
        change (2 ^ 32) with UINT_MOD in Hrange.
        unfold UINT_MOD in *; lia.
      * exact PreH40.
    + dump_pre_spatial; exact PreH51.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH52.
      ring.
    + dump_pre_spatial; exact PreH57.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n1 + d1) 32 + retval) 32 ltac:(lia)) as Hrange.
      change (2 ^ 32) with UINT_MOD in Hrange.
      unfold UINT_MOD in *; lia.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (n1 + d1) 32 + retval) 32 ltac:(lia)) as Hrange.
      change (2 ^ 32) with UINT_MOD in Hrange.
      unfold UINT_MOD in *; lia.
    + dump_pre_spatial; exact PreH72.
    + dump_pre_spatial; exact PreH73.
    + dump_pre_spatial; exact PreH74.
    + dump_pre_spatial; exact PreH75.
    + dump_pre_spatial; exact PreH76.
    + dump_pre_spatial; exact PreH77.
    + dump_pre_spatial; exact PreH78.
    + dump_pre_spatial; exact PreH79.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial; exact Hrem_nonneg.
    + dump_pre_spatial.
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      rewrite PreH86.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
      rewrite Hpow.
      ring.
    + dump_pre_spatial; exact PreH88.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_7 : mpn_div_qr_pi1_entail_wit_9_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_repl := replace_Znth 0 (n0 - retval) l_mid_high).
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact PreH41. }
  assert (Hlrepl_bound : list_within_bound UINT_MOD l_repl).
  { subst l_repl.
    rewrite PreH34.
    rewrite replace_Znth_sublist_head.
    { simpl.
      split.
      - unfold UINT_MOD in *; lia.
      - eapply list_within_bound_sublist; [lia | rewrite PreH38; lia | exact PreH48]. }
    { rewrite PreH38. lia. } }
  pose proof (mpn_div_qr_pi1_submul_no_borrow_transition
    l_cur_2 l_low l_mid l_high l_mid_low l_mid_high l_out
    l_dp_bare l_dp_low l_dp_high dn0_bare nn0_bare i q n1 n0 n1_in d1 d0 dval_bare val_out retval remv_2
    PreH22 PreH25 PreH26 PreH27 PreH37 PreH38 PreH39 PreH40 PreH41 PreH16 PreH28 PreH42 PreH43
    PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
    PreH47 PreH48 PreH49 PreH50 PreH51 PreH17 PreH45 PreH52 PreH53
    PreH18 PreH19 PreH54 PreH20 PreH21 PreH61 PreH3 PreH2 PreH74 PreH75 PreH76) as [Hrem_eq [Hrem_nonneg Hrem_lt]].
  fold l_repl in Hrem_eq, Hrem_nonneg, Hrem_lt.
  Exists (n1 * UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_repl ++ l_high))).
  Exists (q + qv_done_2 * UINT_MOD).
  Exists (q :: l_done_2).
  Exists (l_low ++ l_out ++ l_repl ++ l_high).
  split_pure_spatial.
  - replace (dn0_bare - 2 - (dn0_bare - 2)) with 0 by ring.
    fold l_repl.
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite PreH80.
    sep_apply_l_atomic (UIntArray.full_to_seg (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) l_out).
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) 0 (dn0_bare - 2) l_out).
    replace (np0_bare + i * sizeof(UINT) + 0 * sizeof(UINT)) with (np0_bare + i * sizeof(UINT)) by lia.
    replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_repl).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) 2 l_repl) with
      (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_repl) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_out l_repl).
    { dump_pre_spatial. clear -PreH22. lia. }
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare (l_out ++ l_repl)) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) (l_out ++ l_repl)) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low (l_out ++ l_repl)).
    { dump_pre_spatial. clear -PreH22 PreH25. lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ l_out ++ l_repl) l_high).
    { dump_pre_spatial. clear -PreH22 PreH25 PreH26. lia. }
    rewrite app_assoc.
    sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_high).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) 2 l_dp_high) with
      (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_dp_high) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_low l_dp_high).
    { dump_pre_spatial. clear -PreH22. lia. }
    assert (Hdp_join : l_dp_low ++ l_dp_high = l_dp_bare).
    { rewrite PreH35, PreH36.
      pose proof (sublist_split 0 dn0_bare (dn0_bare - 2) l_dp_bare
        ltac:(clear -PreH22; lia)
        ltac:(rewrite PreH28; clear -PreH22; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH28; clear -PreH22; lia).
      reflexivity. }
    rewrite Hdp_join.
    repeat rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) q).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy")) 0).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy1")) 0).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH20.
    + dump_pre_spatial; exact PreH21.
    + dump_pre_spatial; exact PreH22.
    + dump_pre_spatial; exact PreH23.
    + dump_pre_spatial; exact PreH24.
    + dump_pre_spatial. clear -PreH25. lia.
    + dump_pre_spatial. clear -PreH26. lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH37, PreH16, Hlrepl_len, PreH39. clear. lia.
    + dump_pre_spatial; exact PreH28.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH29. clear. lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH47.
      * apply list_within_bound_concat.
        -- exact PreH17.
        -- apply list_within_bound_concat; [exact Hlrepl_bound | exact PreH49].
    + dump_pre_spatial; exact PreH45.
    + dump_pre_spatial.
      simpl; split; [unfold UINT_MOD in *; lia | exact PreH46].
    + dump_pre_spatial; exact PreH54.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH55.
      unfold UINT_MOD; ring.
    + dump_pre_spatial; exact PreH56.
    + dump_pre_spatial. clear -PreH61. lia.
    + dump_pre_spatial. clear -PreH62. lia.
    + dump_pre_spatial; exact PreH65.
    + dump_pre_spatial; exact PreH66.
    + dump_pre_spatial; exact PreH67.
    + dump_pre_spatial; exact PreH68.
    + dump_pre_spatial; exact PreH69.
    + dump_pre_spatial; exact PreH70.
    + dump_pre_spatial; exact PreH71.
    + dump_pre_spatial; exact PreH72.
    + dump_pre_spatial.
      ring_simplify (n1 - 0); reflexivity.
    + dump_pre_spatial; exact Hrem_nonneg.
    + dump_pre_spatial.
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      rewrite PreH79.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
      rewrite Hpow.
      ring.
    + dump_pre_spatial; exact PreH81.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_entail_wit_9_8 : mpn_div_qr_pi1_entail_wit_9_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hborrow_eq : unsigned_last_nbits (n0 - retval) 32 = n0 + UINT_MOD - retval).
  { rewrite (u32_sub_borrow_eq n0 retval); try (unfold UINT_MOD in *; lia). }
  set (l_repl := replace_Znth 0 (unsigned_last_nbits (n0 - retval) 32) l_mid_high).
  assert (Hrepl_eq : l_repl = replace_Znth 0 (n0 + UINT_MOD - retval) l_mid_high).
  { subst l_repl. rewrite Hborrow_eq. reflexivity. }
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact PreH41. }
  assert (Hlrepl_bound : list_within_bound UINT_MOD l_repl).
  { subst l_repl.
    rewrite Hborrow_eq.
    rewrite PreH34.
    rewrite replace_Znth_sublist_head.
    { simpl.
      split.
      - unfold UINT_MOD in *; lia.
      - eapply list_within_bound_sublist; [lia | rewrite PreH38; lia | exact PreH48]. }
    { rewrite PreH38. lia. } }
  assert (Hwindow :
    n1_in * UINT_MOD ^ 2 + Znth (dn0_bare - 1) l_mid 0 * UINT_MOD +
      Znth (dn0_bare - 2) l_mid 0 =
    q * (d1 * UINT_MOD + d0) + (n1 - 1) * UINT_MOD + (n0 + UINT_MOD)).
  { rewrite PreH74. ring. }
  assert (Hpair_lt :
    (n1 - 1) * UINT_MOD + (n0 + UINT_MOD) < d1 * UINT_MOD + d0).
  { replace ((n1 - 1) * UINT_MOD + (n0 + UINT_MOD))
      with (n1 * UINT_MOD + n0) by ring.
    exact PreH75. }
  pose proof (mpn_div_qr_pi1_submul_no_borrow_transition
    l_cur_2 l_low l_mid l_high l_mid_low l_mid_high l_out
    l_dp_bare l_dp_low l_dp_high dn0_bare nn0_bare i q (n1 - 1) (n0 + UINT_MOD) n1_in d1 d0 dval_bare val_out retval remv_2
    PreH22 PreH25 PreH26 PreH27 PreH37 PreH38 PreH39 PreH40 PreH41 PreH16 PreH28 PreH42 PreH43
    PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
    PreH47 PreH48 PreH49 PreH50 PreH51 PreH17 PreH45 PreH52 PreH53
    PreH18 PreH19 PreH54 PreH20 PreH21
    ltac:(clear -PreH1; lia) PreH3 ltac:(unfold UINT_MOD in *; lia)
    Hwindow Hpair_lt PreH76) as [Hrem_eq [Hrem_nonneg Hrem_lt]].
  rewrite <- Hrepl_eq in Hrem_eq, Hrem_nonneg, Hrem_lt.
  Exists ((n1 - 1) * UINT_MOD ^ (dn0_bare + (i - 1)) +
          list_to_Z UINT_MOD (sublist 0 (dn0_bare + (i - 1)) (l_low ++ l_out ++ l_repl ++ l_high))).
  Exists (q + qv_done_2 * UINT_MOD).
  Exists (q :: l_done_2).
  Exists (l_low ++ l_out ++ l_repl ++ l_high).
  split_pure_spatial.
  - replace (dn0_bare - 2 - (dn0_bare - 2)) with 0 by ring.
    fold l_repl.
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare 0 i l_low).
    replace (np0_bare + 0 * sizeof(UINT)) with np0_bare by lia.
    replace (i - 0) with i by ring.
    rewrite PreH80.
    sep_apply_l_atomic (UIntArray.full_to_seg (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) l_out).
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) 0 (dn0_bare - 2) l_out).
    replace (np0_bare + i * sizeof(UINT) + 0 * sizeof(UINT)) with (np0_bare + i * sizeof(UINT)) by lia.
    replace (dn0_bare - 2 - 0) with (dn0_bare - 2) by ring.
    sep_apply_l_atomic (UIntArray.seg_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_repl).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) 2 l_repl) with
      (UIntArray.full (np0_bare + i * sizeof(UINT) + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_repl) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full (np0_bare + i * sizeof(UINT)) (dn0_bare - 2) dn0_bare l_out l_repl).
    { dump_pre_spatial. clear -PreH22. lia. }
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (np0_bare + i * sizeof(UINT)) dn0_bare (l_out ++ l_repl)) with
      (UIntArray.full (np0_bare + i * sizeof(UINT)) (i + dn0_bare - i) (l_out ++ l_repl)) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare i (i + dn0_bare) l_low (l_out ++ l_repl)).
    { dump_pre_spatial. clear -PreH22 PreH25. lia. }
    sep_apply_l_atomic (UIntArray.seg_to_full np0_bare (i + dn0_bare) nn0_bare l_high).
    replace (nn0_bare - (i + dn0_bare)) with (nn0_bare - (i + dn0_bare)) by ring.
    sep_apply_l_atomic (UIntArray.full_merge_to_full np0_bare (i + dn0_bare) nn0_bare (l_low ++ l_out ++ l_repl) l_high).
    { dump_pre_spatial. clear -PreH22 PreH25 PreH26. lia. }
    rewrite app_assoc.
    sep_apply_l_atomic (UIntArray.seg_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_high).
    replace (dn0_bare - (dn0_bare - 2)) with 2 by ring.
    rewrite logic_equiv_sepcon_swap.
    replace (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) 2 l_dp_high) with
      (UIntArray.full (dp0_bare + (dn0_bare - 2) * sizeof(UINT)) (dn0_bare - (dn0_bare - 2)) l_dp_high) by (f_equal; ring).
    sep_apply_l_atomic (UIntArray.full_merge_to_full dp0_bare (dn0_bare - 2) dn0_bare l_dp_low l_dp_high).
    { dump_pre_spatial. clear -PreH22. lia. }
    assert (Hdp_join : l_dp_low ++ l_dp_high = l_dp_bare).
    { rewrite PreH35, PreH36.
      pose proof (sublist_split 0 dn0_bare (dn0_bare - 2) l_dp_bare
        ltac:(clear -PreH22; lia)
        ltac:(rewrite PreH28; clear -PreH22; lia)) as Hsplit.
      rewrite <- Hsplit.
      rewrite sublist_self by (rewrite PreH28; clear -PreH22; lia).
      reflexivity. }
    rewrite Hdp_join.
    repeat rewrite app_assoc.
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("q")) q).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy")) 0).
    cancel.
    sep_apply_l_atomic (store_uint_undef_store_uint (&("cy1")) 1).
    cancel.
  - split_pures.
    + dump_pre_spatial; exact PreH20.
    + dump_pre_spatial; exact PreH21.
    + dump_pre_spatial; exact PreH22.
    + dump_pre_spatial; exact PreH23.
    + dump_pre_spatial; exact PreH24.
    + dump_pre_spatial. clear -PreH25. lia.
    + dump_pre_spatial. clear -PreH26. lia.
    + dump_pre_spatial.
      rewrite !Zlength_app, PreH37, PreH16, Hlrepl_len, PreH39. clear. lia.
    + dump_pre_spatial; exact PreH28.
    + dump_pre_spatial.
      rewrite Zlength_cons, PreH29. clear. lia.
    + dump_pre_spatial.
      apply list_within_bound_concat.
      * exact PreH47.
      * apply list_within_bound_concat.
        -- exact PreH17.
        -- apply list_within_bound_concat; [exact Hlrepl_bound | exact PreH49].
    + dump_pre_spatial; exact PreH45.
    + dump_pre_spatial.
      simpl; split; [unfold UINT_MOD in *; lia | exact PreH46].
    + dump_pre_spatial; exact PreH54.
    + dump_pre_spatial.
      rewrite list_to_Z_cons, PreH55.
      unfold UINT_MOD; ring.
    + dump_pre_spatial; exact PreH56.
    + dump_pre_spatial. clear -PreH1. lia.
    + dump_pre_spatial. clear -PreH1 PreH62. lia.
    + dump_pre_spatial; exact PreH65.
    + dump_pre_spatial; exact PreH66.
    + dump_pre_spatial; exact PreH67.
    + dump_pre_spatial; exact PreH68.
    + dump_pre_spatial; exact PreH69.
    + dump_pre_spatial; exact PreH70.
    + dump_pre_spatial; exact PreH71.
    + dump_pre_spatial; exact PreH72.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial; exact Hrem_nonneg.
    + dump_pre_spatial.
      replace (i - 1 + 1) with i by lia.
      exact Hrem_lt.
    + dump_pre_spatial.
      rewrite PreH79.
      rewrite Hrem_eq.
      replace (i - 1 + 1) with i by lia.
      assert (Hpow : UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { replace (i + 1) with (1 + i) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
      rewrite Hpow.
      ring.
    + dump_pre_spatial; exact PreH81.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_return_wit_1 : mpn_div_qr_pi1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv qv_done
    (sublist dn0_bare nn0_bare (replace_Znth (dn0_bare - 1) n1 l_cur))
    (sublist 0 dn0_bare (replace_Znth (dn0_bare - 1) n1 l_cur))
    l_done.
  split_pure_spatial.
  -
    assert (Hi : i = -1) by lia.
    rewrite Hi in *.
    replace (-1 + 1) with 0 by lia.
    sep_apply_l_atomic (UIntArray.seg_to_full qp0_bare 0 (nn0_bare - dn0_bare + 1) l_done).
    replace (qp0_bare + 0 * sizeof(UINT)) with qp0_bare by lia.
    replace (nn0_bare - dn0_bare + 1 - 0) with (nn0_bare - dn0_bare + 1) by lia.
    sep_apply_l_atomic (UIntArray.full_to_seg np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np0_bare 0 dn0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 0) with dn0_bare by lia.
      replace (nn0_bare - 0) with nn0_bare by lia.
      cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial.
    assert (Hi : i = -1) by lia.
    rewrite PreH11.
    lia.
    dump_pre_spatial.
    rewrite Zlength_sublist0.
    reflexivity.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    dump_pre_spatial.
    rewrite Zlength_sublist.
    ring.
    split.
    lia.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    Intros Hrep_bound.
    dump_pre_spatial.
    apply list_within_bound_sublist.
    lia.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    exact H.
    sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    Intros Hrep_bound.
    dump_pre_spatial.
    apply list_within_bound_sublist.
    lia.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    exact H.
    sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    Intros Hrep_bound.
    dump_pre_spatial.
    assert (Hi : i = -1) by lia.
    rewrite PreH28, Hi.
    replace (dn0_bare + -1) with (dn0_bare - 1) by ring.
    replace dn0_bare with (dn0_bare - 1 + 1) by ring.
    replace (dn0_bare - 1 + 1 - 1) with (dn0_bare - 1) by ring.
    assert (Happend :
      list_to_Z UINT_MOD
        (sublist 0 (dn0_bare - 1 + 1)
          (replace_Znth (dn0_bare - 1) n1 l_cur)) =
      list_to_Z UINT_MOD
        (sublist 0 (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur)) +
      Znth (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur) 0 *
      UINT_MOD ^ (dn0_bare - 1)).
    {
      apply list_to_Z_list_append.
      - exact UINT_MOD_pos.
      - rewrite Zlength_replace_Znth.
        rewrite PreH9.
        clear -PreH4 PreH5.
        lia.
      - exact H.
    }
    rewrite Happend.
    assert (Hznth :
      Znth (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur) 0 = n1).
    {
      apply Znth_replace_Znth_Same.
      rewrite PreH9.
      clear -PreH4 PreH5.
      lia.
    }
    rewrite Hznth.
    assert (Hprefix :
      sublist 0 (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur) =
      sublist 0 (dn0_bare - 1) l_cur).
    {
      apply list_eq_ext with (d := 0).
      split.
      - rewrite (Zlength_sublist0 (dn0_bare - 1)
          (replace_Znth (dn0_bare - 1) n1 l_cur))
          by (rewrite Zlength_replace_Znth; rewrite PreH9; lia).
        rewrite (Zlength_sublist0 (dn0_bare - 1) l_cur)
          by (rewrite PreH9; lia).
        reflexivity.
      - intros j Hj.
        assert (Hj' : 0 <= j < dn0_bare - 1).
        {
          rewrite (Zlength_sublist0 (dn0_bare - 1)
            (replace_Znth (dn0_bare - 1) n1 l_cur)) in Hj.
          - exact Hj.
          - rewrite Zlength_replace_Znth.
            rewrite PreH9.
            lia.
        }
        assert (Hdiff :
          Znth j (replace_Znth (dn0_bare - 1) n1 l_cur) 0 =
          Znth j l_cur 0).
        {
          apply Znth_replace_Znth_Diff.
          - rewrite PreH9; clear -Hj' PreH4 PreH5; nia.
          - rewrite PreH9; clear -Hj' PreH4 PreH5; nia.
          - clear -Hj'; nia.
        }
        rewrite !Znth_sublist by (clear -Hj'; lia).
        replace (j + 0) with j by ring.
        exact Hdiff.
    }
    rewrite Hprefix.
    ring.
    dump_pre_spatial.
    assert (Hi0 : i = -1) by lia.
    rewrite Hi0 in PreH31.
    replace (-1 + 1) with 0 in PreH31 by ring.
    rewrite Z.pow_0_r in PreH31.
    replace (qv_done * 1 * dval_bare + remv)
      with (qv_done * dval_bare + remv) in PreH31 by ring.
    exact PreH31.
    dump_pre_spatial.
    assert (Hi1 : i = -1) by lia.
    rewrite Hi1 in PreH30.
    replace (-1 + 1) with 0 in PreH30 by ring.
    rewrite Z.pow_0_r in PreH30.
    replace (dval_bare * 1) with dval_bare in PreH30 by ring.
    exact PreH30.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_return_wit_2 : mpn_div_qr_pi1_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists remv qv_done
    (sublist dn0_bare nn0_bare (replace_Znth (dn0_bare - 1) n1 l_cur))
    (sublist 0 dn0_bare (replace_Znth (dn0_bare - 1) n1 l_cur))
    l_done.
  split_pure_spatial.
  -
    assert (Hi : i = -1) by lia.
    rewrite Hi in *.
    sep_apply_l_atomic (UIntArray.full_to_seg np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    sep_apply_l_atomic (UIntArray.seg_split_to_seg np0_bare 0 dn0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    + dump_pre_spatial; lia.
    + replace (dn0_bare - 0) with dn0_bare by lia.
      replace (nn0_bare - 0) with nn0_bare by lia.
      cancel.
  -
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; reflexivity).
    dump_pre_spatial.
    assert (Hi : i = -1) by lia.
    rewrite PreH11.
    lia.
    dump_pre_spatial.
    rewrite Zlength_sublist0.
    reflexivity.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    dump_pre_spatial.
    rewrite Zlength_sublist.
    ring.
    split.
    lia.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    Intros Hrep_bound.
    dump_pre_spatial.
    apply list_within_bound_sublist.
    lia.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    exact H.
    sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    Intros Hrep_bound.
    dump_pre_spatial.
    apply list_within_bound_sublist.
    lia.
    rewrite Zlength_replace_Znth.
    rewrite PreH9.
    lia.
    exact H.
    sep_apply_l_atomic (UIntArray_full_list_within_bound_preserve np0_bare nn0_bare
      (replace_Znth (dn0_bare - 1) n1 l_cur)).
    Intros Hrep_bound.
    dump_pre_spatial.
    assert (Hi : i = -1) by lia.
    rewrite PreH28, Hi.
    replace (dn0_bare + -1) with (dn0_bare - 1) by ring.
    replace dn0_bare with (dn0_bare - 1 + 1) by ring.
    replace (dn0_bare - 1 + 1 - 1) with (dn0_bare - 1) by ring.
    assert (Happend :
      list_to_Z UINT_MOD
        (sublist 0 (dn0_bare - 1 + 1)
          (replace_Znth (dn0_bare - 1) n1 l_cur)) =
      list_to_Z UINT_MOD
        (sublist 0 (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur)) +
      Znth (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur) 0 *
      UINT_MOD ^ (dn0_bare - 1)).
    {
      apply list_to_Z_list_append.
      - exact UINT_MOD_pos.
      - rewrite Zlength_replace_Znth.
        rewrite PreH9.
        clear -PreH4 PreH5.
        lia.
      - exact H.
    }
    rewrite Happend.
    assert (Hznth :
      Znth (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur) 0 = n1).
    {
      apply Znth_replace_Znth_Same.
      rewrite PreH9.
      clear -PreH4 PreH5.
      lia.
    }
    rewrite Hznth.
    assert (Hprefix :
      sublist 0 (dn0_bare - 1) (replace_Znth (dn0_bare - 1) n1 l_cur) =
      sublist 0 (dn0_bare - 1) l_cur).
    {
      apply list_eq_ext with (d := 0).
      split.
      - rewrite (Zlength_sublist0 (dn0_bare - 1)
          (replace_Znth (dn0_bare - 1) n1 l_cur))
          by (rewrite Zlength_replace_Znth; rewrite PreH9; lia).
        rewrite (Zlength_sublist0 (dn0_bare - 1) l_cur)
          by (rewrite PreH9; lia).
        reflexivity.
      - intros j Hj.
        assert (Hj' : 0 <= j < dn0_bare - 1).
        {
          rewrite (Zlength_sublist0 (dn0_bare - 1)
            (replace_Znth (dn0_bare - 1) n1 l_cur)) in Hj.
          - exact Hj.
          - rewrite Zlength_replace_Znth.
            rewrite PreH9.
            lia.
        }
        assert (Hdiff :
          Znth j (replace_Znth (dn0_bare - 1) n1 l_cur) 0 =
          Znth j l_cur 0).
        {
          apply Znth_replace_Znth_Diff.
          - rewrite PreH9; clear -Hj' PreH4 PreH5; nia.
          - rewrite PreH9; clear -Hj' PreH4 PreH5; nia.
          - clear -Hj'; nia.
        }
        rewrite !Znth_sublist by (clear -Hj'; lia).
        replace (j + 0) with j by ring.
        exact Hdiff.
    }
    rewrite Hprefix.
    ring.
    dump_pre_spatial.
    assert (Hi0 : i = -1) by lia.
    rewrite Hi0 in PreH31.
    replace (-1 + 1) with 0 in PreH31 by ring.
    rewrite Z.pow_0_r in PreH31.
    replace (qv_done * 1 * dval_bare + remv)
      with (qv_done * dval_bare + remv) in PreH31 by ring.
    exact PreH31.
    dump_pre_spatial.
    assert (Hi1 : i = -1) by lia.
    rewrite Hi1 in PreH30.
    replace (-1 + 1) with 0 in PreH30 by ring.
    rewrite Z.pow_0_r in PreH30.
    replace (dval_bare * 1) with dval_bare in PreH30 by ring.
    exact PreH30.
Qed. 

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_1 :
  mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH27; lia) PreH33).
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_2 :
  mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH27; lia) PreH33).
  unfold UINT_MOD in *.
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_3 :
  mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (mpn_div_qr_pi1_trial_le
                l_cur l_mid l_dp_bare dn0_bare nn0_bare i n1 remv dval_bare d1 d0
                PreH15 PreH18 PreH19 PreH20 PreH21 PreH24
                PreH29 PreH30 PreH35 PreH13 PreH14 PreH48
                PreH50 PreH38) as Htrial_le.
  apply (mpn_div_qr_pi1_trial_lt_neq
           n1 d1 (Znth (dn0_bare - 1) l_mid 0) d0).
  + lia.
  + unfold UINT_MOD in *; lia.
  + exact PreH42.
  + unfold UINT_MOD in *; lia.
  + exact PreH12.
  + exact Htrial_le.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure :
  mpn_div_qr_pi1_partial_solve_wit_15_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_1.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_2.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_15_pure_split_goal_3.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_1 :
  mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH27; lia) PreH33).
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_2 :
  mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH27; lia) PreH33).
  unfold UINT_MOD in *.
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_3 :
  mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (mpn_div_qr_pi1_trial_le
                l_cur l_mid l_dp_bare dn0_bare nn0_bare i n1 remv dval_bare d1 d0
                PreH15 PreH18 PreH19 PreH20 PreH21 PreH24
                PreH29 PreH30 PreH35 PreH13 PreH14 PreH48
                PreH50 PreH38) as Htrial_le.
  apply (mpn_div_qr_pi1_trial_lt_neq
           n1 d1 (Znth (dn0_bare - 1) l_mid 0) d0).
  + lia.
  + unfold UINT_MOD in *; lia.
  + exact PreH42.
  + unfold UINT_MOD in *; lia.
  + exact PreH12.
  + exact Htrial_le.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure :
  mpn_div_qr_pi1_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_1.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_2.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_16_pure_split_goal_3.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_1 :
  mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH28; lia) PreH34).
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_2 :
  mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH28; lia) PreH34).
  unfold UINT_MOD in *.
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_3 :
  mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (mpn_div_qr_pi1_trial_le
                l_cur l_mid l_dp_bare dn0_bare nn0_bare i n1 remv dval_bare d1 d0
                PreH16 PreH19 PreH20 PreH21 PreH22 PreH25
                PreH30 PreH31 PreH36 PreH14 PreH15 PreH49
                PreH51 PreH39) as Htrial_le.
  rewrite PreH13 in Htrial_le.
  unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_4 :
  mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (mpn_div_qr_pi1_trial_le
                l_cur l_mid l_dp_bare dn0_bare nn0_bare i n1 remv dval_bare d1 d0
                PreH16 PreH19 PreH20 PreH21 PreH22 PreH25
                PreH30 PreH31 PreH36 PreH14 PreH15 PreH49
                PreH51 PreH39) as Htrial_le.
  rewrite PreH13 in Htrial_le.
  unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure :
  mpn_div_qr_pi1_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_1.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_2.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_3.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_17_pure_split_goal_4.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_1 :
  mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH28; lia) PreH34).
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_2 :
  mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_mid (dn0_bare - 2)
                ltac:(rewrite PreH28; lia) PreH34).
  unfold UINT_MOD in *.
  lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_3 :
  mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (mpn_div_qr_pi1_trial_le
                l_cur l_mid l_dp_bare dn0_bare nn0_bare i n1 remv dval_bare d1 d0
                PreH16 PreH19 PreH20 PreH21 PreH22 PreH25
                PreH30 PreH31 PreH36 PreH14 PreH15 PreH49
                PreH51 PreH39) as Htrial_le.
  rewrite PreH13 in Htrial_le.
  unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_4 :
  mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (mpn_div_qr_pi1_trial_le
                l_cur l_mid l_dp_bare dn0_bare nn0_bare i n1 remv dval_bare d1 d0
                PreH16 PreH19 PreH20 PreH21 PreH22 PreH25
                PreH30 PreH31 PreH36 PreH14 PreH15 PreH49
                PreH51 PreH39) as Htrial_le.
  rewrite PreH13 in Htrial_le.
  unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure :
  mpn_div_qr_pi1_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_1.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_2.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_3.
  + Goal_apply proof_of_mpn_div_qr_pi1_partial_solve_wit_18_pure_split_goal_4.
Qed.

Lemma proof_of_mpn_div_qr_pi1_derive_optional_by_bare : mpn_div_qr_pi1_derive_optional_by_bare.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold optional_q_undef.
  Split.
  - Intros_p Hnull.
    Exists qp_pre np_pre dp_pre nn_pre dn_pre n1_pre
           l_np_optional l_dp_optional dval_optional.
    Right.
    split_pure_spatial.
    + cancel (UIntArray.full np_pre nn_pre l_np_optional).
      cancel (UIntArray.full dp_pre dn_pre l_dp_optional).
      apply derivable1_wand_sepcon_adjoint.
      Split.
      * normalize.
        Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
        unfold optional_q_full.
        Left.
        split_pure_spatial.
        -- rewrite H0, H1, H2, H3.
           cancel (UIntArray.seg np_pre 0 dn_pre l_rem_2).
           cancel (UIntArray.seg np_pre dn_pre nn_pre l_tail_2).
           cancel (UIntArray.full dp_pre dn_pre l_dp_optional).
        -- split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try tauto.
           rewrite H4, H2; assumption.
      * normalize.
        Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        exfalso.
        unfold NULL in *; tauto.
    + split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try tauto.
  - Intros_p Hnonnull.
    Exists qp_pre np_pre dp_pre nn_pre dn_pre n1_pre
           l_np_optional l_dp_optional dval_optional.
    Left.
    split_pure_spatial.
    + cancel (UIntArray.undef_full qp_pre ((nn_pre - dn_pre) + 1)).
      cancel (UIntArray.full np_pre nn_pre l_np_optional).
      cancel (UIntArray.full dp_pre dn_pre l_dp_optional).
      apply derivable1_wand_sepcon_adjoint.
      Split.
      * normalize.
        Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        exfalso.
        unfold NULL in *; tauto.
      * normalize.
        Intros rv_2.
        Intros qv_2.
        Intros l_tail_2.
        Intros l_rem_2.
        Intros l_q_2.
        Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
        unfold optional_q_full.
        Right.
        split_pure_spatial.
        -- rewrite H, H0, H1, H2, H3.
           cancel (UIntArray.full qp_pre ((nn_pre - dn_pre) + 1) l_q_2).
           cancel (UIntArray.seg np_pre 0 dn_pre l_rem_2).
           cancel (UIntArray.seg np_pre dn_pre nn_pre l_tail_2).
           cancel (UIntArray.full dp_pre dn_pre l_dp_optional).
        -- split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try tauto.
           rewrite H4, H2; assumption.
    + split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity; try tauto.
Qed. 
