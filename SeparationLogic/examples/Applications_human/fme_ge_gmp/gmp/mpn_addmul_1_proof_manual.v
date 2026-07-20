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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_addmul_1_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_addmul_1_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_addmul_1_entail_wit_1 : mpn_addmul_1_entail_wit_1.
Proof.
  pre_process.
  rename PreH1 into Hn_pos.
  rename PreH2 into Hn_max.
  rename PreH3 into Hvl_nonneg.
  rename PreH4 into Hvl_max.
  rename PreH5 into Hlen_rp.
  rename PreH6 into Hlen_up.
  rename PreH7 into Hbound_rp.
  rename PreH8 into Hbound_up.
  Exists (@nil Z).
  split_pure_spatial.
  - Intros.
    sep_apply (UIntArray.full_split_to_seg rp_pre 0 n_pre l_rp).
    + rewrite Zsublist_nil by lia.
      entailer!.
    + lia.
  - Intros.
    rewrite list_to_Z_nil.
    rewrite !Zsublist_nil by lia.
    rewrite list_to_Z_nil.
    entailer!.
Qed.

Lemma proof_of_mpn_addmul_1_entail_wit_5_1 : mpn_addmul_1_entail_wit_5_1.
Proof.
  pre_process.
  rename PreH1 into Hout_ge.
  rename PreH2 into Hlo_ge.
  rename PreH3 into Hvl_nonneg.
  rename PreH4 into Hvl_max.
  rename PreH5 into Hi_nonneg.
  rename PreH6 into Hi_lt.
  rename PreH7 into Hcl_nonneg.
  rename PreH8 into Hcl_max.
  rename PreH9 into Hlpl_nonneg.
  rename PreH10 into Hlpl_max.
  rename PreH11 into Hhpl_nonneg.
  rename PreH12 into Hhpl_max.
  rename PreH13 into Hlen_done.
  rename PreH14 into Hlen_rp.
  rename PreH15 into Hlen_up.
  rename PreH16 into Hbound_done.
  rename PreH17 into Hbound_rp.
  rename PreH18 into Hbound_up.
  rename PreH19 into Hinv.
  rename PreH20 into Hprod.
  pose proof Hout_ge as H.
  pose proof Hlo_ge as H0.
  pose proof Hi_nonneg as H3.
  pose proof Hi_lt as H4.
  pose proof Hlen_done as H11.
  pose proof Hlen_rp as H12.
  pose proof Hlen_up as H13.
  pose proof Hbound_done as H14.
  pose proof Hbound_rp as H15.
  pose proof Hbound_up as H16.
  pose proof Hinv as H17.
  pose proof Hprod as H18.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  Exists (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact H3 | rewrite H12; exact H4].
    - exact H15.
  }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact H3 | rewrite H13; exact H4].
    - exact H16.
  }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hhpl_upper: hpl <= UINT_MOD - 2).
  {
    assert (Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)) by (unfold UINT_MOD in *; nia).
    unfold UINT_MOD in *.
    nia.
  }
  assert (Hhpl_succ: unsigned_last_nbits (hpl + 1) 32 = hpl + 1).
  {
    unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_small; lia.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i)
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)
      (sublist i n_pre l_rp) =
    unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
    sublist (i + 1) n_pre l_rp).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact H3 | split; [exact H4 | rewrite H12; lia]].
  }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
       sublist (i + 1) n_pre l_rp)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      n_pre - i =
      Zlength (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
               sublist (i + 1) n_pre l_rp)).
    {
      rewrite Zlength_cons.
      rewrite Zlength_sublist.
      - lia.
      - split; [lia | rewrite H12; lia].
    }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil)).
    entailer!.
    entailer!.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    entailer!.
  - Intros.
    entailer!.
    + rewrite Hsub_rp_i in *.
      replace (0 + hpl + 0) with hpl by lia.
      rewrite (list_to_Z_concat_r UINT_MOD ltac:(unfold UINT_MOD; lia)).
      2: { change (2 ^ 32) with UINT_MOD in Hout_range. exact Hout_range. }
      rewrite H11.
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_rp i).
      2: { split; [exact H3 | rewrite H12; exact H4]. }
      2: { exact H15. }
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_up i).
      2: { split; [exact H3 | rewrite H13; exact H4]. }
      2: { exact H16. }
      replace ((list_to_Z UINT_MOD (sublist 0 i l_up) + Znth i l_up 0 * UINT_MOD ^ i) * vl_pre)
        with (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre + (Znth i l_up 0 * vl_pre) * UINT_MOD ^ i) by ring.
      rewrite <- H18.
      replace (list_to_Z UINT_MOD (sublist 0 i l_rp) + Znth i l_rp 0 * UINT_MOD ^ i +
        (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre + (hpl * UINT_MOD + lpl) * UINT_MOD ^ i))
        with ((list_to_Z UINT_MOD (sublist 0 i l_rp) + list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 + hpl * UINT_MOD + lpl) * UINT_MOD ^ i) by ring.
      rewrite <- H17.
      assert (H3add:
        lpl + Znth i l_rp 0 + cl =
        unsigned_last_nbits (Znth i l_rp 0 + unsigned_last_nbits (lpl + cl) 32) 32).
      {
        unfold unsigned_last_nbits in *.
        change (2 ^ 32) with UINT_MOD in *.
        replace (Znth i l_rp 0 + (lpl + cl) mod UINT_MOD) with ((lpl + cl) mod UINT_MOD + Znth i l_rp 0) in H by lia.
        pose proof (Z_mod_3add_carry00 lpl (Znth i l_rp 0) cl UINT_MOD) as HH.
        specialize (HH ltac:(unfold UINT_MOD; lia) ltac:(unfold UINT_MOD in *; lia) Hrp_bound ltac:(unfold UINT_MOD in *; lia) H0 H).
        replace ((Znth i l_rp 0 + (lpl + cl) mod UINT_MOD) mod UINT_MOD)
          with (((lpl + cl) mod UINT_MOD + Znth i l_rp 0) mod UINT_MOD) by (f_equal; lia).
        exact HH.
      }
      assert (Hpow: UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      change UINT_MOD with 4294967296 in *.
      nia.
    + apply list_within_bound_concat.
      * exact H14.
      * simpl. change UINT_MOD with 4294967296 in *. change (2 ^ 32) with 4294967296 in Hout_range. lia.
    + rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite Zlength_nil.
      rewrite H11.
      lia.
Qed.

Lemma proof_of_mpn_addmul_1_entail_wit_5_2 : mpn_addmul_1_entail_wit_5_2.
Proof.
  pre_process.
  rename PreH1 into Hout_ge.
  rename PreH2 into Hlo_ge.
  rename PreH3 into Hvl_nonneg.
  rename PreH4 into Hvl_max.
  rename PreH5 into Hi_nonneg.
  rename PreH6 into Hi_lt.
  rename PreH7 into Hcl_nonneg.
  rename PreH8 into Hcl_max.
  rename PreH9 into Hlpl_nonneg.
  rename PreH10 into Hlpl_max.
  rename PreH11 into Hhpl_nonneg.
  rename PreH12 into Hhpl_max.
  rename PreH13 into Hlen_done.
  rename PreH14 into Hlen_rp.
  rename PreH15 into Hlen_up.
  rename PreH16 into Hbound_done.
  rename PreH17 into Hbound_rp.
  rename PreH18 into Hbound_up.
  rename PreH19 into Hinv.
  rename PreH20 into Hprod.
  pose proof Hout_ge as H.
  pose proof Hlo_ge as H0.
  pose proof Hi_nonneg as H3.
  pose proof Hi_lt as H4.
  pose proof Hlen_done as H11.
  pose proof Hlen_rp as H12.
  pose proof Hlen_up as H13.
  pose proof Hbound_done as H14.
  pose proof Hbound_rp as H15.
  pose proof Hbound_up as H16.
  pose proof Hinv as H17.
  pose proof Hprod as H18.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  Exists (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact H3 | rewrite H12; exact H4].
    - exact H15. }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact H3 | rewrite H13; exact H4].
    - exact H16. }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia.
    f_equal; lia. }
  assert (Hhpl_upper: hpl <= UINT_MOD - 2).
  { assert (Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)) by (unfold UINT_MOD in *; nia).
    unfold UINT_MOD in *.
    nia. }
  assert (Hhpl_succ: unsigned_last_nbits (0 + hpl + 1) 32 = hpl + 1).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_small; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i)
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)
      (sublist i n_pre l_rp) =
    unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
    sublist (i + 1) n_pre l_rp).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact H3 | split; [exact H4 | rewrite H12; lia]]. }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
       sublist (i + 1) n_pre l_rp)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      n_pre - i =
      Zlength (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
               sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist.
      - lia.
      - split; [lia | rewrite H12; lia]. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil)).
    entailer!.
    entailer!.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    entailer!.
  - Intros.
    rewrite Hhpl_succ.
    entailer!.
    + rewrite Hsub_rp_i in *.
      rewrite (list_to_Z_concat_r UINT_MOD ltac:(unfold UINT_MOD; lia)).
      2: { change (2 ^ 32) with UINT_MOD in Hout_range. exact Hout_range. }
      rewrite H11.
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_rp i).
      2: { split; [exact H3 | rewrite H12; exact H4]. }
      2: { exact H15. }
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_up i).
      2: { split; [exact H3 | rewrite H13; exact H4]. }
      2: { exact H16. }
      replace ((list_to_Z UINT_MOD (sublist 0 i l_up) + Znth i l_up 0 * UINT_MOD ^ i) * vl_pre)
        with (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre + (Znth i l_up 0 * vl_pre) * UINT_MOD ^ i) by ring.
      rewrite <- H18.
      replace (list_to_Z UINT_MOD (sublist 0 i l_rp) + Znth i l_rp 0 * UINT_MOD ^ i +
        (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre + (hpl * UINT_MOD + lpl) * UINT_MOD ^ i))
        with ((list_to_Z UINT_MOD (sublist 0 i l_rp) + list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 + hpl * UINT_MOD + lpl) * UINT_MOD ^ i) by ring.
      rewrite <- H17.
      assert (H3add:
        lpl + Znth i l_rp 0 + cl =
        unsigned_last_nbits (Znth i l_rp 0 + unsigned_last_nbits (lpl + cl) 32) 32 + UINT_MOD).
      { unfold unsigned_last_nbits in *.
        change (2 ^ 32) with UINT_MOD in *.
        replace (Znth i l_rp 0 + (lpl + cl) mod UINT_MOD) with ((lpl + cl) mod UINT_MOD + Znth i l_rp 0) in H by lia.
        pose proof (Z_mod_3add_carry01 lpl (Znth i l_rp 0) cl UINT_MOD) as HH.
        specialize (HH ltac:(unfold UINT_MOD; lia) ltac:(unfold UINT_MOD in *; lia) Hrp_bound ltac:(unfold UINT_MOD in *; lia) H0 H).
        replace ((Znth i l_rp 0 + (lpl + cl) mod UINT_MOD) mod UINT_MOD)
          with (((lpl + cl) mod UINT_MOD + Znth i l_rp 0) mod UINT_MOD) by (f_equal; lia).
        exact HH. }
      assert (Hpow: UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      change UINT_MOD with 4294967296 in *.
      nia.
    + apply list_within_bound_concat.
      * exact H14.
      * simpl. change UINT_MOD with 4294967296 in *. change (2 ^ 32) with 4294967296 in Hout_range. lia.
    + rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite H11. lia.
Qed.

Lemma proof_of_mpn_addmul_1_entail_wit_5_3 : mpn_addmul_1_entail_wit_5_3.
Proof.
  pre_process.
  rename PreH1 into Hout_ge.
  rename PreH2 into Hlo_ge.
  rename PreH3 into Hvl_nonneg.
  rename PreH4 into Hvl_max.
  rename PreH5 into Hi_nonneg.
  rename PreH6 into Hi_lt.
  rename PreH7 into Hcl_nonneg.
  rename PreH8 into Hcl_max.
  rename PreH9 into Hlpl_nonneg.
  rename PreH10 into Hlpl_max.
  rename PreH11 into Hhpl_nonneg.
  rename PreH12 into Hhpl_max.
  rename PreH13 into Hlen_done.
  rename PreH14 into Hlen_rp.
  rename PreH15 into Hlen_up.
  rename PreH16 into Hbound_done.
  rename PreH17 into Hbound_rp.
  rename PreH18 into Hbound_up.
  rename PreH19 into Hinv.
  rename PreH20 into Hprod.
  pose proof Hout_ge as H.
  pose proof Hlo_ge as H0.
  pose proof Hi_nonneg as H3.
  pose proof Hi_lt as H4.
  pose proof Hlen_done as H11.
  pose proof Hlen_rp as H12.
  pose proof Hlen_up as H13.
  pose proof Hbound_done as H14.
  pose proof Hbound_rp as H15.
  pose proof Hbound_up as H16.
  pose proof Hinv as H17.
  pose proof Hprod as H18.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  Exists (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact H3 | rewrite H12; exact H4].
    - exact H15. }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact H3 | rewrite H13; exact H4].
    - exact H16. }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia.
    f_equal; lia. }
  assert (Hhpl_upper: hpl <= UINT_MOD - 2).
  { assert (Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)) by (unfold UINT_MOD in *; nia).
    unfold UINT_MOD in *.
    nia. }
  assert (Hhpl_succ: unsigned_last_nbits (1 + hpl) 32 + 0 = hpl + 1).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_small; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i)
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)
      (sublist i n_pre l_rp) =
    unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
    sublist (i + 1) n_pre l_rp).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact H3 | split; [exact H4 | rewrite H12; lia]]. }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
       sublist (i + 1) n_pre l_rp)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      n_pre - i =
      Zlength (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
               sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist.
      - lia.
      - split; [lia | rewrite H12; lia]. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil)).
    entailer!.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    entailer!.
  - Intros.
    rewrite Hhpl_succ.
    change UINT_MOD with 4294967296 in *.
    assert (Hdone_len:
      Zlength (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil) = i + 1).
    { rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite H11. lia. }
    assert (Hdone_bound:
      list_within_bound 4294967296
        (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil)).
    { apply list_within_bound_concat.
      - exact H14.
      - simpl. change (2 ^ 32) with 4294967296 in Hout_range. lia. }
    assert (Heq_main:
      list_to_Z 4294967296
        (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil) +
      (hpl + 1) * 4294967296 ^ (i + 1) =
      list_to_Z 4294967296 (sublist 0 (i + 1) l_rp) +
      list_to_Z 4294967296 (sublist 0 (i + 1) l_up) * vl_pre).
    { rewrite Hsub_rp_i in *.
      rewrite (list_to_Z_concat_r 4294967296 ltac:(lia)).
      2: { change (2 ^ 32) with 4294967296 in Hout_range. exact Hout_range. }
      rewrite H11.
      rewrite (list_to_Z_list_append 4294967296 ltac:(lia) l_rp i).
      2: { split; [exact H3 | rewrite H12; exact H4]. }
      2: { exact H15. }
      rewrite (list_to_Z_list_append 4294967296 ltac:(lia) l_up i).
      2: { split; [exact H3 | rewrite H13; exact H4]. }
      2: { exact H16. }
      replace ((list_to_Z 4294967296 (sublist 0 i l_up) + Znth i l_up 0 * 4294967296 ^ i) * vl_pre)
        with (list_to_Z 4294967296 (sublist 0 i l_up) * vl_pre + (Znth i l_up 0 * vl_pre) * 4294967296 ^ i) by ring.
      rewrite <- H18.
      replace (list_to_Z 4294967296 (sublist 0 i l_rp) + Znth i l_rp 0 * 4294967296 ^ i +
        (list_to_Z 4294967296 (sublist 0 i l_up) * vl_pre + (hpl * 4294967296 + lpl) * 4294967296 ^ i))
        with ((list_to_Z 4294967296 (sublist 0 i l_rp) + list_to_Z 4294967296 (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 + hpl * 4294967296 + lpl) * 4294967296 ^ i) by ring.
      rewrite <- H17.
      assert (H3add:
        lpl + Znth i l_rp 0 + cl =
        unsigned_last_nbits (Znth i l_rp 0 + unsigned_last_nbits (lpl + cl) 32) 32 + 4294967296).
      { unfold unsigned_last_nbits in *.
        change (2 ^ 32) with 4294967296 in *.
        replace (Znth i l_rp 0 + (lpl + cl) mod 4294967296) with ((lpl + cl) mod 4294967296 + Znth i l_rp 0) in H by lia.
        pose proof (Z_mod_3add_carry10 lpl (Znth i l_rp 0) cl 4294967296) as HH.
        specialize (HH ltac:(lia) ltac:(lia) Hrp_bound ltac:(lia) H0 H).
        replace ((Znth i l_rp 0 + (lpl + cl) mod 4294967296) mod 4294967296)
          with (((lpl + cl) mod 4294967296 + Znth i l_rp 0) mod 4294967296) by (f_equal; lia).
        exact HH. }
      assert (Hpow: 4294967296 ^ (i + 1) = 4294967296 * 4294967296 ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      nia. }
    entailer!.
Qed.

Lemma proof_of_mpn_addmul_1_entail_wit_5_4 : mpn_addmul_1_entail_wit_5_4.
Proof.
  pre_process.
  rename PreH1 into Hout_ge.
  rename PreH2 into Hlo_ge.
  rename PreH3 into Hvl_nonneg.
  rename PreH4 into Hvl_max.
  rename PreH5 into Hi_nonneg.
  rename PreH6 into Hi_lt.
  rename PreH7 into Hcl_nonneg.
  rename PreH8 into Hcl_max.
  rename PreH9 into Hlpl_nonneg.
  rename PreH10 into Hlpl_max.
  rename PreH11 into Hhpl_nonneg.
  rename PreH12 into Hhpl_max.
  rename PreH13 into Hlen_done.
  rename PreH14 into Hlen_rp.
  rename PreH15 into Hlen_up.
  rename PreH16 into Hbound_done.
  rename PreH17 into Hbound_rp.
  rename PreH18 into Hbound_up.
  rename PreH19 into Hinv.
  rename PreH20 into Hprod.
  pose proof Hout_ge as H.
  pose proof Hlo_ge as H0.
  pose proof Hi_nonneg as H3.
  pose proof Hi_lt as H4.
  pose proof Hlen_done as H11.
  pose proof Hlen_rp as H12.
  pose proof Hlen_up as H13.
  pose proof Hbound_done as H14.
  pose proof Hbound_rp as H15.
  pose proof Hbound_up as H16.
  pose proof Hinv as H17.
  pose proof Hprod as H18.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  Exists (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact H3 | rewrite H12; exact H4].
    - exact H15. }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact H3 | rewrite H13; exact H4].
    - exact H16. }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia.
    f_equal; lia. }
  assert (Hhpl_upper: hpl <= UINT_MOD - 3).
  { rewrite Hsub_rp_i in H.
    unfold unsigned_last_nbits in H, H0.
    change (2 ^ 32) with UINT_MOD in H, H0.
    replace (Znth i l_rp 0 + (lpl + cl) mod UINT_MOD) with ((lpl + cl) mod UINT_MOD + Znth i l_rp 0) in H by lia.
    assert (Hfirst_eq: lpl + cl = (lpl + cl) mod UINT_MOD + UINT_MOD).
    { apply Z_mod_add_carry; try lia; unfold UINT_MOD in *; lia. }
    assert (Hlow_pos: 0 < (lpl + cl) mod UINT_MOD).
    { pose proof (Z.mod_pos_bound (lpl + cl) UINT_MOD ltac:(unfold UINT_MOD; lia)).
      destruct (Z.eq_dec ((lpl + cl) mod UINT_MOD) 0) as [Heq | Hneq].
      - rewrite Heq in H.
        rewrite Z.add_0_l in H.
        rewrite Z.mod_small in H by exact Hrp_bound.
        lia.
      - lia. }
    assert (Hlpl_ge2: 2 <= lpl) by (unfold UINT_MOD in *; lia).
    assert (Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)) by (unfold UINT_MOD in *; nia).
    unfold UINT_MOD in *.
    nia. }
  assert (Hhpl_succ2: unsigned_last_nbits (unsigned_last_nbits (1 + hpl) 32 + 1) 32 = hpl + 2).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    change (2 ^ 32) with 4294967296.
    replace ((1 + hpl) mod 4294967296) with (1 + hpl) by (rewrite Z.mod_small; lia).
    rewrite Z.mod_small; lia. }
  assert (Hreplace_tail:
    replace_Znth (i - i)
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)
      (sublist i n_pre l_rp) =
    unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
    sublist (i + 1) n_pre l_rp).
  { replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact H3 | split; [exact H4 | rewrite H12; lia]]. }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
       sublist (i + 1) n_pre l_rp)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      n_pre - i =
      Zlength (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 ::
               sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist.
      - lia.
      - split; [lia | rewrite H12; lia]. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2
      (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil)).
    entailer!.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") (unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32)).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    entailer!.
  - Intros.
    rewrite Hhpl_succ2.
    change UINT_MOD with 4294967296 in *.
    assert (Hdone_len:
      Zlength (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil) = i + 1).
    { rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite H11. lia. }
    assert (Hdone_bound:
      list_within_bound 4294967296
        (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil)).
    { apply list_within_bound_concat.
      - exact H14.
      - simpl. change (2 ^ 32) with 4294967296 in Hout_range. lia. }
    assert (Heq_main:
      list_to_Z 4294967296
        (l_done_2 ++ unsigned_last_nbits (Znth (i - i) (sublist i n_pre l_rp) 0 + unsigned_last_nbits (lpl + cl) 32) 32 :: nil) +
      (hpl + 2) * 4294967296 ^ (i + 1) =
      list_to_Z 4294967296 (sublist 0 (i + 1) l_rp) +
      list_to_Z 4294967296 (sublist 0 (i + 1) l_up) * vl_pre).
    { rewrite Hsub_rp_i in *.
      rewrite (list_to_Z_concat_r 4294967296 ltac:(lia)).
      2: { change (2 ^ 32) with 4294967296 in Hout_range. exact Hout_range. }
      rewrite H11.
      rewrite (list_to_Z_list_append 4294967296 ltac:(lia) l_rp i).
      2: { split; [exact H3 | rewrite H12; exact H4]. }
      2: { exact H15. }
      rewrite (list_to_Z_list_append 4294967296 ltac:(lia) l_up i).
      2: { split; [exact H3 | rewrite H13; exact H4]. }
      2: { exact H16. }
      replace ((list_to_Z 4294967296 (sublist 0 i l_up) + Znth i l_up 0 * 4294967296 ^ i) * vl_pre)
        with (list_to_Z 4294967296 (sublist 0 i l_up) * vl_pre + (Znth i l_up 0 * vl_pre) * 4294967296 ^ i) by ring.
      rewrite <- H18.
      replace (list_to_Z 4294967296 (sublist 0 i l_rp) + Znth i l_rp 0 * 4294967296 ^ i +
        (list_to_Z 4294967296 (sublist 0 i l_up) * vl_pre + (hpl * 4294967296 + lpl) * 4294967296 ^ i))
        with ((list_to_Z 4294967296 (sublist 0 i l_rp) + list_to_Z 4294967296 (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 + hpl * 4294967296 + lpl) * 4294967296 ^ i) by ring.
      rewrite <- H17.
      assert (H3add:
        lpl + Znth i l_rp 0 + cl =
        unsigned_last_nbits (Znth i l_rp 0 + unsigned_last_nbits (lpl + cl) 32) 32 + 4294967296 * 2).
      { unfold unsigned_last_nbits in *.
        change (2 ^ 32) with 4294967296 in *.
        replace (Znth i l_rp 0 + (lpl + cl) mod 4294967296) with ((lpl + cl) mod 4294967296 + Znth i l_rp 0) in H by lia.
        pose proof (Z_mod_3add_carry11 lpl (Znth i l_rp 0) cl 4294967296) as HH.
        specialize (HH ltac:(lia) ltac:(lia) Hrp_bound ltac:(lia) H0 H).
        replace ((Znth i l_rp 0 + (lpl + cl) mod 4294967296) mod 4294967296)
          with (((lpl + cl) mod 4294967296 + Znth i l_rp 0) mod 4294967296) by (f_equal; lia).
        exact HH. }
      assert (Hpow: 4294967296 ^ (i + 1) = 4294967296 * 4294967296 ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      nia. }
    entailer!.
Qed.

Lemma proof_of_mpn_addmul_1_return_wit_1 : mpn_addmul_1_return_wit_1.
Proof.
  pre_process.
  rename PreH1 into Hi_ge.
  rename PreH2 into Hvl_nonneg.
  rename PreH3 into Hvl_max.
  rename PreH4 into Hi_nonneg.
  rename PreH5 into Hi_le.
  rename PreH6 into Hcl_nonneg.
  rename PreH7 into Hcl_max.
  rename PreH8 into Hlen_done.
  rename PreH9 into Hlen_rp.
  rename PreH10 into Hlen_up.
  rename PreH11 into Hbound_done.
  rename PreH12 into Hbound_rp.
  rename PreH13 into Hbound_up.
  rename PreH14 into Hinv.
  pose proof Hinv as H12.
  Exists (list_to_Z UINT_MOD l_done).
  Exists l_done.
  Intros.
  assert (Hi: i = n_pre) by lia.
  subst i.
  split_pure_spatial.
  - rewrite Zsublist_nil by lia.
    rewrite Hi.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l_done (@nil Z)).
    rewrite app_nil_r.
    sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_done).
    entailer!.
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    entailer!.
    lia.
  - Intros.
    rewrite Hi in H12.
    rewrite (sublist_self l_rp n_pre) in H12 by lia.
    rewrite (sublist_self l_up n_pre) in H12 by lia.
    entailer!.
Qed.
