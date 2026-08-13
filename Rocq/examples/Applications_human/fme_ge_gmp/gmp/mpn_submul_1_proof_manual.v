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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_submul_1_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_submul_1_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_submul_1_entail_wit_1_split_goal_1 :
  mpn_submul_1_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_1_split_goal_2 :
  mpn_submul_1_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_1_split_goal_3 :
  mpn_submul_1_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_1_split_goal_spatial :
  mpn_submul_1_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (UIntArray.full_split_to_seg rp_pre 0 n_pre l_rp).
  - dump_pre_spatial; lia.
  - rewrite Zsublist_nil by lia.
    replace n_pre with (Zlength l_rp) by lia.
    rewrite (sublist_self l_rp (Zlength l_rp)) by lia.
    rewrite UIntArray.seg_empty.
    Intros.
    cancel.
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_1 : mpn_submul_1_entail_wit_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_submul_1_entail_wit_1_split_goal_spatial.
  + Goal_apply proof_of_mpn_submul_1_entail_wit_1_split_goal_2.
  + Goal_apply proof_of_mpn_submul_1_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_4_split_goal_1 :
  mpn_submul_1_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_4 : mpn_submul_1_entail_wit_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_submul_1_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_5_1 : mpn_submul_1_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  set (out := unsigned_last_nbits
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32).
  Exists (l_done_2 ++ out :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact PreH5 | rewrite PreH14; exact PreH6].
    - exact PreH17.
  }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact PreH5 | rewrite PreH15; exact PreH6].
    - exact PreH18.
  }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hlow_eq: lpl + cl = unsigned_last_nbits (lpl + cl) 32).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    apply Z_mod_add_uncarry.
    - unfold UINT_MOD; lia.
    - unfold UINT_MOD in *; lia.
    - unfold UINT_MOD in *; lia.
    - unfold unsigned_last_nbits in PreH2.
      change (2 ^ 32) with UINT_MOD in PreH2.
      exact PreH2.
  }
  assert (Hle_sub: lpl + cl <= Znth i l_rp 0).
  {
    rewrite Hsub_rp_i in PreH1.
    rewrite <- Hlow_eq in PreH1.
    unfold unsigned_last_nbits in PreH1.
    change (2 ^ 32) with UINT_MOD in PreH1.
    destruct (Z_le_gt_dec (lpl + cl) (Znth i l_rp 0)); [lia|].
    assert (Hneg: (0 - UINT_MOD) < Znth i l_rp 0 - (lpl + cl) < 0)
      by (unfold UINT_MOD in *; lia).
    pose proof (Z_mod_neg (Znth i l_rp 0 - (lpl + cl)) UINT_MOD
      ltac:(unfold UINT_MOD; lia) Hneg) as Hmod.
    rewrite Hmod in PreH1.
    unfold UINT_MOD in *; lia.
  }
  assert (Hout_eq: out = Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32).
  {
    unfold out.
    rewrite Hsub_rp_i.
    rewrite <- Hlow_eq.
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z.mod_small; unfold UINT_MOD in *; lia.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i n_pre l_rp) =
    out :: sublist (i + 1) n_pre l_rp).
  {
    subst out.
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact PreH5 | split; [exact PreH6 | rewrite PreH14; lia]].
  }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (out :: sublist (i + 1) n_pre l_rp)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons: n_pre - i = Zlength (out :: sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") out).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    cancel.
  - Intros.
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite PreH13. lia.
    + apply list_within_bound_concat.
      * exact PreH16.
      * simpl. subst out. change (2 ^ 32) with UINT_MOD in Hout_range. lia.
    + rewrite (list_to_Z_concat_r UINT_MOD ltac:(unfold UINT_MOD; lia)).
      2: { subst out. change (2 ^ 32) with UINT_MOD in Hout_range. exact Hout_range. }
      rewrite PreH13.
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_rp i).
      2: { split; [exact PreH5 | rewrite PreH14; exact PreH6]. }
      2: { exact PreH17. }
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_up i).
      2: { split; [exact PreH5 | rewrite PreH15; exact PreH6]. }
      2: { exact PreH18. }
      replace ((list_to_Z UINT_MOD (sublist 0 i l_up) + Znth i l_up 0 * UINT_MOD ^ i) * vl_pre)
        with (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
              (Znth i l_up 0 * vl_pre) * UINT_MOD ^ i) by ring.
      rewrite <- PreH20.
      replace (list_to_Z UINT_MOD (sublist 0 i l_rp) + Znth i l_rp 0 * UINT_MOD ^ i -
        (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
         (hpl * UINT_MOD + lpl) * UINT_MOD ^ i))
        with ((list_to_Z UINT_MOD (sublist 0 i l_rp) -
               list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 - (hpl * UINT_MOD + lpl)) * UINT_MOD ^ i) by ring.
      rewrite <- PreH19.
      rewrite Hout_eq.
      rewrite <- Hlow_eq.
      assert (Hpow: UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      ring.
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_5_2 : mpn_submul_1_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  set (out := unsigned_last_nbits
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32).
  Exists (l_done_2 ++ out :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact PreH5 | rewrite PreH14; exact PreH6].
    - exact PreH17.
  }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact PreH5 | rewrite PreH15; exact PreH6].
    - exact PreH18.
  }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hlow_eq: lpl + cl = unsigned_last_nbits (lpl + cl) 32).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    apply Z_mod_add_uncarry.
    - unfold UINT_MOD; lia.
    - unfold UINT_MOD in *; lia.
    - unfold UINT_MOD in *; lia.
    - unfold unsigned_last_nbits in PreH2.
      change (2 ^ 32) with UINT_MOD in PreH2.
      exact PreH2.
  }
  assert (Hgt_sub: Znth i l_rp 0 < lpl + cl).
  {
    rewrite Hsub_rp_i in PreH1.
    rewrite <- Hlow_eq in PreH1.
    unfold unsigned_last_nbits in PreH1.
    change (2 ^ 32) with UINT_MOD in PreH1.
    destruct (Z_lt_ge_dec (Znth i l_rp 0) (lpl + cl)); [lia|].
    assert (Hdiff_range: 0 <= Znth i l_rp 0 - (lpl + cl) < UINT_MOD).
    { rewrite Hlow_eq. change (2 ^ 32) with UINT_MOD in Hlo_range. lia. }
    rewrite Z.mod_small in PreH1 by exact Hdiff_range.
    lia.
  }
  assert (Hout_eq: out = Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32 + UINT_MOD).
  {
    unfold out.
    rewrite Hsub_rp_i.
    rewrite <- Hlow_eq.
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z_mod_neg by (change (2 ^ 32) with UINT_MOD in Hlo_range; unfold UINT_MOD in *; lia).
    reflexivity.
  }
  assert (Hhpl_upper: hpl <= UINT_MOD - 2).
  {
    assert (Hprod_bound: Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)).
    { apply Z.mul_le_mono_nonneg; unfold UINT_MOD in *; lia. }
    unfold UINT_MOD in *; nia.
  }
  assert (Hret_eq: unsigned_last_nbits (0 + hpl + 1) 32 = hpl + 1).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z.mod_small; [reflexivity | unfold UINT_MOD in *; lia].
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i n_pre l_rp) =
    out :: sublist (i + 1) n_pre l_rp).
  {
    subst out.
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact PreH5 | split; [exact PreH6 | rewrite PreH14; lia]].
  }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (out :: sublist (i + 1) n_pre l_rp)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons: n_pre - i = Zlength (out :: sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") out).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    cancel.
  - Intros.
    rewrite Hret_eq.
    assert (Hret_range: 0 <= hpl + 1 <= 4294967295).
    { unfold UINT_MOD in *; lia. }
    assert (Hdone_len:
      Zlength (l_done_2 ++ out :: nil) = i + 1).
    { rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite PreH13. lia. }
    assert (Hdone_bound:
      list_within_bound UINT_MOD (l_done_2 ++ out :: nil)).
    {
      apply list_within_bound_concat.
      - exact PreH16.
      - simpl. subst out. change (2 ^ 32) with UINT_MOD in Hout_range. lia.
    }
    assert (Heq_main:
      list_to_Z UINT_MOD (l_done_2 ++ out :: nil) -
        (hpl + 1) * UINT_MOD ^ (i + 1) =
      list_to_Z UINT_MOD (sublist 0 (i + 1) l_rp) -
        list_to_Z UINT_MOD (sublist 0 (i + 1) l_up) * vl_pre).
    {
      rewrite (list_to_Z_concat_r UINT_MOD ltac:(unfold UINT_MOD; lia)).
      2: { subst out. change (2 ^ 32) with UINT_MOD in Hout_range. exact Hout_range. }
      rewrite PreH13.
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_rp i).
      2: { split; [exact PreH5 | rewrite PreH14; exact PreH6]. }
      2: { exact PreH17. }
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_up i).
      2: { split; [exact PreH5 | rewrite PreH15; exact PreH6]. }
      2: { exact PreH18. }
      replace ((list_to_Z UINT_MOD (sublist 0 i l_up) + Znth i l_up 0 * UINT_MOD ^ i) * vl_pre)
        with (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
              (Znth i l_up 0 * vl_pre) * UINT_MOD ^ i) by ring.
      rewrite <- PreH20.
      replace (list_to_Z UINT_MOD (sublist 0 i l_rp) + Znth i l_rp 0 * UINT_MOD ^ i -
        (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
         (hpl * UINT_MOD + lpl) * UINT_MOD ^ i))
        with ((list_to_Z UINT_MOD (sublist 0 i l_rp) -
               list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 - (hpl * UINT_MOD + lpl)) * UINT_MOD ^ i) by ring.
      rewrite <- PreH19.
      rewrite Hout_eq.
      rewrite <- Hlow_eq.
      assert (Hpow: UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      ring.
    }
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_5_3 : mpn_submul_1_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  set (out := unsigned_last_nbits
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32).
  Exists (l_done_2 ++ out :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact PreH5 | rewrite PreH14; exact PreH6].
    - exact PreH17.
  }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact PreH5 | rewrite PreH15; exact PreH6].
    - exact PreH18.
  }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hlow_carry: lpl + cl = unsigned_last_nbits (lpl + cl) 32 + UINT_MOD).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    apply Z_mod_add_carry.
    - unfold UINT_MOD; lia.
    - unfold UINT_MOD in *; lia.
    - unfold UINT_MOD in *; lia.
    - unfold unsigned_last_nbits in PreH2.
      change (2 ^ 32) with UINT_MOD in PreH2.
      exact PreH2.
  }
  assert (Hlow_expr: unsigned_last_nbits (lpl + cl) 32 = lpl + cl - UINT_MOD) by lia.
  assert (Hle_low: unsigned_last_nbits (lpl + cl) 32 <= Znth i l_rp 0).
  {
    rewrite Hsub_rp_i in PreH1.
    destruct (Z_le_gt_dec (unsigned_last_nbits (lpl + cl) 32) (Znth i l_rp 0)); [lia|].
    assert (Hneg: (0 - UINT_MOD) <
      Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32 < 0).
    { change (2 ^ 32) with UINT_MOD in Hlo_range. unfold UINT_MOD in *; lia. }
    assert (Hout_neg:
      unsigned_last_nbits (Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32) 32 =
      Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32 + UINT_MOD).
    {
      unfold unsigned_last_nbits.
      change (2 ^ 32) with UINT_MOD.
      pose proof (Z_mod_neg
        (Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32)
        UINT_MOD ltac:(unfold UINT_MOD; lia) Hneg) as Hmod.
      exact Hmod.
    }
    rewrite Hout_neg in PreH1.
    change (2 ^ 32) with UINT_MOD in Hlo_range.
    unfold UINT_MOD in *; lia.
  }
  assert (Hout_eq: out = Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32).
  {
    unfold out.
    rewrite Hsub_rp_i.
    unfold unsigned_last_nbits at 1.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z.mod_small.
    - reflexivity.
    - change (2 ^ 32) with UINT_MOD in Hlo_range.
      unfold UINT_MOD in *; lia.
  }
  assert (Hhpl_upper: hpl <= UINT_MOD - 2).
  {
    assert (Hprod_bound: Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)).
    { apply Z.mul_le_mono_nonneg; unfold UINT_MOD in *; lia. }
    unfold UINT_MOD in *; nia.
  }
  assert (Hret_eq: unsigned_last_nbits (1 + hpl) 32 = hpl + 1).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z.mod_small; [ring | unfold UINT_MOD in *; lia].
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i n_pre l_rp) =
    out :: sublist (i + 1) n_pre l_rp).
  {
    subst out.
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact PreH5 | split; [exact PreH6 | rewrite PreH14; lia]].
  }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - clear Hrp_bound Hup_bound Hlo_range Hout_range Hlow_carry Hlow_expr
      Hle_low Hout_eq Hhpl_upper Hret_eq.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (out :: sublist (i + 1) n_pre l_rp)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons: n_pre - i = Zlength (out :: sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") out).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    cancel.
  - Intros.
    rewrite Hret_eq.
    assert (Hret_range: 0 <= hpl + 1 <= 4294967295).
    { unfold UINT_MOD in *; lia. }
    assert (Hdone_len:
      Zlength (l_done_2 ++ out :: nil) = i + 1).
    { rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite PreH13. lia. }
    assert (Hdone_bound:
      list_within_bound UINT_MOD (l_done_2 ++ out :: nil)).
    {
      apply list_within_bound_concat.
      - exact PreH16.
      - simpl. subst out. change (2 ^ 32) with UINT_MOD in Hout_range. lia.
    }
    assert (Heq_main:
      list_to_Z UINT_MOD (l_done_2 ++ out :: nil) -
        (hpl + 1) * UINT_MOD ^ (i + 1) =
      list_to_Z UINT_MOD (sublist 0 (i + 1) l_rp) -
        list_to_Z UINT_MOD (sublist 0 (i + 1) l_up) * vl_pre).
    {
      rewrite (list_to_Z_concat_r UINT_MOD ltac:(unfold UINT_MOD; lia)).
      2: { subst out. change (2 ^ 32) with UINT_MOD in Hout_range. exact Hout_range. }
      rewrite PreH13.
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_rp i).
      2: { split; [exact PreH5 | rewrite PreH14; exact PreH6]. }
      2: { exact PreH17. }
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_up i).
      2: { split; [exact PreH5 | rewrite PreH15; exact PreH6]. }
      2: { exact PreH18. }
      replace ((list_to_Z UINT_MOD (sublist 0 i l_up) + Znth i l_up 0 * UINT_MOD ^ i) * vl_pre)
        with (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
              (Znth i l_up 0 * vl_pre) * UINT_MOD ^ i) by ring.
      rewrite <- PreH20.
      replace (list_to_Z UINT_MOD (sublist 0 i l_rp) + Znth i l_rp 0 * UINT_MOD ^ i -
        (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
         (hpl * UINT_MOD + lpl) * UINT_MOD ^ i))
        with ((list_to_Z UINT_MOD (sublist 0 i l_rp) -
               list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 - (hpl * UINT_MOD + lpl)) * UINT_MOD ^ i) by ring.
      rewrite <- PreH19.
      rewrite Hout_eq.
      rewrite Hlow_expr.
      assert (Hpow: UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      ring.
    }
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_submul_1_entail_wit_5_4 : mpn_submul_1_entail_wit_5_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  pose proof (unsigned_Lastnbits_range (lpl + cl) 32 ltac:(lia)) as Hlo_range.
  pose proof (unsigned_Lastnbits_range
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32 ltac:(lia)) as Hout_range.
  set (out := unsigned_last_nbits
    (Znth (i - i) (sublist i n_pre l_rp) 0 -
     unsigned_last_nbits (lpl + cl) 32) 32).
  Exists (l_done_2 ++ out :: nil).
  Intros.
  assert (Hrp_bound: 0 <= Znth i l_rp 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_rp i).
    - split; [exact PreH5 | rewrite PreH14; exact PreH6].
    - exact PreH17.
  }
  assert (Hup_bound: 0 <= Znth i l_up 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l_up i).
    - split; [exact PreH5 | rewrite PreH15; exact PreH6].
    - exact PreH18.
  }
  assert (Hsub_rp_i: Znth (i - i) (sublist i n_pre l_rp) 0 = Znth i l_rp 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hlow_carry: lpl + cl = unsigned_last_nbits (lpl + cl) 32 + UINT_MOD).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    apply Z_mod_add_carry.
    - unfold UINT_MOD; lia.
    - unfold UINT_MOD in *; lia.
    - unfold UINT_MOD in *; lia.
    - unfold unsigned_last_nbits in PreH2.
      change (2 ^ 32) with UINT_MOD in PreH2.
      exact PreH2.
  }
  assert (Hlow_expr: unsigned_last_nbits (lpl + cl) 32 = lpl + cl - UINT_MOD) by lia.
  assert (Hgt_low: Znth i l_rp 0 < unsigned_last_nbits (lpl + cl) 32).
  {
    rewrite Hsub_rp_i in PreH1.
    destruct (Z_lt_ge_dec (Znth i l_rp 0) (unsigned_last_nbits (lpl + cl) 32)); [lia|].
    assert (Hdiff_range:
      0 <= Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32 < UINT_MOD).
    { change (2 ^ 32) with UINT_MOD in Hlo_range. unfold UINT_MOD in *; lia. }
    assert (Hout_small:
      unsigned_last_nbits (Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32) 32 =
      Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32).
    {
      unfold unsigned_last_nbits.
      change (2 ^ 32) with UINT_MOD.
      rewrite Z.mod_small; [reflexivity | exact Hdiff_range].
    }
    rewrite Hout_small in PreH1.
    lia.
  }
  assert (Hout_eq: out = Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32 + UINT_MOD).
  {
    unfold out.
    rewrite Hsub_rp_i.
    assert (Hneg:
      0 - UINT_MOD < Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32 < 0).
    { change (2 ^ 32) with UINT_MOD in Hlo_range. unfold UINT_MOD in *; lia. }
    unfold unsigned_last_nbits at 1.
    change (2 ^ 32) with UINT_MOD.
    pose proof (Z_mod_neg
      (Znth i l_rp 0 - unsigned_last_nbits (lpl + cl) 32)
      UINT_MOD ltac:(unfold UINT_MOD; lia) Hneg) as Hmod.
    exact Hmod.
  }
  assert (Hlpl_ge2: 2 <= lpl).
  { rewrite Hlow_expr in Hgt_low. unfold UINT_MOD in *; lia. }
  assert (Hhpl_upper: hpl <= UINT_MOD - 3).
  {
    assert (Hprod_bound: Znth i l_up 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)).
    { apply Z.mul_le_mono_nonneg; unfold UINT_MOD in *; lia. }
    unfold UINT_MOD in *; nia.
  }
  assert (Hret1: unsigned_last_nbits (1 + hpl) 32 = hpl + 1).
  {
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z.mod_small; [ring | unfold UINT_MOD in *; lia].
  }
  assert (Hret_eq:
    unsigned_last_nbits (unsigned_last_nbits (1 + hpl) 32 + 1) 32 = hpl + 2).
  {
    rewrite Hret1.
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    rewrite Z.mod_small; [ring | unfold UINT_MOD in *; lia].
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i n_pre l_rp) =
    out :: sublist (i + 1) n_pre l_rp).
  {
    subst out.
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [exact PreH5 | split; [exact PreH6 | rewrite PreH14; lia]].
  }
  rewrite Hreplace_tail.
  split_pure_spatial.
  - clear Hrp_bound Hup_bound Hlo_range Hout_range Hlow_carry Hlow_expr
      Hgt_low Hout_eq Hlpl_ge2 Hhpl_upper Hret1 Hret_eq.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) n_pre
      (out :: sublist (i + 1) n_pre l_rp)).
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons: n_pre - i = Zlength (out :: sublist (i + 1) n_pre l_rp)).
    { rewrite Zlength_cons. rewrite Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_done_2 (out :: nil)).
    dump_pre_spatial; lia.
    cancel.
    sep_apply (store_uint_undef_store_uint &("lpl") out).
    sep_apply (store_uint_undef_store_uint &("hpl") hpl).
    sep_apply (store_uint_undef_store_uint &("ul") (Znth i l_up 0)).
    sep_apply (store_uint_undef_store_uint &("rl") (Znth (i - i) (sublist i n_pre l_rp) 0)).
    cancel.
  - Intros.
    rewrite Hret_eq.
    assert (Hret_range: 0 <= hpl + 2 <= 4294967295).
    { unfold UINT_MOD in *; lia. }
    assert (Hdone_len:
      Zlength (l_done_2 ++ out :: nil) = i + 1).
    { rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. rewrite PreH13. lia. }
    assert (Hdone_bound:
      list_within_bound UINT_MOD (l_done_2 ++ out :: nil)).
    {
      apply list_within_bound_concat.
      - exact PreH16.
      - simpl. subst out. change (2 ^ 32) with UINT_MOD in Hout_range. lia.
    }
    assert (Heq_main:
      list_to_Z UINT_MOD (l_done_2 ++ out :: nil) -
        (hpl + 2) * UINT_MOD ^ (i + 1) =
      list_to_Z UINT_MOD (sublist 0 (i + 1) l_rp) -
        list_to_Z UINT_MOD (sublist 0 (i + 1) l_up) * vl_pre).
    {
      rewrite (list_to_Z_concat_r UINT_MOD ltac:(unfold UINT_MOD; lia)).
      2: { subst out. change (2 ^ 32) with UINT_MOD in Hout_range. exact Hout_range. }
      rewrite PreH13.
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_rp i).
      2: { split; [exact PreH5 | rewrite PreH14; exact PreH6]. }
      2: { exact PreH17. }
      rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l_up i).
      2: { split; [exact PreH5 | rewrite PreH15; exact PreH6]. }
      2: { exact PreH18. }
      replace ((list_to_Z UINT_MOD (sublist 0 i l_up) + Znth i l_up 0 * UINT_MOD ^ i) * vl_pre)
        with (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
              (Znth i l_up 0 * vl_pre) * UINT_MOD ^ i) by ring.
      rewrite <- PreH20.
      replace (list_to_Z UINT_MOD (sublist 0 i l_rp) + Znth i l_rp 0 * UINT_MOD ^ i -
        (list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre +
         (hpl * UINT_MOD + lpl) * UINT_MOD ^ i))
        with ((list_to_Z UINT_MOD (sublist 0 i l_rp) -
               list_to_Z UINT_MOD (sublist 0 i l_up) * vl_pre) +
              (Znth i l_rp 0 - (hpl * UINT_MOD + lpl)) * UINT_MOD ^ i) by ring.
      rewrite <- PreH19.
      rewrite Hout_eq.
      rewrite Hlow_expr.
      assert (Hpow: UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
      { rewrite Z.pow_add_r by lia. ring. }
      rewrite Hpow.
      ring.
    }
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_submul_1_return_wit_1 : mpn_submul_1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
    sep_apply_l_atomic
      (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l_done (@nil Z)).
    + dump_pre_spatial; lia.
    + rewrite app_nil_r.
      sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_done).
      replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
      replace (n_pre - 0) with n_pre by lia.
      cancel.
  - Intros.
    rewrite Hi in H12.
    rewrite (sublist_self l_rp n_pre) in H12 by lia.
    rewrite (sublist_self l_up n_pre) in H12 by lia.
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.
