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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_add_n_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_add_n_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_add_n_entail_wit_1_rp_eq_bp : mpn_add_n_entail_wit_1_rp_eq_bp.
Proof.
  pre_process.
  Exists 0 (@nil Z).
  Exists 0 0.
  rewrite PreH9.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_rp_eq_ap : mpn_add_n_entail_wit_2_rp_eq_ap.
Proof.
  pre_process.
  Exists 0 (@nil Z).
  Exists 0 0.
  rewrite PreH9.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_3_1_rp_eq_bp : mpn_add_n_entail_wit_3_1_rp_eq_bp.
Proof.
  pre_process.
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32) as Hinner_range.
  assert (Hinner:
    unsigned_last_nbits (Znth i l_a 0 + cy) 32 = Znth i l_a 0 + cy).
  {
    unfold unsigned_last_nbits in *.
    change (2 ^ 32) with 4294967296 in *.
    symmetry.
    apply Z_mod_add_uncarry; unfold UINT_MOD in *; lia.
  }
  assert (Houter:
    unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 =
    Znth i l_a 0 + cy + Znth i l_b 0).
  {
    rewrite Hinner.
    rewrite Hinner in PreH1.
    pose proof (Hinner_range ltac:(lia)) as Hinner_bound.
    rewrite Hinner in Hinner_bound.
    unfold unsigned_last_nbits in *.
    change (2 ^ 32) with 4294967296 in *.
    symmetry.
    replace (Znth i l_a 0 + cy + Znth i l_b 0)
      with ((Znth i l_a 0 + cy) + Znth i l_b 0) by ring.
    assert (Houter_a_range: 0 <= Znth i l_a 0 + cy < 4294967296) by lia.
    assert (Houter_b_range: 0 <= Znth i l_b 0 < 4294967296) by (unfold UINT_MOD in *; lia).
    assert (Houter_cond:
      ((Znth i l_a 0 + cy) + Znth i l_b 0) mod 4294967296 >= Znth i l_b 0).
    {
      replace ((Znth i l_a 0 + cy) + Znth i l_b 0)
        with (Znth i l_a 0 + cy + Znth i l_b 0) by ring.
      exact PreH1.
    }
    pose proof (Z_mod_add_uncarry (Znth i l_a 0 + cy) (Znth i l_b 0) 4294967296
      ltac:(lia) Houter_a_range Houter_b_range Houter_cond) as Huncarry.
    exact Huncarry.
  }
  rewrite Houter in *.
  assert (Hreplace_tail:
    replace_Znth (i - i) (Znth i l_a 0 + cy + Znth i l_b 0)
      (sublist i (Zlength l_a) l_b) =
    (Znth i l_a 0 + cy + Znth i l_b 0) ::
    sublist (i + 1) (Zlength l_a) l_b).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      ((Znth i l_a 0 + cy + Znth i l_b 0) ::
       sublist (i + 1) (Zlength l_a) l_b)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i =
      Zlength ((Znth i l_a 0 + cy + Znth i l_b 0) ::
        sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2
      ((Znth i l_a 0 + cy + Znth i l_b 0) :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    ring.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_3_2_rp_eq_bp : mpn_add_n_entail_wit_3_2_rp_eq_bp.
Proof.
  pre_process.
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  set (out := unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32) as Hinner_range.
  assert (Hfirst:
    unsigned_last_nbits (Znth i l_a 0 + cy) 32 = Znth i l_a 0 + cy).
  {
    unfold unsigned_last_nbits in Hinner_range, PreH2 |- *.
    change (2 ^ 32) with UINT_MOD in Hinner_range.
    change (2 ^ 32) with UINT_MOD in PreH2.
    symmetry.
    change (2 ^ 32) with UINT_MOD.
    pose proof (Z_mod_add_uncarry (Znth i l_a 0) cy UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      ltac:(unfold UINT_MOD in *; lia)
      ltac:(unfold UINT_MOD in *; lia)
      ltac:(unfold UINT_MOD in *; lia)) as Huncarry.
    exact Huncarry.
  }
  assert (Hfinal:
    unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0 = out + UINT_MOD).
  {
    assert (Hlow_bound:
      0 <= unsigned_last_nbits (Znth i l_a 0 + cy) 32 < UINT_MOD).
    {
      pose proof (Hinner_range ltac:(lia)) as Hlow.
      change (2 ^ 32) with UINT_MOD in Hlow.
      exact Hlow.
    }
    assert (Houter_cond:
      (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) mod UINT_MOD < Znth i l_b 0).
    {
      unfold unsigned_last_nbits in PreH1 |- *.
      change (2 ^ 32) with UINT_MOD in PreH1.
      change (2 ^ 32) with UINT_MOD.
      exact PreH1.
    }
    subst out.
    unfold unsigned_last_nbits in |- *.
    change (2 ^ 32) with UINT_MOD.
    pose proof (Z_mod_add_carry (unsigned_last_nbits (Znth i l_a 0 + cy) 32)
      (Znth i l_b 0) UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      ltac:(unfold UINT_MOD in *; lia)
      ltac:(unfold UINT_MOD in *; lia)
      Houter_cond) as Hcarry.
    exact Hcarry.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    unfold UINT_MOD in Hfirst, Hfinal.
    nia.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_3_3_rp_eq_bp : mpn_add_n_entail_wit_3_3_rp_eq_bp.
Proof.
  pre_process.
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (Ha_bound: 0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
    unfold UINT_MOD in *; lia.
  }
  assert (Hb_bound: 0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
  }
  assert (Hcy_bound: 0 <= cy < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hout_bound: 0 <= out < UINT_MOD).
  {
    subst out.
    change UINT_MOD with (2 ^ 32).
    apply unsigned_Lastnbits_range; lia.
  }
  assert (list_within_bound UINT_MOD (out :: nil)).
  { simpl; tauto. }
  assert (Hsum:
    Znth i l_a 0 + Znth i l_b 0 + cy = out + UINT_MOD).
  {
    change ((Znth i l_a 0 + cy) mod UINT_MOD < cy) in PreH2.
    change
      (((Znth i l_a 0 + cy) mod UINT_MOD + Znth i l_b 0) mod UINT_MOD
        >= Znth i l_b 0) in PreH1.
    pose proof (Z_mod_3add_carry10
      (Znth i l_a 0) (Znth i l_b 0) cy UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      Ha_bound Hb_bound Hcy_bound PreH2 PreH1) as Hcarry.
    subst out.
    exact Hcarry.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    ring.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_3_4_rp_eq_bp : mpn_add_n_entail_wit_3_4_rp_eq_bp.
Proof.
  pre_process.
  assert (Hb_sub: Znth (i - i) (sublist i (Zlength l_a) l_b) 0 = Znth i l_b 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Hb_sub in *.
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (Ha_bound: 0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
    unfold UINT_MOD in *; lia.
  }
  assert (Hb_bound: 0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
  }
  assert (Hcy_bound: 0 <= cy < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hout_bound: 0 <= out < UINT_MOD).
  {
    subst out.
    change UINT_MOD with (2 ^ 32).
    apply unsigned_Lastnbits_range; lia.
  }
  assert (list_within_bound UINT_MOD (out :: nil)).
  { simpl; tauto. }
  assert (Hsum:
    Znth i l_a 0 + Znth i l_b 0 + cy = out + UINT_MOD * 2).
  {
    change ((Znth i l_a 0 + cy) mod UINT_MOD < cy) in PreH2.
    change
      (((Znth i l_a 0 + cy) mod UINT_MOD + Znth i l_b 0) mod UINT_MOD
        < Znth i l_b 0) in PreH1.
    pose proof (Z_mod_3add_carry11
      (Znth i l_a 0) (Znth i l_b 0) cy UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      Ha_bound Hb_bound Hcy_bound PreH2 PreH1) as Hcarry.
    subst out.
    exact Hcarry.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_b) =
    out :: sublist (i + 1) (Zlength l_a) l_b).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_b)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_b)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    ring.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_4_1_rp_eq_ap : mpn_add_n_entail_wit_4_1_rp_eq_ap.
Proof.
  pre_process.
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32) as Hinner_range.
  assert (Hinner:
    unsigned_last_nbits (Znth i l_a 0 + cy) 32 = Znth i l_a 0 + cy).
  {
    unfold unsigned_last_nbits in *.
    change (2 ^ 32) with 4294967296 in *.
    symmetry.
    apply Z_mod_add_uncarry; unfold UINT_MOD in *; lia.
  }
  assert (Houter:
    unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 =
    Znth i l_a 0 + cy + Znth i l_b 0).
  {
    rewrite Hinner.
    rewrite Hinner in PreH1.
    pose proof (Hinner_range ltac:(lia)) as Hinner_bound.
    rewrite Hinner in Hinner_bound.
    unfold unsigned_last_nbits in *.
    change (2 ^ 32) with 4294967296 in *.
    symmetry.
    replace (Znth i l_a 0 + cy + Znth i l_b 0)
      with ((Znth i l_a 0 + cy) + Znth i l_b 0) by ring.
    assert (Houter_a_range: 0 <= Znth i l_a 0 + cy < 4294967296) by lia.
    assert (Houter_b_range: 0 <= Znth i l_b 0 < 4294967296) by (unfold UINT_MOD in *; lia).
    assert (Houter_cond:
      ((Znth i l_a 0 + cy) + Znth i l_b 0) mod 4294967296 >= Znth i l_b 0).
    {
      replace ((Znth i l_a 0 + cy) + Znth i l_b 0)
        with (Znth i l_a 0 + cy + Znth i l_b 0) by ring.
      exact PreH1.
    }
    pose proof (Z_mod_add_uncarry (Znth i l_a 0 + cy) (Znth i l_b 0) 4294967296
      ltac:(lia) Houter_a_range Houter_b_range Houter_cond) as Huncarry.
    exact Huncarry.
  }
  rewrite Houter in *.
  assert (Hreplace_tail:
    replace_Znth (i - i) (Znth i l_a 0 + cy + Znth i l_b 0)
      (sublist i (Zlength l_a) l_a) =
    (Znth i l_a 0 + cy + Znth i l_b 0) ::
    sublist (i + 1) (Zlength l_a) l_a).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      ((Znth i l_a 0 + cy + Znth i l_b 0) ::
       sublist (i + 1) (Zlength l_a) l_a)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i =
      Zlength ((Znth i l_a 0 + cy + Znth i l_b 0) ::
        sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2
      ((Znth i l_a 0 + cy + Znth i l_b 0) :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    ring.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_4_2_rp_eq_ap : mpn_add_n_entail_wit_4_2_rp_eq_ap.
Proof.
  pre_process.
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  set (out := unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  assert (list_within_bound UINT_MOD (out :: nil)).
  { subst out. simpl. unfold UINT_MOD in *. lia. }
  assert (0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
    unfold UINT_MOD in *. lia.
  }
  assert (0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth ; try lia ; try tauto.
  }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32) as Hinner_range.
  assert (Hfirst:
    unsigned_last_nbits (Znth i l_a 0 + cy) 32 = Znth i l_a 0 + cy).
  {
    unfold unsigned_last_nbits in Hinner_range, PreH2 |- *.
    change (2 ^ 32) with UINT_MOD in Hinner_range.
    change (2 ^ 32) with UINT_MOD in PreH2.
    symmetry.
    change (2 ^ 32) with UINT_MOD.
    pose proof (Z_mod_add_uncarry (Znth i l_a 0) cy UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      ltac:(unfold UINT_MOD in *; lia)
      ltac:(unfold UINT_MOD in *; lia)
      ltac:(unfold UINT_MOD in *; lia)) as Huncarry.
    exact Huncarry.
  }
  assert (Hfinal:
    unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0 = out + UINT_MOD).
  {
    assert (Hlow_bound:
      0 <= unsigned_last_nbits (Znth i l_a 0 + cy) 32 < UINT_MOD).
    {
      pose proof (Hinner_range ltac:(lia)) as Hlow.
      change (2 ^ 32) with UINT_MOD in Hlow.
      exact Hlow.
    }
    assert (Houter_cond:
      (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) mod UINT_MOD < Znth i l_b 0).
    {
      unfold unsigned_last_nbits in PreH1 |- *.
      change (2 ^ 32) with UINT_MOD in PreH1.
      change (2 ^ 32) with UINT_MOD.
      exact PreH1.
    }
    subst out.
    unfold unsigned_last_nbits in |- *.
    change (2 ^ 32) with UINT_MOD.
    pose proof (Z_mod_add_carry (unsigned_last_nbits (Znth i l_a 0 + cy) 32)
      (Znth i l_b 0) UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      ltac:(unfold UINT_MOD in *; lia)
      ltac:(unfold UINT_MOD in *; lia)
      Houter_cond) as Hcarry.
    exact Hcarry.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    unfold UINT_MOD in Hfirst, Hfinal.
    nia.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_4_3_rp_eq_ap : mpn_add_n_entail_wit_4_3_rp_eq_ap.
Proof.
  pre_process.
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (Ha_bound: 0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
    unfold UINT_MOD in *; lia.
  }
  assert (Hb_bound: 0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
  }
  assert (Hcy_bound: 0 <= cy < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hout_bound: 0 <= out < UINT_MOD).
  {
    subst out.
    change UINT_MOD with (2 ^ 32).
    apply unsigned_Lastnbits_range; lia.
  }
  assert (list_within_bound UINT_MOD (out :: nil)).
  { simpl; tauto. }
  assert (Hsum:
    Znth i l_a 0 + Znth i l_b 0 + cy = out + UINT_MOD).
  {
    change ((Znth i l_a 0 + cy) mod UINT_MOD < cy) in PreH2.
    change
      (((Znth i l_a 0 + cy) mod UINT_MOD + Znth i l_b 0) mod UINT_MOD
        >= Znth i l_b 0) in PreH1.
    pose proof (Z_mod_3add_carry10
      (Znth i l_a 0) (Znth i l_b 0) cy UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      Ha_bound Hb_bound Hcy_bound PreH2 PreH1) as Hcarry.
    subst out.
    exact Hcarry.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    ring.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_4_4_rp_eq_ap : mpn_add_n_entail_wit_4_4_rp_eq_ap.
Proof.
  pre_process.
  assert (Ha_sub: Znth (i - i) (sublist i (Zlength l_a) l_a) 0 = Znth i l_a 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  rewrite Ha_sub in *.
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  Exists (val_r_2 + out * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ out :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i)
    (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  assert (Ha_bound: 0 <= Znth i l_a 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
    unfold UINT_MOD in *; lia.
  }
  assert (Hb_bound: 0 <= Znth i l_b 0 < UINT_MOD).
  {
    apply list_within_bound_Znth; try lia; try tauto.
  }
  assert (Hcy_bound: 0 <= cy < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hout_bound: 0 <= out < UINT_MOD).
  {
    subst out.
    change UINT_MOD with (2 ^ 32).
    apply unsigned_Lastnbits_range; lia.
  }
  assert (list_within_bound UINT_MOD (out :: nil)).
  { simpl; tauto. }
  assert (Hsum:
    Znth i l_a 0 + Znth i l_b 0 + cy = out + UINT_MOD * 2).
  {
    change ((Znth i l_a 0 + cy) mod UINT_MOD < cy) in PreH2.
    change
      (((Znth i l_a 0 + cy) mod UINT_MOD + Znth i l_b 0) mod UINT_MOD
        < Znth i l_b 0) in PreH1.
    pose proof (Z_mod_3add_carry11
      (Znth i l_a 0) (Znth i l_b 0) cy UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      Ha_bound Hb_bound Hcy_bound PreH2 PreH1) as Hcarry.
    subst out.
    exact Hcarry.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) out (sublist i (Zlength l_a) l_a) =
    out :: sublist (i + 1) (Zlength l_a) l_a).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  rewrite Hreplace_tail.
  entailer! ; unfold UINT_MOD in *.
  + sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l_a)
      (out :: sublist (i + 1) (Zlength l_a) l_a)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l_a - i = Zlength (out :: sublist (i + 1) (Zlength l_a) l_a)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l_r_2 (out :: nil)).
    entailer!.
    match goal with H : _ = _ |- _ => rewrite H end.
    entailer!.
  + rewrite PreH16.
    replace (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i +
      (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i))
      with ((val_a_prefix_2 + val_b_prefix_2) +
        (Znth i l_a 0 + Znth i l_b 0) * 4294967296 ^ i) by ring.
    rewrite <- PreH19.
    rewrite Z.pow_add_r ; try lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH12.
    rewrite list_to_Z_cons, list_to_Z_nil.
    ring.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH11.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite PreH10.
      rewrite list_to_Z_cons, list_to_Z_nil.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. ring.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
Qed.

Lemma proof_of_mpn_add_n_return_wit_1_rp_eq_bp : mpn_add_n_return_wit_1_rp_eq_bp.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  try rewrite (sublist_self l_a n_pre) in PreH8 by lia.
  try rewrite (sublist_self l_b n_pre) in PreH9 by lia.
  try rewrite PreH21 in PreH8.
  try rewrite PreH22 in PreH9.
  assert (Ha_prefix: val_a_prefix = val_a_rp_eq_bp).
  {
    rewrite <- PreH8.
    rewrite (sublist_self l_a (Zlength l_r)) by lia.
    exact PreH21.
  }
  assert (Hb_prefix: val_b_prefix = val_b_rp_eq_bp).
  {
    rewrite <- PreH9.
    rewrite (sublist_self l_b (Zlength l_r)) by lia.
    exact PreH22.
  }
  assert (Hval: val_r + cy * UINT_MOD ^ n_pre = val_a_rp_eq_bp + val_b_rp_eq_bp).
  {
    rewrite <- H.
    rewrite PreH17.
    rewrite Ha_prefix, Hb_prefix.
    reflexivity.
  }
  unfold mpd_store_Z, mpd_store_list.
  Exists val_r.
  rewrite Zsublist_nil by lia.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_a) with n_pre by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l_r (@nil Z)).
  rewrite app_nil_r.
  sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_r).
  2: lia.
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists l_a l_r.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_a) with n_pre by lia.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_return_wit_2_rp_eq_ap : mpn_add_n_return_wit_2_rp_eq_ap.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  try rewrite (sublist_self l_a n_pre) in PreH8 by lia.
  try rewrite (sublist_self l_b n_pre) in PreH9 by lia.
  try rewrite PreH21 in PreH8.
  try rewrite PreH22 in PreH9.
  assert (Ha_prefix: val_a_prefix = val_a_rp_eq_ap).
  {
    rewrite <- PreH8.
    rewrite (sublist_self l_a (Zlength l_r)) by lia.
    exact PreH21.
  }
  assert (Hb_prefix: val_b_prefix = val_b_rp_eq_ap).
  {
    rewrite <- PreH9.
    rewrite (sublist_self l_b (Zlength l_r)) by lia.
    exact PreH22.
  }
  assert (Hval: val_r + cy * UINT_MOD ^ n_pre = val_a_rp_eq_ap + val_b_rp_eq_ap).
  {
    rewrite <- H.
    rewrite PreH17.
    rewrite Ha_prefix, Hb_prefix.
    reflexivity.
  }
  unfold mpd_store_Z, mpd_store_list.
  Exists val_r.
  rewrite Zsublist_nil by lia.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_a) with n_pre by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l_r (@nil Z)).
  rewrite app_nil_r.
  sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_r).
  2: lia.
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists l_r l_b.
  replace (Zlength l_r) with n_pre by lia.
  replace (Zlength l_b) with n_pre by lia.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_which_implies_wit_2 : mpn_add_n_which_implies_wit_2.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_which_implies_wit_3 : mpn_add_n_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Intros.
  prop_apply (UIntArray.full_Zlength ap n l_a).
  Intros.
  sep_apply (UIntArray.full_split_to_seg ap 0 n l_a).
  2: lia.
  rewrite Zsublist_nil by lia.
  replace n with (Zlength l_a) by lia.
  rewrite (sublist_self l_a (Zlength l_a)) by lia.
  sep_apply (UIntArray.seg_merge_to_seg ap 0 0 (Zlength l_a) (@nil Z) l_a).
  2: lia.
  simpl.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_which_implies_wit_4 : mpn_add_n_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Intros.
  prop_apply (UIntArray.full_Zlength bp n l_b).
  Intros.
  sep_apply (UIntArray.full_split_to_seg bp 0 n l_b).
  2: lia.
  rewrite Zsublist_nil by lia.
  replace n with (Zlength l_a) by lia.
  rewrite (sublist_self l_b (Zlength l_a)) by lia.
  sep_apply (UIntArray.seg_merge_to_seg bp 0 0 (Zlength l_a) (@nil Z) l_b).
  2: lia.
  simpl.
  entailer!.
Qed.
