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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_sub_1_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_sub_1_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_sub_1_entail_wit_3_1_non_alias : mpn_sub_1_entail_wit_3_1_non_alias.
Proof.
  unfold mpn_sub_1_entail_wit_3_1_non_alias.
  left.
  intros n_pre ap_pre rp_pre b0_non_alias val_non_alias l val2_2 val1_2 l'_2 b i
    Hge Hi Hile Hile_n Hb_nonneg Hb_le Hneq Hn Hlen_l'
    Hval_sub Hval_l' Hbound_l' Hbound_l Hlen_l Hval_l Hrec.
  set (new := Znth i l 0 - b).
  Exists (list_to_Z UINT_MOD (l'_2 ++ new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (l'_2 ++ new :: nil).
  Intros.
  assert (Hz_bound: 0 <= Znth i l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound_l; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. unfold UINT_MOD in *. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Happend_bound: list_within_bound UINT_MOD (l'_2 ++ new :: nil)).
  { apply list_within_bound_concat; try exact Hbound_l'. exact Hsingle_bound. }
  assert (Hlen_app: Zlength (l'_2 ++ new :: nil) = i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hval_app:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) = val2_2 + new * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat UINT_MOD ltac:(unfold UINT_MOD; lia)); try tauto.
    rewrite Hlen_l'.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite Hval_l'.
    ring.
  }
  assert (Hsub_val:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) = val1_2 + Znth i l 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l i).
    - rewrite Hval_sub. nia.
    - lia.
    - exact Hbound_l.
  }
  assert (Hmain:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) - 0 * UINT_MOD ^ (i + 1) =
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) - b0_non_alias).
  {
    rewrite Hval_app, Hsub_val.
    subst new.
    replace (val2_2 + (Znth i l 0 - b) * UINT_MOD ^ i)
      with ((val2_2 - b * UINT_MOD ^ i) + Znth i l 0 * UINT_MOD ^ i) by ring.
    rewrite Hrec.
    ring.
  }
  split_pure_spatial.
  - entailer!.
  - Intros. entailer!.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_2_non_alias : mpn_sub_1_entail_wit_3_2_non_alias.
Proof.
  unfold mpn_sub_1_entail_wit_3_2_non_alias.
  left.
  intros n_pre ap_pre rp_pre b0_non_alias val_non_alias l val2_2 val1_2 l'_2 b i
    Hlt Hi Hile Hile_n Hb_nonneg Hb_le Hneq Hn Hlen_l'
    Hval_sub Hval_l' Hbound_l' Hbound_l Hlen_l Hval_l Hrec.
  set (new := unsigned_last_nbits (Znth i l 0 - b) 32).
  Exists (list_to_Z UINT_MOD (l'_2 ++ new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (l'_2 ++ new :: nil).
  Intros.
  assert (Hz_bound: 0 <= Znth i l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound_l; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Happend_bound: list_within_bound UINT_MOD (l'_2 ++ new :: nil)).
  { apply list_within_bound_concat; try exact Hbound_l'. exact Hsingle_bound. }
  assert (Hlen_app: Zlength (l'_2 ++ new :: nil) = i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hval_app:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) = val2_2 + new * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat UINT_MOD ltac:(unfold UINT_MOD; lia));
      try exact Hbound_l'; try exact Hsingle_bound.
    rewrite Hlen_l'. rewrite list_to_Z_cons, list_to_Z_nil. rewrite Hval_l'. ring.
  }
  assert (Hsub_val:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) = val1_2 + Znth i l 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l i).
    - rewrite Hval_sub. nia.
    - lia.
    - exact Hbound_l.
  }
  assert (Hborrow: new - UINT_MOD = Znth i l 0 - b).
  {
    subst new. unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    replace (Znth i l 0 - b) with (-(b - Znth i l 0)) by ring.
    rewrite Z_mod_nz_opp_full.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). ring.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). lia.
  }
  assert (Hmain:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) - 1 * UINT_MOD ^ (i + 1) =
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) - b0_non_alias).
  {
    rewrite Hval_app, Hsub_val.
    replace (UINT_MOD ^ (i + 1)) with (UINT_MOD * UINT_MOD ^ i).
    2:{ rewrite Z.pow_add_r; unfold UINT_MOD; try lia; ring. }
    replace (val2_2 + new * UINT_MOD ^ i - 1 * (UINT_MOD * UINT_MOD ^ i))
      with (val2_2 + (new - UINT_MOD) * UINT_MOD ^ i) by ring.
    rewrite Hborrow.
    replace (val2_2 + (Znth i l 0 - b) * UINT_MOD ^ i)
      with ((val2_2 - b * UINT_MOD ^ i) + Znth i l 0 * UINT_MOD ^ i) by ring.
    rewrite Hrec.
    ring.
  }
  split_pure_spatial.
  - entailer!.
  - Intros. entailer!.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_4_1_rp_eq_ap : mpn_sub_1_entail_wit_4_1_rp_eq_ap.
Proof.
  unfold mpn_sub_1_entail_wit_4_1_rp_eq_ap.
  left.
  intros n_pre ap_pre rp_pre b0_rp_eq_ap val_rp_eq_ap l val2_2 val1_2 l'_2 b i
    Heq0 Hge Heq1 Hi Hile Hile_n Hb_nonneg Hb_le Heq2 Hn
    Hlen_l' Hval_sub Hval_l' Hbound_l' Hbound_l Hlen_l Hval_l Hrec.
  set (new := Znth (i - i) (sublist i (Zlength l) l) 0 - b).
  Exists (list_to_Z UINT_MOD (l'_2 ++ new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (l'_2 ++ new :: nil).
  Intros.
  assert (Hsub_i: Znth (i - i) (sublist i (Zlength l) l) 0 = Znth i l 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hz_bound: 0 <= Znth i l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound_l; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. rewrite Hsub_i. unfold UINT_MOD in *. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Happend_bound: list_within_bound UINT_MOD (l'_2 ++ new :: nil)).
  { apply list_within_bound_concat; try exact Hbound_l'. exact Hsingle_bound. }
  assert (Hlen_app: Zlength (l'_2 ++ new :: nil) = i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hval_app:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) = val2_2 + new * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat UINT_MOD ltac:(unfold UINT_MOD; lia));
      try exact Hbound_l'; try exact Hsingle_bound.
    rewrite Hlen_l'. rewrite list_to_Z_cons, list_to_Z_nil. rewrite Hval_l'. ring.
  }
  assert (Hsub_val:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) = val1_2 + Znth i l 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l i).
    - rewrite Hval_sub. nia.
    - lia.
    - exact Hbound_l.
  }
  assert (Hmain:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) - 0 * UINT_MOD ^ (i + 1) =
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) - b0_rp_eq_ap).
  {
    rewrite Hval_app, Hsub_val.
    subst new.
    rewrite Hsub_i.
    replace (val2_2 + (Znth i l 0 - b) * UINT_MOD ^ i)
      with ((val2_2 - b * UINT_MOD ^ i) + Znth i l 0 * UINT_MOD ^ i) by ring.
    rewrite Hrec.
    ring.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) new (sublist i (Zlength l) l) =
    new :: sublist (i + 1) (Zlength l) l).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  change (replace_Znth (i - i)
            (Znth (i - i) (sublist i (Zlength l) l) 0 - b)
            (sublist i (Zlength l) l))
    with (replace_Znth (i - i) new (sublist i (Zlength l) l)).
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l)
      (new :: sublist (i + 1) (Zlength l) l)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l - i = Zlength (new :: sublist (i + 1) (Zlength l) l)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l'_2 (new :: nil)).
    entailer!.
    entailer!.
  - Intros.
    entailer!.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_4_2_rp_eq_ap : mpn_sub_1_entail_wit_4_2_rp_eq_ap.
Proof.
  unfold mpn_sub_1_entail_wit_4_2_rp_eq_ap.
  left.
  intros n_pre ap_pre rp_pre b0_rp_eq_ap val_rp_eq_ap l val2_2 val1_2 l'_2 b i
    Heq0 Hlt Heq1 Hi Hile Hile_n Hb_nonneg Hb_le Heq2 Hn
    Hlen_l' Hval_sub Hval_l' Hbound_l' Hbound_l Hlen_l Hval_l Hrec.
  set (new := unsigned_last_nbits (Znth (i - i) (sublist i (Zlength l) l) 0 - b) 32).
  Exists (list_to_Z UINT_MOD (l'_2 ++ new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (l'_2 ++ new :: nil).
  Intros.
  assert (Hsub_i: Znth (i - i) (sublist i (Zlength l) l) 0 = Znth i l 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hz_bound: 0 <= Znth i l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound_l; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Happend_bound: list_within_bound UINT_MOD (l'_2 ++ new :: nil)).
  { apply list_within_bound_concat; try exact Hbound_l'. exact Hsingle_bound. }
  assert (Hlen_app: Zlength (l'_2 ++ new :: nil) = i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hval_app:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) = val2_2 + new * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat UINT_MOD ltac:(unfold UINT_MOD; lia));
      try exact Hbound_l'; try exact Hsingle_bound.
    rewrite Hlen_l'. rewrite list_to_Z_cons, list_to_Z_nil. rewrite Hval_l'. ring.
  }
  assert (Hsub_val:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) = val1_2 + Znth i l 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD ltac:(unfold UINT_MOD; lia) l i).
    - rewrite Hval_sub. nia.
    - lia.
    - exact Hbound_l.
  }
  assert (Hborrow: new - UINT_MOD = Znth i l 0 - b).
  {
    subst new. unfold unsigned_last_nbits.
    rewrite Hsub_i.
    change (2 ^ 32) with UINT_MOD.
    replace (Znth i l 0 - b) with (-(b - Znth i l 0)) by ring.
    rewrite Z_mod_nz_opp_full.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). ring.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). lia.
  }
  assert (Hmain:
    list_to_Z UINT_MOD (l'_2 ++ new :: nil) - 1 * UINT_MOD ^ (i + 1) =
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) - b0_rp_eq_ap).
  {
    rewrite Hval_app, Hsub_val.
    replace (UINT_MOD ^ (i + 1)) with (UINT_MOD * UINT_MOD ^ i).
    2:{ rewrite Z.pow_add_r; unfold UINT_MOD; try lia; ring. }
    replace (val2_2 + new * UINT_MOD ^ i - 1 * (UINT_MOD * UINT_MOD ^ i))
      with (val2_2 + (new - UINT_MOD) * UINT_MOD ^ i) by ring.
    rewrite Hborrow.
    replace (val2_2 + (Znth i l 0 - b) * UINT_MOD ^ i)
      with ((val2_2 - b * UINT_MOD ^ i) + Znth i l 0 * UINT_MOD ^ i) by ring.
    rewrite Hrec.
    ring.
  }
  assert (Hreplace_tail:
    replace_Znth (i - i) new (sublist i (Zlength l) l) =
    new :: sublist (i + 1) (Zlength l) l).
  {
    replace (i - i) with 0 by lia.
    apply replace_Znth_sublist_head.
    split; [lia | split; [lia | lia]].
  }
  change (replace_Znth (i - i)
            (unsigned_last_nbits (Znth (i - i) (sublist i (Zlength l) l) 0 - b) 32)
            (sublist i (Zlength l) l))
    with (replace_Znth (i - i) new (sublist i (Zlength l) l)).
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i (i + 1) (Zlength l)
      (new :: sublist (i + 1) (Zlength l) l)).
    entailer!.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l - i = Zlength (new :: sublist (i + 1) (Zlength l) l)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l'_2 (new :: nil)).
    entailer!.
    entailer!.
  - Intros.
    entailer!.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_5_1_non_alias : mpn_sub_1_entail_wit_5_1_non_alias.
Proof.
  pre_process.
  subst i.
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (list_to_Z UINT_MOD ((Znth 0 l 0 - b0_non_alias) :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists ((Znth 0 l 0 - b0_non_alias) :: nil).
  entailer!; unfold UINT_MOD in *; simpl; try lia.
  replace (0 + 1) with 1 by lia.
  entailer!.
  rewrite (sublist_single 0); try lia.
  rewrite !list_to_Z_cons, !list_to_Z_nil.
  ring.
  pose proof (list_within_bound_Znth_bound 4294967296 l 0 ltac:(lia) PreH9) as Hz.
  split; [lia | tauto].
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_5_2_non_alias : mpn_sub_1_entail_wit_5_2_non_alias.
Proof.
  pre_process.
  subst i.
  sep_apply UIntArray.seg_single.
  sep_apply UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (list_to_Z UINT_MOD (unsigned_last_nbits (Znth 0 l 0 - b0_non_alias) 32 :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (unsigned_last_nbits (Znth 0 l 0 - b0_non_alias) 32 :: nil).
  entailer!; unfold UINT_MOD in *; simpl;
    pose proof (unsigned_Lastnbits_range (Znth 0 l 0 - b0_non_alias) 32); try lia.
  replace (0 + 1) with 1 by lia.
  entailer!.
  rewrite (sublist_single 0); try lia.
  rewrite !list_to_Z_cons, !list_to_Z_nil.
  unfold unsigned_last_nbits.
  replace (2 ^ 32) with 4294967296 in * by reflexivity.
  replace (Znth 0 l 0 - b0_non_alias)
    with (-(b0_non_alias - Znth 0 l 0)) by ring.
  pose proof (list_within_bound_Znth_bound 4294967296 l 0 ltac:(lia) PreH9) as Hz.
  rewrite Z_mod_nz_opp_full.
  - rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_6_1_rp_eq_ap : mpn_sub_1_entail_wit_6_1_rp_eq_ap.
Proof.
  pre_process.
  subst i.
  set (new := Znth 0 l 0 - b0_rp_eq_ap).
  Exists (list_to_Z UINT_MOD (new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (new :: nil).
  assert (Hsub_0: Znth (0 - 0) (sublist 0 (Zlength l) l) 0 = Znth 0 l 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hz_bound: 0 <= Znth 0 l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l 0); try exact PreH11; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. unfold UINT_MOD in *. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Hval_single: list_to_Z UINT_MOD (new :: nil) = new).
  { rewrite list_to_Z_cons, list_to_Z_nil. ring. }
  assert (Hsub_val: list_to_Z UINT_MOD (sublist 0 1 l) = Znth 0 l 0).
  { rewrite (sublist_single 0); try lia. rewrite list_to_Z_cons, list_to_Z_nil. ring. }
  assert (Hmain:
    list_to_Z UINT_MOD (new :: nil) - 0 * UINT_MOD ^ (0 + 1) =
    list_to_Z UINT_MOD (sublist 0 1 l) - b0_rp_eq_ap).
  { rewrite Hval_single, Hsub_val. subst new. ring. }
  assert (Hreplace_tail:
    replace_Znth 0 new (sublist 0 (Zlength l) l) =
    new :: sublist 1 (Zlength l) l).
  { apply replace_Znth_sublist_head. split; [lia | split; [lia | lia]]. }
  rewrite Hsub_0.
  change (replace_Znth (0 - 0)
            (Znth 0 l 0 - b0_rp_eq_ap)
            (sublist 0 (Zlength l) l))
    with (replace_Znth 0 new (sublist 0 (Zlength l) l)).
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre 0 1 (Zlength l)
      (new :: sublist 1 (Zlength l) l)).
    entailer!.
    replace (1 - 0) with 1 by lia.
    assert (Hlen_cons:
      Zlength l = Zlength (new :: sublist 1 (Zlength l) l)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite sublist_cons_head.
    replace (sublist 1 (Zlength l) (new :: sublist 1 (Zlength l) l))
      with (sublist 1 (Zlength (new :: sublist 1 (Zlength l) l))
        (new :: sublist 1 (Zlength l) l))
      by (rewrite <- Hlen_cons; reflexivity).
    replace (Zlength l - 0) with (Zlength (new :: sublist 1 (Zlength l) l))
      by (rewrite <- Hlen_cons; lia).
    rewrite sublist_cons_tail_all.
    replace (0 + 1) with 1 by lia.
    entailer!.
    rewrite UIntArray.seg_empty.
    entailer!.
  - Intros.
    entailer!.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_6_2_rp_eq_ap : mpn_sub_1_entail_wit_6_2_rp_eq_ap.
Proof.
  pre_process.
  subst i.
  set (new := unsigned_last_nbits (Znth 0 l 0 - b0_rp_eq_ap) 32).
  Exists (list_to_Z UINT_MOD (new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (new :: nil).
  assert (Hsub_0: Znth (0 - 0) (sublist 0 (Zlength l) l) 0 = Znth 0 l 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hz_bound: 0 <= Znth 0 l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l 0); try exact PreH11; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Hval_single: list_to_Z UINT_MOD (new :: nil) = new).
  { rewrite list_to_Z_cons, list_to_Z_nil. ring. }
  assert (Hsub_val: list_to_Z UINT_MOD (sublist 0 1 l) = Znth 0 l 0).
  { rewrite (sublist_single 0); try lia. rewrite list_to_Z_cons, list_to_Z_nil. ring. }
  assert (Hborrow: new - UINT_MOD = Znth 0 l 0 - b0_rp_eq_ap).
  {
    subst new.
    unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    replace (Znth 0 l 0 - b0_rp_eq_ap)
      with (-(b0_rp_eq_ap - Znth 0 l 0)) by ring.
    rewrite Z_mod_nz_opp_full.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). ring.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). lia.
  }
  assert (Hmain:
    list_to_Z UINT_MOD (new :: nil) - 1 * UINT_MOD ^ (0 + 1) =
    list_to_Z UINT_MOD (sublist 0 1 l) - b0_rp_eq_ap).
  {
    rewrite Hval_single, Hsub_val.
    replace (UINT_MOD ^ (0 + 1)) with UINT_MOD by (unfold UINT_MOD; reflexivity).
    nia.
  }
  assert (Hreplace_tail:
    replace_Znth 0 new (sublist 0 (Zlength l) l) =
    new :: sublist 1 (Zlength l) l).
  { apply replace_Znth_sublist_head. split; [lia | split; [lia | lia]]. }
  rewrite Hsub_0.
  change (replace_Znth (0 - 0)
            (unsigned_last_nbits (Znth 0 l 0 - b0_rp_eq_ap) 32)
            (sublist 0 (Zlength l) l))
    with (replace_Znth 0 new (sublist 0 (Zlength l) l)).
  rewrite Hreplace_tail.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre 0 1 (Zlength l)
      (new :: sublist 1 (Zlength l) l)).
    entailer!.
    replace (1 - 0) with 1 by lia.
    assert (Hlen_cons:
      Zlength l = Zlength (new :: sublist 1 (Zlength l) l)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite sublist_cons_head.
    replace (sublist 1 (Zlength l) (new :: sublist 1 (Zlength l) l))
      with (sublist 1 (Zlength (new :: sublist 1 (Zlength l) l))
        (new :: sublist 1 (Zlength l) l))
      by (rewrite <- Hlen_cons; reflexivity).
    replace (Zlength l - 0) with (Zlength (new :: sublist 1 (Zlength l) l))
      by (rewrite <- Hlen_cons; lia).
    rewrite sublist_cons_tail_all.
    replace (0 + 1) with 1 by lia.
    entailer!.
    rewrite UIntArray.seg_empty.
    entailer!.
  - Intros.
    entailer!.
Qed.

Lemma proof_of_mpn_sub_1_return_wit_1_non_alias : mpn_sub_1_return_wit_1_non_alias.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists val2.
  rewrite Hi.
  rewrite UIntArray.undef_seg_empty.
  unfold mpd_store_Z, mpd_store_list.
  Exists l l'.
  split_pure_spatial.
  - sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l').
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    entailer!.
    rewrite Hi.
    rewrite PreH13.
    entailer!.
  - rewrite Hi in PreH9.
    rewrite (sublist_self l n_pre) in PreH9 by lia.
    rewrite PreH14 in PreH9.
    rewrite Hi in PreH15.
    entailer!.
Qed.

Lemma proof_of_mpn_sub_1_return_wit_2_rp_eq_ap : mpn_sub_1_return_wit_2_rp_eq_ap.
Proof.
  unfold mpn_sub_1_return_wit_2_rp_eq_ap.
  right.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists val2.
  split_pure_spatial.
  - rewrite Zsublist_nil by lia.
    replace (Zlength l') with n_pre by lia.
    replace (Zlength l) with n_pre by lia.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l' (@nil Z)).
    rewrite app_nil_r.
    sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l').
    unfold mpd_store_Z, mpd_store_list.
    Exists l'.
    entailer!.
    replace (Zlength l') with n_pre by lia.
    entailer!.
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    entailer!.
    lia.
  - Intros.
    rewrite Hi in PreH9, PreH15.
    rewrite (sublist_self l n_pre) in PreH9 by lia.
    rewrite PreH14 in PreH9.
    entailer!.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_1 : mpn_sub_1_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_2 : mpn_sub_1_which_implies_wit_2.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_3 : mpn_sub_1_which_implies_wit_3.
Proof.
  unfold mpn_sub_1_which_implies_wit_3.
  left.
  intros l n ap PreH1.
  Intros.
  prop_apply (UIntArray.full_Zlength ap n l).
  Intros.
  sep_apply (UIntArray.full_split_to_seg ap 0 n l).
  2: lia.
  rewrite Zsublist_nil by lia.
  replace n with (Zlength l) by lia.
  rewrite (sublist_self l (Zlength l)) by lia.
  entailer!.
Qed.
