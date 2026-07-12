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

Lemma proof_of_mpn_add_1_entail_wit_2_1 : mpn_add_1_entail_wit_2_1.
Proof.
  pre_process.
  sep_apply UIntArray.seg_single.
  sep_apply UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with (rp_pre) by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (list_to_Z UINT_MOD (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil)).
  entailer! ; unfold UINT_MOD in * ; simpl ; pose proof (unsigned_Lastnbits_range (Znth 0 l 0 + b_pre) 32) ; try lia.
  unfold unsigned_last_nbits in *.
  replace (2 ^ 32) with 4294967296 in * by reflexivity.
  rewrite (sublist_single 0) ; try lia. simpl. 
  pose proof (Z_mod_add_uncarry (Znth 0 l 0) b_pre 4294967296
    ltac:(lia) ltac:(apply list_within_bound_Znth; try lia; auto) ltac:(lia) PreH1) as Hsum.
  rewrite <- Hsum.
  rewrite !list_to_Z_single.
  lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_2_2 : mpn_add_1_entail_wit_2_2.
Proof.
  pre_process.
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with (rp_pre) by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (list_to_Z UINT_MOD (unsigned_last_nbits (Znth 0 l 0 + b_pre) 32 :: nil)).
  entailer! ; unfold UINT_MOD in * ; simpl ; pose proof (unsigned_Lastnbits_range (Znth 0 l 0 + b_pre) 32) ; try lia.
  rewrite (sublist_single 0) ; try lia.
  simpl.
  unfold unsigned_last_nbits in *.
  replace (2 ^ 32) with 4294967296 in * by reflexivity.
  pose proof (Z_mod_add_carry (Znth 0 l 0) b_pre 4294967296
    ltac:(lia) ltac:(apply list_within_bound_Znth; try lia; auto) ltac:(lia) PreH1) as Hsum.
  rewrite !list_to_Z_single.
  rewrite <- Hsum.
  lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_1 : mpn_add_1_entail_wit_1_1.
Proof.
  pre_process.
  Exists (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (list_to_Z UINT_MOD (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)).
  pose proof (unsigned_Lastnbits_range (Znth i l 0 + b) 32 ltac:(lia)) as Hrange.
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)) by (simpl ; unfold UINT_MOD in * ; lia).
  entailer! ; unfold UINT_MOD in * ;  try lia.
  - apply list_within_bound_concat ; try tauto.
  - rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil.
    lia.
  - rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH10. simpl list_to_Z.
    rewrite PreH8.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    + rewrite PreH9. simpl list_to_Z.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia.
      unfold unsigned_last_nbits.
      replace (2 ^ 32) with 4294967296 in * by reflexivity.
      pose proof (Z_mod_add_uncarry (Znth i l 0) b 4294967296
        ltac:(lia) ltac:(apply list_within_bound_Znth; try lia; auto)
        ltac:(lia) PreH1) as Hsum.
      rewrite <- Hsum.
      rewrite !list_to_Z_single.
      lia.
    + apply list_within_bound_sublist ; try lia ; try tauto.
    + simpl. split ; try tauto. apply list_within_bound_Znth ; try lia. auto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2 : mpn_add_1_entail_wit_1_2.
Proof.
  pre_process.
  Exists (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 (i + 1) l)).
  Exists (list_to_Z UINT_MOD (l'_2 ++ unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)).
  pose proof (unsigned_Lastnbits_range (Znth i l 0 + b) 32 ltac:(lia)) as Hrange.
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (Znth i l 0 + b) 32
:: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  entailer! ; unfold UINT_MOD in * ;  try lia.
  - apply list_within_bound_concat ; try tauto.
  - rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil.
    lia.
  - rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH10. simpl list_to_Z.
    rewrite PreH8.
    rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    + rewrite PreH9. simpl list_to_Z.
      rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia.
      unfold unsigned_last_nbits.
      replace (2 ^ 32) with 4294967296 in * by reflexivity.
      pose proof (Z_mod_add_carry (Znth i l 0) b 4294967296
        ltac:(lia) ltac:(apply list_within_bound_Znth; try lia; auto)
        ltac:(lia) PreH1) as Hsum.
      rewrite Z.pow_add_r by lia.
      replace (4294967296 ^ 1) with 4294967296 by reflexivity.
      rewrite !list_to_Z_single.
      assert (Hmod: (Znth i l 0 + b) mod 4294967296 =
                    Znth i l 0 + b - 4294967296) by lia.
      rewrite Hmod.
      lia.
    + apply list_within_bound_sublist ; try lia ; try tauto.
    + simpl. split ; try tauto. apply list_within_bound_Znth ; try lia. auto.
Qed.

Lemma proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  assert (Hlen_done : i = n_pre) by lia. subst i.
  match goal with
  | Hlen : Zlength l' = n_pre |- _ => rewrite Hlen
  end.
  rewrite UIntArray.undef_seg_empty.
  rewrite Hlen_done in PreH8.
  rewrite sublist_self in PreH8 by lia.
  assert (val = val1) by lia. subst val1.
  Exists val2.
  Exists l l'.
  match goal with
  | Hval2 : list_to_Z _ l' = val2 |- _ => rewrite Hval2
  end.
  match goal with
  | Hlen : Zlength l' = n_pre |- _ => rewrite Hlen
  end.
  rewrite PreH11.
  entailer!. 
  rewrite Hlen_done in PreH6.
  lia.
Qed.

Lemma proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Proof. 
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Proof. 
  pre_process.
  Exists 0 nil.
  Exists 0 0.
  entailer!.
  sep_apply UIntArray.undef_full_to_undef_seg.
  rewrite UIntArray.full_empty.
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_2 : mpn_add_n_entail_wit_2_2.
Proof.
  pre_process.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
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
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  entailer! ; unfold UINT_MOD in *.
  + try rewrite PreH10; try rewrite PreH12.
    rewrite Z.pow_add_r by lia.
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_uncarry (Znth i l_a 0) cy 4294967296
      ltac:(lia) ltac:(lia) ltac:(lia) PreH2) as Hinner_sum.
    pose proof (Z_mod_add_carry ((Znth i l_a 0 + cy) mod 4294967296)
      (Znth i l_b 0) 4294967296 ltac:(lia) ltac:(lia) ltac:(lia) PreH1)
      as Houter_sum.
    lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    rewrite list_to_Z_single. lia.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_1 : mpn_add_n_entail_wit_2_1.
Proof. 
  pre_process.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
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
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  entailer! ; unfold UINT_MOD in *.
  + try rewrite PreH10; try rewrite PreH12.
    rewrite Z.pow_add_r by lia.
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_uncarry (Znth i l_a 0) cy 4294967296
      ltac:(lia) ltac:(lia) ltac:(lia) PreH2) as Hinner_sum.
    pose proof (Z_mod_add_uncarry ((Znth i l_a 0 + cy) mod 4294967296)
      (Znth i l_b 0) 4294967296 ltac:(lia) ltac:(lia) ltac:(lia) PreH1)
      as Houter_sum.
    lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    rewrite list_to_Z_single. lia.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_4 : mpn_add_n_entail_wit_2_4.
Proof.
  pre_process.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
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
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  entailer! ; unfold UINT_MOD in *.
  + try rewrite PreH10; try rewrite PreH12.
    rewrite Z.pow_add_r by lia.
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_carry (Znth i l_a 0) cy 4294967296
      ltac:(lia) ltac:(lia) ltac:(lia) PreH2) as Hinner_sum.
    pose proof (Z_mod_add_carry ((Znth i l_a 0 + cy) mod 4294967296)
      (Znth i l_b 0) 4294967296 ltac:(lia) ltac:(lia) ltac:(lia) PreH1)
      as Houter_sum.
    lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    rewrite list_to_Z_single. lia.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_3 : mpn_add_n_entail_wit_2_3.
Proof. 
  pre_process.
  Exists (val_r_2 + unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 * 4294967296 ^ Zlength l_r_2).
  Exists (l_r_2 ++ unsigned_last_nbits (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil).
  Exists (val_b_prefix_2 + Znth i l_b 0 * 4294967296 ^ i) (val_a_prefix_2 + Znth i l_a 0 * 4294967296 ^ i).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
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
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  entailer! ; unfold UINT_MOD in *.
  + try rewrite PreH10; try rewrite PreH12.
    rewrite Z.pow_add_r by lia.
    replace (4294967296 ^ 1) with 4294967296 by reflexivity.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_carry (Znth i l_a 0) cy 4294967296
      ltac:(lia) ltac:(lia) ltac:(lia) PreH2) as Hinner_sum.
    pose proof (Z_mod_add_uncarry ((Znth i l_a 0 + cy) mod 4294967296)
      (Znth i l_b 0) 4294967296 ltac:(lia) ltac:(lia) ltac:(lia) PreH1)
      as Houter_sum.
    lia.
  + rewrite Zlength_app ; rewrite Zlength_cons ; rewrite Zlength_nil ; lia.
  + apply list_within_bound_concat ; try tauto.
  + rewrite list_to_Z_concat ; try lia ; try tauto. 
    rewrite list_to_Z_single. lia.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_b) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto.
  + rewrite (sublist_split 0 (i + 1) i) ; try lia.
    rewrite (sublist_single 0 i l_a) ; try lia.
    rewrite list_to_Z_concat ; try lia ; try tauto.
    - rewrite list_to_Z_single. rewrite Zlength_sublist ; try lia.
      replace (i - 0) with i by lia. lia.
    - apply list_within_bound_sublist ; try lia ; try tauto.
    - simpl. split ; try tauto. 
Qed.

Lemma proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Proof.
  pre_process.
  assert (Hdone : i = n_pre) by lia. subst i.
  unfold mpd_store_Z , mpd_store_list.
  rewrite Hdone.
  rewrite UIntArray.undef_seg_empty.
  rewrite sublist_self in PreH6 by lia.
  rewrite sublist_self in PreH7 by lia.
  Exists val_r.
  Exists l_a l_b l_r.
  rewrite PreH8, PreH12, PreH13, Hdone.
  entailer!. 
  rewrite Hdone in PreH11.
  lia.
Qed.

Lemma proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0 , <- H2.
  entailer!.
Qed.

Lemma proof_of_mpn_add_return_wit_1 : mpn_add_return_wit_1.
Proof.
  pre_process.
  Exists (val_r_out_2 + val' * UINT_MOD ^ bn_pre).
  unfold mpd_store_Z , mpd_store_list.
  Intros la' lr' la lb.
  destruct H as [Hla'_val Hla'_bound].
  destruct H1 as [Hlr'_val Hlr'_bound].
  destruct H3 as [Hla_val Hla_bound].
  destruct H5 as [Hlb_val Hlb_bound].
  Exists (la ++ la') lb (l_r ++ lr').
  rewrite <- H6, <- H4, <- H2, <- H0.
  sep_apply (UIntArray.full_merge_to_full rp_pre) ; try lia.
  sep_apply (UIntArray.full_merge_to_full ap_pre) ; try lia.
  repeat rewrite Zlength_app.
  try rewrite PreH9.
  try rewrite <- H6; try rewrite <- H4; try rewrite <- H2; try rewrite <- H0.
  replace (bn_pre + (an_pre - bn_pre)) with an_pre by lia.
  entailer!.
  all : try apply list_within_bound_concat ; try tauto.
  all : unfold UINT_MOD in *.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite PreH10, Hlr'_val.
    rewrite PreH9.
    lia.
  + rewrite list_to_Z_concat ; try lia ; try tauto.
    rewrite Hla_val, Hla'_val.
    rewrite <- H4.
    lia.
  + replace (an_pre) with (bn_pre + (an_pre - bn_pre)) by lia.
    rewrite Z.pow_add_r by lia.
    replace (UINT_MOD ^ (an_pre - bn_pre) * UINT_MOD ^ bn_pre)
      with (UINT_MOD ^ bn_pre * UINT_MOD ^ (an_pre - bn_pre)) by ring.
    nia.
Qed.

Lemma proof_of_mpn_add_return_wit_2 : mpn_add_return_wit_2.
Proof. 
  pre_process.
  assert (an_pre = bn_pre) by lia. subst an_pre.
  Exists val_r_out_2.
  unfold mpd_store_Z , mpd_store_list.
  Intros la lb lr.
  destruct H as [Hla_val Hla_bound].
  destruct H1 as [Hlb_val Hlb_bound].
  destruct H3 as [Hlr_val Hlr_bound].
  Exists la lb l_r.
  replace (bn_pre - bn_pre) with 0 in * by lia.
  symmetry in H4.
  apply Zlength_nil_inv in H4.
  subst lr. simpl in Hlr_val.
  subst val_a_high.
  simpl in PreH12.
  replace (val_a_low + 0 * UINT_MOD ^ bn_pre) with val_a_low in PreH12 by lia.
  subst val_a.
  rewrite UIntArray.full_empty.
  rewrite Zlength_nil.
  rewrite UIntArray.undef_full_empty.
  rewrite <- H0, <- H2.
  rewrite PreH9, PreH8.
  entailer!.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l.
  destruct H as [Hval Hbound].
  pose proof H0 as Hlen.
  Exists (list_to_Z UINT_MOD (sublist bn an l)) (list_to_Z UINT_MOD (sublist 0 bn l)) .
  Exists (sublist 0 bn l) (sublist bn an l).
  rewrite Zlength_sublist ; try lia.
  sep_apply (UIntArray.full_split_to_full ap bn) ; try lia.
  rewrite <- Hlen.
  rewrite Zlength_sublist ; try lia.
  replace (bn - 0) with bn by lia.
  entailer!.
  all : try apply list_within_bound_sublist ; try lia ; try tauto.
  rewrite <- Hval.
  rewrite <- (sublist_self l an) at 1; try lia.
  rewrite (sublist_split 0 an bn) ; try lia.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat ; try lia.
  rewrite Zlength_sublist ; try lia.
  replace (bn - 0) with bn by lia.
  lia.
  all : apply list_within_bound_sublist ; try lia ; try tauto.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Proof.
  pre_process.
  apply UIntArray.undef_full_split_to_undef_full ; try lia.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_3 : mpn_add_which_implies_wit_3.
Proof.
  pre_process.
  unfold mpd_store_Z , mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_2_1 : mpn_sub_1_entail_wit_2_1.
Proof.
  pre_process.
  Exists ((Znth 0 l 0 - b_pre) :: nil).
  entailer!.
  - sep_apply_l_atomic (UIntArray.seg_single rp_pre 0 (Znth 0 l 0 - b_pre)).
    entailer!.
	  - rewrite !list_to_Z_single.
	    unfold sublist.
	    destruct l.
	    + simpl. rewrite Zlength_nil in PreH2. lia.
	    + simpl. unfold Znth. simpl. rewrite list_to_Z_single. lia.
  - unfold list_within_bound. simpl.
    unfold list_within_bound in PreH4.
    destruct l.
    + simpl. rewrite Zlength_nil in PreH2. lia.
    + simpl in PreH4. destruct PreH4 as [[Hd_ge Hd_lt] _].
      unfold UINT_MOD in *.
      unfold Znth in PreH1. simpl in PreH1.
      change (Znth 0 (z :: l) 0) with z.
      change (Znth 0 (z :: l) 0) with z in PreH1.
      split; [lia | exact I].
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_2_2 : mpn_sub_1_entail_wit_2_2.
Proof.
  pre_process.
  Exists ((unsigned_last_nbits (Znth 0 l 0 - b_pre) 32) :: nil).
  entailer!.
  - sep_apply_l_atomic (UIntArray.seg_single rp_pre 0 (unsigned_last_nbits (Znth 0 l 0 - b_pre) 32)).
    entailer!.
	  - rewrite !list_to_Z_single.
	    unfold sublist.
	    destruct l.
	    + simpl. rewrite Zlength_nil in PreH2. lia.
	    + simpl.
	      unfold Znth in *. simpl in *.
	      rewrite list_to_Z_single.
	      unfold unsigned_last_nbits, UINT_MOD in *.
      unfold list_within_bound in PreH4.
      simpl in PreH4.
      destruct PreH4 as [[Hz_ge Hz_lt] _].
      change (Znth 0 (z :: l) 0) with z in PreH1.
      assert (Hneg: z - b_pre < 0) by lia.
      assert (Hlow: - 4294967296 < z - b_pre) by lia.
      assert (Hmod_eq: (z - b_pre) mod 2^32 = z - b_pre + 4294967296).
      { symmetry.
        apply Z.mod_unique with (-1).
        left. lia.
        ring. }
      rewrite Hmod_eq.
      lia.
  - unfold list_within_bound. simpl.
    unfold unsigned_last_nbits, UINT_MOD.
    pose proof (Z.mod_pos_bound (Znth 0 l 0 - b_pre) (2^32)).
    lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_1 : mpn_sub_1_entail_wit_1_1.
Proof.
  pre_process.
  Exists (data_rp_partial_2 ++ (Znth i l 0 - b) :: nil).
  entailer!.
  - ring_simplify.
    pose proof (list_within_bound_Znth_bound UINT_MOD l i ltac:(lia) PreH9).
    assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (Znth i l 0 - b)).
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l i).
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    lia.
    + lia.
    + assumption.
    + unfold UINT_MOD in *.
      lia.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l i ltac:(lia) PreH9).
    apply list_within_bound_app_single.
    + assumption.
    + unfold UINT_MOD in *. lia.
  - rewrite Zlength_app.
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_2 : mpn_sub_1_entail_wit_1_2.
Proof.
  pre_process.
  Exists (data_rp_partial_2 ++ (unsigned_last_nbits (Znth i l 0 - b) 32) :: nil).
  entailer!.
  - rewrite Z.mul_1_l.
    pose proof (list_within_bound_Znth_bound UINT_MOD l i ltac:(unfold UINT_MOD; lia) PreH9).
    assert (Hb_is_1: b = 1) by (unfold UINT_MOD in *; lia).
    assert (HZnth0: Znth i l 0 = 0) by (unfold UINT_MOD in *; lia).
    subst b.
    rewrite HZnth0.
    unfold unsigned_last_nbits.
    replace ((0 - 1) mod 2^32) with (2^32 - 1) by reflexivity.
    assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
    assert (Hval_range: 0 <= 2^32 - 1 < UINT_MOD) by (unfold UINT_MOD; lia).
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (2^32 - 1) Hval_range).
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    assert (Hi_range: 0 <= i < Zlength l) by lia.
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l i Hi_range PreH9).
    rewrite HZnth0.
    unfold UINT_MOD in *.
    replace (4294967296 ^ (i + 1)) with (4294967296 * 4294967296 ^ i) by (rewrite Z.pow_add_r by lia; ring).
    assert (Heq: list_to_Z 4294967296 data_rp_partial_2 = list_to_Z 4294967296 (sublist 0 i l) - b_pre + 4294967296 ^ i) by lia.
    rewrite Heq.
    ring.
  - apply list_within_bound_app_single.
    + assumption.
    + unfold unsigned_last_nbits, UINT_MOD.
      pose proof (Z.mod_pos_bound (Znth i l 0 - b) (2^32) ltac:(lia)).
      lia.
  - rewrite Zlength_app.
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_1_return_wit_1 : mpn_sub_1_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq_n: i = n_pre) by lia.
  Exists (list_to_Z UINT_MOD data_rp_partial).
  unfold mpd_store_Z.
  Exists l.
  Exists data_rp_partial.
  unfold mpd_store_list.
  rewrite Hi_eq_n.
  rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
  entailer!.
  - rewrite PreH6.
    rewrite PreH7.
    rewrite Hi_eq_n.
    entailer!.
  - rewrite Hi_eq_n in PreH11.
    rewrite sublist_self in PreH11 by lia.
    rewrite PreH10 in PreH11.
    exact PreH11.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_1 : mpn_sub_1_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1 : mpn_sub_n_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  rewrite (UIntArray.full_empty rp_pre 0).
  entailer!.
  apply UIntArray.undef_full_to_undef_seg.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_2 : mpn_sub_n_entail_wit_2_2.
Proof.
  pre_process.
  Exists (data_rp_partial_2 ++ (unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32) :: nil).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  assert (Hnew_bound: 0 <= unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD.
    apply Z.mod_pos_bound; lia. }
  entailer!.
  - rewrite Z.mul_1_l.
    assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32) Hnew_bound).
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i ltac:(lia) PreH11).
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i ltac:(lia) PreH12).
    rewrite Hulb_eq.
    unfold unsigned_last_nbits, UINT_MOD in *.
    assert (Hdiff_neg: Znth i l_a 0 - (Znth i l_b 0 + cy) < 0).
    { rewrite Hulb_eq in PreH1. lia. }
    assert (Hdiff_bound: - 4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy)).
    { lia. }
    assert (Hmod_eq: (Znth i l_a 0 - (Znth i l_b 0 + cy)) mod 2^32 =
                     Znth i l_a 0 - (Znth i l_b 0 + cy) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1).
      { left. lia. }
      ring. }
    rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
  - apply list_within_bound_app_single.
    + assumption.
    + assumption.
  - rewrite Zlength_app.
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_1 : mpn_sub_n_entail_wit_2_1.
Proof.
  pre_process.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  Exists (data_rp_partial_2 ++ (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) :: nil).
  entailer!.
  - try rewrite Z.mul_0_l; try rewrite Z.sub_0_r.
    assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32)).
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i ltac:(lia) PreH11).
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i ltac:(lia) PreH12).
    rewrite Hulb_eq.
    lia.
    + rewrite Hulb_eq. unfold UINT_MOD in *. lia.
  - apply list_within_bound_app_single.
    + assumption.
    + rewrite Hulb_eq. unfold UINT_MOD in *. lia.
  - rewrite Zlength_app.
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_4 : mpn_sub_n_entail_wit_2_4.
Proof.
  pre_process.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso. assert (Hulb_eq: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy) by (apply Z.mod_small; lia). lia.
    - lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32). lia. lia. }
  assert (Hulb_range: 0 <= unsigned_last_nbits (Znth i l_b 0 + cy) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  assert (Hnew_bound: 0 <= unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  Exists (data_rp_partial_2 ++ (unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32) :: nil).
  entailer!.
  - replace (1 + 1) with 2 by lia.
    assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (unsigned_last_nbits (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32) Hnew_bound).
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i ltac:(lia) PreH11).
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i ltac:(lia) PreH12).
    rewrite Hulb_eq.
    rewrite Hulb_eq in Hulb_range.
    unfold unsigned_last_nbits, UINT_MOD in *.
    assert (Hdiff_neg: Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) < 0) by lia.
    assert (Hdiff_bound: - 4294967296 < Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) by lia.
    assert (Hmod_eq: (Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) mod 2^32 =
                     Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) + 4294967296).
    { symmetry. apply Z.mod_unique with (-1). left. lia. ring. }
    rewrite Hmod_eq.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
  - apply list_within_bound_app_single.
    + assumption.
    + assumption.
  - rewrite Zlength_app.
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_3 : mpn_sub_n_entail_wit_2_3.
Proof.
  pre_process.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso. assert (Hulb_eq: (Znth i l_b 0 + cy) mod 2^32 = Znth i l_b 0 + cy) by (apply Z.mod_small; lia). lia.
    - lia. }
  assert (Hulb_bp_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32). lia. lia. }
  Exists (data_rp_partial_2 ++ (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) :: nil).
  entailer!.
  - rewrite Z.mul_1_l.
    assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32)).
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i ltac:(lia) PreH11).
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i ltac:(lia) PreH12).
    rewrite Hulb_bp_eq.
    unfold UINT_MOD in *.
    replace (i + 1) with (Z.succ i) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
    + rewrite Hulb_bp_eq. lia.
  - apply list_within_bound_app_single.
    + assumption.
    + rewrite Hulb_bp_eq. unfold UINT_MOD in *. lia.
  - rewrite Zlength_app.
    match goal with
    | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
    end.
    rewrite Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_1 : mpn_sub_n_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq: i = n_pre) by lia.
  Exists (list_to_Z UINT_MOD data_rp_partial).
  unfold mpd_store_Z, mpd_store_list.
  Exists l_a.
  Exists l_b.
  Exists data_rp_partial.
  rewrite Hi_eq.
  rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
  entailer!.
  - rewrite PreH6. rewrite PreH7. rewrite PreH8. rewrite Hi_eq.
    entailer!.
  - rewrite Hi_eq in PreH14.
    rewrite (sublist_self l_a n_pre) in PreH14 by lia.
    rewrite (sublist_self l_b n_pre) in PreH14 by lia.
    rewrite PreH12, PreH13 in PreH14.
    exact PreH14.
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_1 : mpn_sub_n_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l_a.
  Intros l_b.
  Exists l_b.
  Exists l_a.
  rewrite <- H0. rewrite <- H2.
  entailer!.
Qed.

Lemma proof_of_mpn_sub_return_wit_2 : mpn_sub_return_wit_2.
Proof.
  pre_process.
  assert (Heq: an_pre = bn_pre) by lia. subst an_pre.
  Exists val_r.
  replace (bn_pre - bn_pre) with 0 by lia.
  sep_apply (mpd_store_Z_zero_to_emp (ap_pre + bn_pre * sizeof(UINT)) val_a_hi).
  Intros.
  assert (Hhi_zero: val_a_hi = 0) by lia.
  assert (Hval_eq: val_a = val_a_lo) by lia.
  subst val_a.
  sep_apply (UIntArray_full_to_mpd_store_Z_exact rp_pre bn_pre l_r val_r PreH8 PreH9 PreH10).
  rewrite UIntArray.undef_full_empty.
  entailer!.
  rewrite Hhi_zero.
  replace (val_a_lo + 0 * UINT_MOD ^ bn_pre) with val_a_lo by lia.
  entailer!.
Qed.

Lemma proof_of_mpn_sub_return_wit_1 : mpn_sub_return_wit_1.
Proof.
  pre_process.
  Exists (val_r + val' * UINT_MOD ^ bn_pre).
  unfold mpd_store_Z, mpd_store_list.
  Intros data_hi data_r_hi.
  Intros data_2 data_3.
  destruct H as [Hdata_hi_val Hdata_hi_bound].
  destruct H1 as [Hdata_r_hi_val Hdata_r_hi_bound].
  destruct H3 as [Hdata_lo_val Hdata_lo_bound].
  destruct H5 as [Hdata_b_val Hdata_b_bound].
  Exists (data_2 ++ data_hi).
  Exists data_3.
  Exists (l_r ++ data_r_hi).
  replace (an_pre - bn_pre - (an_pre - bn_pre)) with 0 by lia.
  replace (bn_pre - bn_pre) with 0 by lia.
  replace (an_pre - an_pre) with 0 by lia.
  rewrite <- H0, <- H2, <- H4, <- H6.
  sep_apply (UIntArray.full_merge_to_full rp_pre bn_pre an_pre l_r data_r_hi); try lia.
  sep_apply_l_atomic (UIntArray.full_merge_to_full ap_pre bn_pre an_pre data_2 data_hi); try lia.
  assert (Zlength (l_r ++ data_r_hi) = an_pre) as Hlen_r by (rewrite Zlength_app; lia).
  assert (Zlength (data_2 ++ data_hi) = an_pre) as Hlen_a by (rewrite Zlength_app; lia).
  entailer!.
  assert (list_to_Z UINT_MOD (l_r ++ data_r_hi) = val_r + val' * UINT_MOD ^ bn_pre) as Hval_r_out.
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite PreH12, Hdata_r_hi_val, PreH11. reflexivity. }
  assert (list_to_Z UINT_MOD (data_2 ++ data_hi) = val_a) as Hval_a_out.
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hdata_lo_val, Hdata_hi_val, <- H4, <- PreH15. lia. }
  rewrite Hval_r_out, Hval_a_out.
  entailer!.
  - replace (Zlength (l_r ++ data_r_hi)) with an_pre by (rewrite Zlength_app; lia).
    replace (Zlength (data_2 ++ data_hi)) with an_pre by (rewrite Zlength_app; lia).
    entailer!.
  - rewrite Zlength_app; lia.
  - apply list_within_bound_concat; auto.
  - rewrite Zlength_app; lia.
  - apply list_within_bound_concat; auto.
  - rewrite PreH15.
    assert (Hr_eq: val_r = val_a_lo - val_b + retval_2 * UINT_MOD ^ bn_pre) by lia.
    rewrite Hr_eq.
    assert (Hhi_eq: val' = val_a_hi - retval_2 + retval * UINT_MOD ^ (an_pre - bn_pre)) by lia.
    rewrite Hhi_eq.
    replace (UINT_MOD ^ an_pre) with (UINT_MOD ^ bn_pre * UINT_MOD ^ (an_pre - bn_pre)) by
      (rewrite <- Z.pow_add_r; try lia; f_equal; lia).
    lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_1 : mpn_sub_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros data_a.
  Exists (list_to_Z UINT_MOD (sublist bn an data_a)).
  Exists (list_to_Z UINT_MOD (sublist 0 bn data_a)).
  Exists (sublist 0 bn data_a).
  Exists (sublist bn an data_a).
  rewrite Zlength_sublist; try lia.
  sep_apply (UIntArray.full_split_to_full ap bn); try lia.
  rewrite <- H0.
  rewrite Zlength_sublist; try lia.
  replace (bn - 0) with bn by lia.
  entailer!.
  all : try apply list_within_bound_sublist ; try lia ; try tauto.
  destruct H as [Hval_a Hbound_a].
  rewrite <- Hval_a.
  assert (data_a = sublist 0 an data_a) as Heq.
  { rewrite sublist_self. reflexivity. lia. }
  rewrite Heq at 1.
  rewrite (sublist_split 0 an bn data_a); try lia.
  rewrite list_to_Z_app by exact UINT_MOD_pos.
  rewrite Zlength_sublist; try lia.
  replace (bn - 0) with bn by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_2 : mpn_sub_which_implies_wit_2.
Proof.
  pre_process.
  apply UIntArray.undef_full_split_to_undef_full; try lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_3 : mpn_sub_which_implies_wit_3.
Proof.
  pre_process.
  unfold mpd_store_Z, mpd_store_list.
  Intros l_r.
  Exists l_r.
  rewrite <- H0.
  entailer!.
Qed.

