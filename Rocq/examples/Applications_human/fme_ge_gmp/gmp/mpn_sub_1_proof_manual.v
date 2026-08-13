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

Lemma proof_of_mpn_sub_1_entail_wit_3_1_non_alias_split_goal_1 :
  mpn_sub_1_entail_wit_3_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH9 into Hlen_l'.
  rename PreH10 into Hval_sub.
  rename PreH11 into Hval_l'.
  rename PreH12 into Hbound_l'.
  rename PreH13 into Hbound_l.
  rename PreH16 into Hrec.
  set (new := Znth i l 0 - b).
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
  exact Hmain.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_1_non_alias_split_goal_2 :
  mpn_sub_1_entail_wit_3_1_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (new := Znth i l 0 - b).
  assert (Hz_bound: 0 <= Znth i l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l i); try exact PreH13; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. unfold UINT_MOD in *. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  apply list_within_bound_concat; try exact PreH12.
  exact Hsingle_bound.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_1_non_alias_split_goal_3 :
  mpn_sub_1_entail_wit_3_1_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9.
  lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_1_non_alias :
  mpn_sub_1_entail_wit_3_1_non_alias.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_3_1_non_alias_split_goal_1.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_3_1_non_alias_split_goal_2.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_3_1_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_2_non_alias_split_goal_1 :
  mpn_sub_1_entail_wit_3_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH9 into Hlen_l'.
  rename PreH10 into Hval_sub.
  rename PreH11 into Hval_l'.
  rename PreH12 into Hbound_l'.
  rename PreH13 into Hbound_l.
  rename PreH16 into Hrec.
  set (new := unsigned_last_nbits (Znth i l 0 - b) 32).
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
  exact Hmain.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_2_non_alias_split_goal_2 :
  mpn_sub_1_entail_wit_3_2_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (new := unsigned_last_nbits (Znth i l 0 - b) 32).
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  apply list_within_bound_concat; try exact PreH12.
  exact Hsingle_bound.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_2_non_alias_split_goal_3 :
  mpn_sub_1_entail_wit_3_2_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9.
  lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_3_2_non_alias :
  mpn_sub_1_entail_wit_3_2_non_alias.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_3_2_non_alias_split_goal_1.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_3_2_non_alias_split_goal_2.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_3_2_non_alias_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_4_1_rp_eq_ap : mpn_sub_1_entail_wit_4_1_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH11 into Hlen_l'.
  rename PreH12 into Hval_sub.
  rename PreH13 into Hval_l'.
  rename PreH14 into Hbound_l'.
  rename PreH15 into Hbound_l.
  rename PreH18 into Hrec.
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
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l - i = Zlength (new :: sublist (i + 1) (Zlength l) l)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l'_2 (new :: nil)).
    dump_pre_spatial; lia.
    cancel.
  - Intros.
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_4_2_rp_eq_ap : mpn_sub_1_entail_wit_4_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH11 into Hlen_l'.
  rename PreH12 into Hval_sub.
  rename PreH13 into Hval_l'.
  rename PreH14 into Hbound_l'.
  rename PreH15 into Hbound_l.
  rename PreH18 into Hrec.
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
    dump_pre_spatial; lia.
    replace (i + 1 - i) with 1 by lia.
    assert (Hlen_cons:
      Zlength l - i = Zlength (new :: sublist (i + 1) (Zlength l) l)).
    { rewrite Zlength_cons, Zlength_sublist; lia. }
    rewrite Hlen_cons.
    rewrite sublist_cons_head.
    rewrite sublist_cons_tail_all.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1) l'_2 (new :: nil)).
    dump_pre_spatial; lia.
    cancel.
  - Intros.
    repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_5_1_non_alias : mpn_sub_1_entail_wit_5_1_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  set (new := Znth 0 l 0 - b0_non_alias).
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (list_to_Z UINT_MOD (new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (new :: nil).
  assert (Hz_bound: 0 <= Znth 0 l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l 0); try exact PreH9; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. unfold UINT_MOD in *. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Hmain:
    list_to_Z UINT_MOD (new :: nil) - 0 * UINT_MOD ^ 1 =
    list_to_Z UINT_MOD (sublist 0 1 l) - b0_non_alias).
  {
    subst new.
    rewrite (sublist_single 0); try lia.
    rewrite !list_to_Z_cons, !list_to_Z_nil.
    ring.
  }
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.full_to_seg rp_pre 1 (new :: nil)).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_5_2_non_alias : mpn_sub_1_entail_wit_5_2_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst i.
  set (new := unsigned_last_nbits (Znth 0 l 0 - b0_non_alias) 32).
  rewrite UIntArray.seg_single.
  rewrite UIntArray.seg_to_full.
  replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (list_to_Z UINT_MOD (new :: nil)).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (new :: nil).
  assert (Hz_bound: 0 <= Znth 0 l 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l 0); try exact PreH9; lia. }
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Hborrow: new - UINT_MOD = Znth 0 l 0 - b0_non_alias).
  {
    subst new. unfold unsigned_last_nbits.
    change (2 ^ 32) with UINT_MOD.
    replace (Znth 0 l 0 - b0_non_alias)
      with (-(b0_non_alias - Znth 0 l 0)) by ring.
    rewrite Z_mod_nz_opp_full.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). ring.
    - rewrite Z.mod_small by (unfold UINT_MOD in *; lia). lia.
  }
  assert (Hmain:
    list_to_Z UINT_MOD (new :: nil) - 1 * UINT_MOD ^ 1 =
    list_to_Z UINT_MOD (sublist 0 1 l) - b0_non_alias).
  {
    rewrite (sublist_single 0); try lia.
    rewrite !list_to_Z_cons, !list_to_Z_nil.
    replace (UINT_MOD ^ 1) with UINT_MOD by ring.
    lia.
  }
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.full_to_seg rp_pre 1 (new :: nil)).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_6_1_rp_eq_ap : mpn_sub_1_entail_wit_6_1_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
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
    dump_pre_spatial; lia.
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
    rewrite UIntArray.seg_empty.
    Intros.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (replace (0 + 1) with 1 by lia; reflexivity);
      try (rewrite Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_6_2_rp_eq_ap : mpn_sub_1_entail_wit_6_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
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
    dump_pre_spatial; lia.
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
    rewrite UIntArray.seg_empty.
    Intros.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (replace (0 + 1) with 1 by lia; reflexivity);
      try (rewrite Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_mpn_sub_1_return_wit_1_non_alias : mpn_sub_1_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
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
    rewrite Hi.
    rewrite PreH13.
    cancel.
  - rewrite Hi in PreH9, PreH15.
    rewrite (sublist_self l n_pre) in PreH9 by lia.
    rewrite PreH14 in PreH9.
    repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (split; assumption).
Qed.

Lemma proof_of_mpn_sub_1_return_wit_2_rp_eq_ap : mpn_sub_1_return_wit_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists val2.
  split_pure_spatial.
  - rewrite Zsublist_nil by lia.
    replace (Zlength l') with n_pre by lia.
    replace (Zlength l) with n_pre by lia.
    sep_apply_l_atomic
      (UIntArray.seg_merge_to_seg rp_pre 0 n_pre n_pre l' (@nil Z)).
    + dump_pre_spatial; lia.
    + rewrite app_nil_r.
      sep_apply_l_atomic (UIntArray.seg_to_full rp_pre 0 n_pre l').
      replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
      replace (n_pre - 0) with n_pre by lia.
      unfold mpd_store_Z, mpd_store_list.
      Exists l'.
      split_pure_spatial.
      * rewrite Hi.
        cancel.
      * repeat split_pures; dump_pre_spatial; try assumption; try lia;
          try (split; assumption).
  - Intros.
    rewrite Hi in PreH9, PreH15.
    rewrite (sublist_self l n_pre) in PreH9 by lia.
    rewrite PreH14 in PreH9.
    repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (split; assumption).
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_1 : mpn_sub_1_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_2 : mpn_sub_1_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_3_split_goal_spatial :
  mpn_sub_1_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros.
  prop_apply (UIntArray.full_Zlength ap n l).
  Intros.
  sep_apply_l_atomic (UIntArray.full_split_to_seg ap 0 n l).
  - dump_pre_spatial; lia.
    - rewrite Zsublist_nil by lia.
    replace n with (Zlength l) by lia.
    rewrite (sublist_self l (Zlength l)) by lia.
    rewrite UIntArray.seg_empty.
    Intros.
    cancel.
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_3 : mpn_sub_1_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_1_which_implies_wit_3_split_goal_spatial.
Qed.
