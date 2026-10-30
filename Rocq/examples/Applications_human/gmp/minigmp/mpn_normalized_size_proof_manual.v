From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_normalized_size_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_normalized_size_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_normalized_size_entail_wit_3_plain_split_goal_1 : mpn_normalized_size_entail_wit_3_plain_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_plain_split_goal_2 : mpn_normalized_size_entail_wit_3_plain_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_plain : mpn_normalized_size_entail_wit_3_plain.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_3_plain_split_goal_1.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_3_plain_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_4_read0_split_goal_1 : mpn_normalized_size_entail_wit_4_read0_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_4_read0_split_goal_2 : mpn_normalized_size_entail_wit_4_read0_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold normalized_size_read0_guard.
  left.
  lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_4_read0 : mpn_normalized_size_entail_wit_4_read0.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_4_read0_split_goal_1.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_4_read0_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_5_plain_split_goal_1 : mpn_normalized_size_entail_wit_5_plain_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist in PreH1 ; try lia.
  replace (n - 1 + 0) with (n - 1) in * by lia.
  rewrite (sublist_split 0 n (n-1)) in *  ; try lia.
  set (m := n - 1) in *.
  replace n with (m + 1) in * by lia.
  rewrite (sublist_single 0 m lp) in * ; try lia.
  rewrite PreH1 in *.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat in PreH5 ; [ | lia | apply list_within_bound_sublist ; [ lia | lia | tauto] | simpl ; lia].
  simpl in PreH5.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_5_plain_split_goal_spatial : mpn_normalized_size_entail_wit_5_plain_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist in PreH1 ; try lia.
  replace (n - 1 + 0) with (n - 1) in * by lia.
  rewrite (sublist_split 0 n (n-1)) in *  ; try lia.
  set (m := n - 1) in *.
  replace n with (m + 1) in * by lia.
  rewrite (sublist_single 0 m lp) in * ; try lia.
  rewrite PreH1 in *.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat in PreH5 ; [ | lia | apply list_within_bound_sublist ; [ lia | lia | tauto] | simpl ; lia].
  sep_apply (UIntArray.full_split_to_seg xp_pre m) ; try lia.
  sep_apply (UIntArray.seg_to_undef_seg xp_pre m ).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg ; try lia.
  sep_apply UIntArray.seg_to_full.
  replace (xp_pre + 0 * sizeof ( UINT )) with (xp_pre) by lia.
  replace (m - 0) with m by lia.
  assert (Hlen_sub: m = Zlength(sublist 0 m lp)).
  {
    rewrite Zlength_sublist ; try lia.
  }
  rewrite Hlen_sub at 2.
  rewrite sublist_app_exact1.
  cancel.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_5_plain : mpn_normalized_size_entail_wit_5_plain.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_5_plain_split_goal_spatial.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_5_plain_split_goal_1.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_6_read0_split_goal_1 : mpn_normalized_size_entail_wit_6_read0_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH7 as Hcalc.
  rewrite (sublist_split 0 n (n - 1)) in Hcalc; try lia.
  set (m := n - 1) in Hcalc.
  replace n with (m + 1) in Hcalc by (unfold m; lia).
  rewrite (sublist_single 0 m l) in Hcalc; try lia.
  change (Znth m l 0 = 0) in PreH1.
  rewrite PreH1 in Hcalc.
  unfold UINT_MOD in Hcalc.
  rewrite list_to_Z_concat in Hcalc;
    [ | lia
      | apply list_within_bound_sublist; try lia; tauto
      | simpl; lia ].
  simpl in Hcalc.
  rewrite Z.add_0_r in Hcalc.
  change (list_to_Z UINT_MOD (sublist 0 (n - 1) l) = val_read0) in Hcalc.
  exact Hcalc.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_6_read0_split_goal_2 : mpn_normalized_size_entail_wit_6_read0_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold normalized_size_read0_guard.
  destruct (Z.eq_dec (n - 1) 0) as [Hm | Hm].
  - right.
    replace (Znth 0 l 0) with (Znth (n - 1) l 0) by
      (rewrite Hm; reflexivity).
    exact PreH1.
  - left; lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_6_read0 : mpn_normalized_size_entail_wit_6_read0.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_normalized_size_entail_wit_6_read0_split_goal_1.
  + Goal_apply proof_of_mpn_normalized_size_entail_wit_6_read0_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_7_1_read0_split_goal_1 : mpn_normalized_size_entail_wit_7_1_read0_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n = 0) by lia.
  subst n.
  rewrite Zsublist_nil; try lia.
  simpl.
  lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_7_1_read0 : mpn_normalized_size_entail_wit_7_1_read0.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_entail_wit_7_1_read0_split_goal_1.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_7_2_read0_split_goal_1 : mpn_normalized_size_entail_wit_7_2_read0_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite list_last_to_Znth.
  - rewrite Zlength_sublist; try lia.
    replace (n - 0 - 1) with (n - 1) by lia.
    pose proof (list_within_bound_sublist UINT_MOD l 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))) as Hbound.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n l) (n - 1) (ltac:(lia)) Hbound) as Hznth.
    rewrite Znth_sublist in Hznth; try lia.
    replace (n - 1 + 0) with (n - 1) in Hznth by lia.
    rewrite Znth_sublist; try lia.
    replace (n - 1 + 0) with (n - 1) by lia.
    lia.
  - intro Hnil.
    pose proof (Zlength_sublist 0 n l) as Hlen.
    rewrite Hnil in Hlen.
    rewrite Zlength_nil in Hlen.
    lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_7_2_read0 : mpn_normalized_size_entail_wit_7_2_read0.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_entail_wit_7_2_read0_split_goal_1.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1_read0_split_goal_spatial : mpn_normalized_size_return_wit_1_read0_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n = 0 \/ n > 0) as Hncase by lia.
  destruct Hncase as [Hn0 | Hnpos].
  - subst n.
    unfold normalized_size_read0_guard in PreH4.
    destruct PreH4 as [Hbad | Hzero]; try lia.
    rewrite Zsublist_nil in PreH5; try lia.
    rewrite list_to_Z_nil in PreH5.
    subst val_read0.
    sep_apply (UIntArray.full_split_to_seg xp_pre 1 n_pre l); try lia.
    sep_apply (UIntArray.seg_to_full xp_pre 0 1 (sublist 0 1 l)).
    sep_apply (UIntArray.seg_to_undef_seg xp_pre 1 n_pre (sublist 1 n_pre l)).
    unfold mpd_store_Z_compact_read0.
    Exists (@nil Z).
    simpl.
    unfold Zmax.
    replace (Z.max 0 1) with 1 by lia.
    replace (sublist 0 1 l) with (Znth 0 l 0 :: nil).
    2:{ replace 1 with (0 + 1) by lia. rewrite (sublist_single 0 0 l ltac:(lia)). reflexivity. }
    rewrite Hzero.
    replace (xp_pre + 0) with xp_pre by lia.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      rewrite list_to_Z_nil, Zlength_nil.
      lia.
  - sep_apply (UIntArray.full_split_to_seg xp_pre n n_pre l); try lia.
    sep_apply (UIntArray.seg_to_full xp_pre 0 n (sublist 0 n l)).
    sep_apply (UIntArray.seg_to_undef_seg xp_pre n n_pre (sublist n n_pre l)).
    unfold mpd_store_Z_compact_read0.
    Exists (sublist 0 n l).
    rewrite Zlength_sublist; try lia.
    replace (n - 0) with n by lia.
    assert (Hbound : list_within_bound UINT_MOD (sublist 0 n l)).
    { apply list_within_bound_sublist; try lia; tauto. }
    destruct (sublist 0 n l) eqn:Hsub.
    + pose proof (Zlength_sublist 0 n l) as Hlen.
      rewrite Hsub in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    + change (mpd_read0_data (z :: l0)) with (z :: l0).
      unfold Zmax.
      replace (Z.max n 1) with n by lia.
      replace (xp_pre + 0 * sizeof(UINT)) with xp_pre by lia.
      replace (n - 0) with n by lia.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        split; [exact PreH5 |].
        split; [exact PreH8 |].
        split; [exact Hbound | reflexivity].
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1_read0 : mpn_normalized_size_return_wit_1_read0.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_return_wit_1_read0_split_goal_spatial.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_2_plain_split_goal_spatial : mpn_normalized_size_return_wit_2_plain_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  assert (n = 0) by lia.
  subst n.
  rewrite Zsublist_nil in * ; try lia.
  unfold mpd_store_list.
  Exists nil.
  split_pure_spatial.
  - change (Zlength (@nil Z)) with 0.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    repeat split; simpl; try assumption; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_2_plain : mpn_normalized_size_return_wit_2_plain.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_return_wit_2_plain_split_goal_spatial.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_3_plain_split_goal_spatial : mpn_normalized_size_return_wit_3_plain_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Exists (sublist 0 n lp).
  rewrite Zlength_sublist ; try lia.
  replace (n - 0) with n by lia.
  pose proof (list_within_bound_sublist UINT_MOD lp 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))).
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  rewrite list_last_to_Znth.
  + rewrite Zlength_sublist ; try lia.
    replace (n - 0 -  1) with (n - 1) by lia.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n lp) (n - 1) (ltac:(lia)) (ltac:(tauto))).
    repeat split; try assumption; lia.
  + intro Hnil. rewrite Hnil in PreH1.
    unfold Znth in PreH1. simpl in PreH1.
    contradiction PreH1; destruct (Z.to_nat (n - 1)); reflexivity.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_3_plain : mpn_normalized_size_return_wit_3_plain.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_return_wit_3_plain_split_goal_spatial.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z.
  unfold mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    destruct H; assumption.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_2 : mpn_normalized_size_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z.
  unfold mpd_store_list.
  Intros l.
  destruct H as [Hval Hbound].
  Exists l.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity.
Qed.

