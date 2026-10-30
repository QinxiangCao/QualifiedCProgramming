From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_goal.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_gmp_abs_return_wit_1_split_goal_1 : gmp_abs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Z.abs_eq by lia.
  reflexivity.
Qed.

Lemma proof_of_gmp_abs_return_wit_1 : gmp_abs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_abs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gmp_abs_return_wit_2_split_goal_1 : gmp_abs_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Z.abs_neq by lia.
  reflexivity.
Qed.

Lemma proof_of_gmp_abs_return_wit_2 : gmp_abs_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_abs_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_gmp_max_return_wit_1_split_goal_1 : gmp_max_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Z.max_l by lia.
  reflexivity.
Qed.

Lemma proof_of_gmp_max_return_wit_1 : gmp_max_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_max_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gmp_max_return_wit_2_split_goal_1 : gmp_max_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rewrite Z.max_r by lia.
  reflexivity.
Qed.

Lemma proof_of_gmp_max_return_wit_2 : gmp_max_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_max_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_1_split_goal_1 : mpn_copyi_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Zlength_nonneg l). lia.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_1_split_goal_2 : mpn_copyi_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_copyi_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_mpn_copyi_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2_split_goal_1 : mpn_copyi_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1_split_goal_spatial : mpn_copyi_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia. subst i.
  rewrite sublist_self by lia.
  unfold mpd_store_Z, mpd_store_list.
  Exists l l.
  rewrite <- PreH4.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto].
Qed.

Lemma proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l.
  Exists l.
  match goal with H : n = Zlength l |- _ => rewrite H end.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; tauto].
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1_split_goal_1 : mpn_cmp_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (n_pre - 1 + 1) with n_pre by lia.
  rewrite !Zsublist_nil by lia. reflexivity.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_2_split_goal_1 : mpn_cmp_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (n - 1 + 1) with n by lia.
  rewrite (sublist_split n n_pre (n+1) l1) by lia.
  rewrite (sublist_split n n_pre (n+1) l2) by lia.
  rewrite (sublist_single 0 n l1) by lia.
  rewrite (sublist_single 0 n l2) by lia.
  congruence.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1_split_goal_1 : mpn_cmp_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (n = -1) by lia. subst n.
  replace (-1 + 1) with 0 in * by lia.
  rewrite (sublist_self l1 n_pre ltac:(lia)) in PreH4.
  rewrite (sublist_self l2 n_pre ltac:(lia)) in PreH4.
  congruence.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1_split_goal_spatial : mpn_cmp_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists l1 l2.
  split_pure_spatial.
  - replace (Zlength l1) with n_pre by lia.
    replace (Zlength l2) with n_pre by lia. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1 : mpn_cmp_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_cmp_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mpn_cmp_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2_split_goal_1 : mpn_cmp_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (list_to_Z UINT_MOD l2 < list_to_Z UINT_MOD l1).
  { apply (list_to_Z_cmp_same_length UINT_MOD UINT_MOD_pos l2 l1 n); try lia; try assumption.
    replace (Zlength l1) with n_pre by lia.
    replace (Zlength l2) with n_pre by lia. symmetry; assumption. }
  lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2_split_goal_spatial : mpn_cmp_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists l1 l2.
  split_pure_spatial.
  - replace (Zlength l1) with n_pre by lia.
    replace (Zlength l2) with n_pre by lia. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_cmp_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mpn_cmp_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3_split_goal_1 : mpn_cmp_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (list_to_Z UINT_MOD l1 < list_to_Z UINT_MOD l2).
  { apply (list_to_Z_cmp_same_length UINT_MOD UINT_MOD_pos l1 l2 n); try lia; try assumption.
    replace (Zlength l1) with n_pre by lia.
    replace (Zlength l2) with n_pre by lia. assumption. }
  lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3_split_goal_spatial : mpn_cmp_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists l1 l2.
  split_pure_spatial.
  - replace (Zlength l1) with n_pre by lia.
    replace (Zlength l2) with n_pre by lia. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3 : mpn_cmp_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_cmp_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_mpn_cmp_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  split_pure_spatial.
  - replace (Zlength l1) with n by lia.
    replace (Zlength l2) with n by lia. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1_split_goal_spatial : mpn_cmp4_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst; cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1 : mpn_cmp4_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2_split_goal_spatial : mpn_cmp4_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst; cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2 : mpn_cmp4_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_3_split_goal_spatial : mpn_cmp4_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst; cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_3 : mpn_cmp4_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_4_split_goal_1 : mpn_cmp4_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_cmp4_return_wit_4 : mpn_cmp4_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z_compact.
  Intros data_a data_b.
  Exists data_a data_b.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  unfold UINT_MOD in *.
  pose proof (list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) data_a data_b
    (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia))).
  lia.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_5_split_goal_1 : mpn_cmp4_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_cmp4_return_wit_5 : mpn_cmp4_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z_compact.
  Intros data_a data_b.
  Exists data_a data_b.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  unfold UINT_MOD in *.
  pose proof (list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) data_b data_a
    (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia))).
  lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2_split_goal_1 : mpn_normalized_size_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2_split_goal_2 : mpn_normalized_size_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_split_goal_1 : mpn_normalized_size_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist in PreH1 ; try lia.
  replace (n - 1 + 0) with (n - 1) in * by lia.
  rewrite (sublist_split 0 n (n-1)) in *  ; try lia.
  set (m := n - 1) in *.
  replace n with (m + 1) in * by lia.
  rewrite (sublist_single 0 m l) in * ; try lia.
  rewrite PreH1 in *.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat in PreH5 ; [ | lia | apply list_within_bound_sublist ; [ lia | lia | tauto] | simpl ; lia].
  dump_pre_spatial. simpl in PreH5. lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_split_goal_spatial : mpn_normalized_size_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist in PreH1 ; try lia.
  replace (n - 1 + 0) with (n - 1) in * by lia.
  rewrite (sublist_split 0 n (n-1)) in *  ; try lia.
  set (m := n - 1) in *.
  replace n with (m + 1) in * by lia.
  rewrite (sublist_single 0 m l) in * ; try lia.
  rewrite PreH1 in *.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat in PreH5 ; [ | lia | apply list_within_bound_sublist ; [ lia | lia | tauto] | simpl ; lia].
  sep_apply (UIntArray.full_split_to_seg xp_pre m) ; try lia.
  sep_apply (UIntArray.seg_to_undef_seg xp_pre m ).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg ; try lia.
  sep_apply UIntArray.seg_to_full.
  replace (xp_pre + 0 * sizeof ( UINT )) with (xp_pre) by lia.
  replace (m - 0) with m by lia.
  assert (Hm_sub_len : m = Zlength(sublist 0 m l)).
  {
    rewrite Zlength_sublist ; try lia.
  }
  rewrite Hm_sub_len at 2.
  rewrite sublist_app_exact1.
  cancel.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3 : mpn_normalized_size_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1_split_goal_spatial : mpn_normalized_size_return_wit_1_split_goal_spatial.
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

Lemma proof_of_mpn_normalized_size_return_wit_1 : mpn_normalized_size_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_2_split_goal_spatial : mpn_normalized_size_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Exists (sublist 0 n l).
  rewrite Zlength_sublist ; try lia.
  replace (n - 0) with n by lia.
  pose proof (list_within_bound_sublist UINT_MOD l 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))).
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  rewrite list_last_to_Znth.
  + rewrite Zlength_sublist ; try lia.
    replace (n - 0 -  1) with (n - 1) by lia.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n l) (n - 1) (ltac:(lia)) (ltac:(tauto))).
    repeat split; try assumption; lia.
  + intro Hnil. rewrite Hnil in PreH1.
    unfold Znth in PreH1. simpl in PreH1.
    contradiction PreH1; destruct (Z.to_nat (n - 1)); reflexivity.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_2 : mpn_normalized_size_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_return_wit_2_split_goal_spatial.
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

Lemma proof_of_mpn_add_1_entail_wit_1_1_split_goal_1 : mpn_add_1_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (unsigned_Lastnbits_range (Znth i l 0 + b) 32 ltac:(lia)) as Hrange.
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (Znth i l 0 + b) 32
    :: nil)) by (simpl; unfold UINT_MOD in *; lia).
  apply list_within_bound_concat; try tauto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_1_split_goal_2 : mpn_add_1_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH8.
  lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_1_split_goal_3 : mpn_add_1_entail_wit_1_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite list_to_Z_concat; try lia; try tauto.
  rewrite PreH10. simpl list_to_Z.
  rewrite PreH8.
  rewrite (sublist_split 0 (i + 1) i); try lia.
  rewrite (sublist_single 0 i l); try lia.
  rewrite list_to_Z_concat; try lia; try tauto.
  - rewrite PreH9. simpl list_to_Z.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia.
    unfold unsigned_last_nbits.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_uncarry (Znth i l 0) b UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      ltac:(apply list_within_bound_Znth; try lia; auto)
      ltac:(lia) PreH1) as Hsum.
    change 4294967296 with UINT_MOD.
    rewrite <- Hsum.
    replace (val1_2 + Znth i l 0 * UINT_MOD ^ i + b_pre)
      with ((val1_2 + b_pre) + Znth i l 0 * UINT_MOD ^ i) by ring.
    rewrite <- PreH7.
    ring.
  - apply list_within_bound_sublist; try lia; try tauto.
  - simpl. split; try tauto. apply list_within_bound_Znth; try lia. auto.
  - simpl. split; try tauto.
    change UINT_MOD with (2 ^ 32).
    apply unsigned_Lastnbits_range; lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_1 : mpn_add_1_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_1_split_goal_1.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_1_split_goal_2.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_1_split_goal_3.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2_split_goal_1 : mpn_add_1_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (unsigned_Lastnbits_range (Znth i l 0 + b) 32 ltac:(lia)) as Hrange.
  assert (list_within_bound UINT_MOD (unsigned_last_nbits (Znth i l 0 + b) 32
    :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  apply list_within_bound_concat; try tauto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2_split_goal_2 : mpn_add_1_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH8.
  lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2_split_goal_3 : mpn_add_1_entail_wit_1_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite list_to_Z_concat; try lia; try tauto.
  rewrite PreH10. simpl list_to_Z.
  rewrite PreH8.
  rewrite (sublist_split 0 (i + 1) i); try lia.
  rewrite (sublist_single 0 i l); try lia.
  rewrite list_to_Z_concat; try lia; try tauto.
  - rewrite PreH9. simpl list_to_Z.
    rewrite Zlength_sublist; try lia.
    replace (i - 0) with i by lia.
    unfold unsigned_last_nbits.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_carry (Znth i l 0) b UINT_MOD
      ltac:(unfold UINT_MOD; lia)
      ltac:(apply list_within_bound_Znth; try lia; auto)
      ltac:(lia) PreH1) as Hsum.
    change 4294967296 with UINT_MOD.
    rewrite Z.pow_add_r by lia.
    replace (UINT_MOD ^ 1) with UINT_MOD by reflexivity.
    replace (val2_2 + (Znth i l 0 + b) mod UINT_MOD * UINT_MOD ^ i +
      1 * (UINT_MOD ^ i * UINT_MOD))
      with (val2_2 + ((Znth i l 0 + b) mod UINT_MOD + UINT_MOD) * UINT_MOD ^ i)
      by ring.
    rewrite <- Hsum.
    replace (val1_2 + Znth i l 0 * UINT_MOD ^ i + b_pre)
      with ((val1_2 + b_pre) + Znth i l 0 * UINT_MOD ^ i) by ring.
    rewrite <- PreH7.
    ring.
  - apply list_within_bound_sublist; try lia; try tauto.
  - simpl. split; try tauto. apply list_within_bound_Znth; try lia. auto.
  - simpl. split; try tauto.
    change UINT_MOD with (2 ^ 32).
    apply unsigned_Lastnbits_range; lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2_split_goal_4 : mpn_add_1_entail_wit_1_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1_2 : mpn_add_1_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_2_split_goal_1.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_2_split_goal_2.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_2_split_goal_3.
  + Goal_apply proof_of_mpn_add_1_entail_wit_1_2_split_goal_4.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_2_1 : mpn_add_1_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (new := unsigned_last_nbits (Znth 0 l 0 + b_pre) 32).
  sep_apply (UIntArray.seg_single rp_pre 0 new).
  sep_apply (UIntArray.seg_to_full rp_pre 0 (0 + 1) (new :: nil)).
  replace (rp_pre + 0 * sizeof ( UINT )) with (rp_pre) by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (new :: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (list_to_Z UINT_MOD (new :: nil)).
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Hmain:
    list_to_Z UINT_MOD (new :: nil) + 0 * UINT_MOD ^ 1 =
    list_to_Z UINT_MOD (sublist 0 1 l) + b_pre).
  {
    subst new.
    unfold UINT_MOD in *; simpl.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    rewrite (sublist_single 0); try lia. simpl.
    pose proof (Z_mod_add_uncarry (Znth 0 l 0) b_pre 4294967296
      ltac:(lia) ltac:(apply list_within_bound_Znth; try lia; auto)
      ltac:(lia) PreH1) as Hsum.
    rewrite <- Hsum.
    lia.
  }
  split_pure_spatial.
  - cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    all: simpl; reflexivity.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_2_2 : mpn_add_1_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (new := unsigned_last_nbits (Znth 0 l 0 + b_pre) 32).
  sep_apply (UIntArray.seg_single rp_pre 0 new).
  sep_apply (UIntArray.seg_to_full rp_pre 0 (0 + 1) (new :: nil)).
  replace (rp_pre + 0 * sizeof ( UINT )) with (rp_pre) by lia.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  Exists (new :: nil).
  Exists (list_to_Z UINT_MOD (sublist 0 1 l)).
  Exists (list_to_Z UINT_MOD (new :: nil)).
  assert (Hnew_range: 0 <= new < UINT_MOD).
  { subst new. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hsingle_bound: list_within_bound UINT_MOD (new :: nil)).
  { simpl. split; [exact Hnew_range | tauto]. }
  assert (Hmain:
    list_to_Z UINT_MOD (new :: nil) + 1 * UINT_MOD ^ 1 =
    list_to_Z UINT_MOD (sublist 0 1 l) + b_pre).
  {
    subst new.
    rewrite (sublist_single 0); try lia.
    simpl.
    unfold unsigned_last_nbits in *.
    replace (2 ^ 32) with 4294967296 in * by reflexivity.
    pose proof (Z_mod_add_carry (Znth 0 l 0) b_pre 4294967296
      ltac:(lia) ltac:(apply list_within_bound_Znth; try lia; auto)
      ltac:(lia) PreH1) as Hsum.
    rewrite <- Hsum.
    lia.
  }
  split_pure_spatial.
  - cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    all: simpl; reflexivity.
Qed.

Lemma proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z , mpd_store_list.
  assert (Hlen_done : i = n_pre) by lia. subst i.
  match goal with
  | Hlen : Zlength l' = n_pre |- _ => rewrite Hlen
  end.
  rewrite UIntArray.undef_seg_empty.
  rewrite Hlen_done in PreH8.
  rewrite sublist_self in PreH8 by lia.
  assert (val = val1) by lia. subst val1.
  assert (Hmain: val2 + b * UINT_MOD ^ n_pre = val + b_pre).
  { rewrite Hlen_done in PreH6. lia. }
  Exists val2.
  Exists l l'.
  match goal with
  | Hval2 : list_to_Z _ l' = val2 |- _ => rewrite Hval2
  end.
  match goal with
  | Hlen : Zlength l' = n_pre |- _ => rewrite Hlen
  end.
  rewrite PreH11.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + split; [symmetry; assumption | assumption].
    + split; [reflexivity | assumption].
Qed.

Lemma proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z , mpd_store_list.
  Intros l1.
  Exists l1.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + reflexivity.
    + destruct H; assumption.
    + destruct H; assumption.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_1_split_goal_1 : mpn_add_n_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_add_n_entail_wit_1_split_goal_2 : mpn_add_n_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_add_n_entail_wit_1_split_goal_3 : mpn_add_n_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_n_entail_wit_1_split_goal_1.
  + Goal_apply proof_of_mpn_add_n_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_1_split_goal_1 : mpn_add_n_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hout_range: 0 <= out < UINT_MOD).
  { subst out. unfold UINT_MOD in *. lia. }
  assert (Ha_range: 0 <= Znth i l_a 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  assert (Hb_range: 0 <= Znth i l_b 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hval_app:
    list_to_Z UINT_MOD (l_r_2 ++ out :: nil) =
    val_r_2 + out * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 l_r_2 out Hout_range).
    rewrite PreH10, PreH12; ring.
  }
  assert (Ha_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_a) =
    val_a_prefix_2 + Znth i l_a 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i).
    - rewrite PreH8; ring.
    - lia.
    - exact PreH17.
  }
  assert (Hb_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_b) =
    val_b_prefix_2 + Znth i l_b 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i).
    - rewrite PreH9; ring.
    - lia.
    - exact PreH19.
  }
  rewrite Hval_app, Ha_sub, Hb_sub.
  subst out.
  unfold UINT_MOD in *.
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
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_1_split_goal_2 : mpn_add_n_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH12; lia.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_1_split_goal_3 : mpn_add_n_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hsingle: list_within_bound UINT_MOD
    (unsigned_last_nbits
      (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  apply list_within_bound_concat; try exact PreH11; exact Hsingle.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_1 : mpn_add_n_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_1_split_goal_1.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_1_split_goal_2.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_2_split_goal_1 : mpn_add_n_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hout_range: 0 <= out < UINT_MOD).
  { subst out. unfold UINT_MOD in *. lia. }
  assert (Ha_range: 0 <= Znth i l_a 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  assert (Hb_range: 0 <= Znth i l_b 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hval_app:
    list_to_Z UINT_MOD (l_r_2 ++ out :: nil) =
    val_r_2 + out * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 l_r_2 out Hout_range).
    rewrite PreH10, PreH12; ring.
  }
  assert (Ha_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_a) =
    val_a_prefix_2 + Znth i l_a 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i).
    - rewrite PreH8; ring.
    - lia.
    - exact PreH17.
  }
  assert (Hb_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_b) =
    val_b_prefix_2 + Znth i l_b 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i).
    - rewrite PreH9; ring.
    - lia.
    - exact PreH19.
  }
  rewrite Hval_app, Ha_sub, Hb_sub.
  subst out.
  unfold UINT_MOD in *.
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
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_2_split_goal_2 : mpn_add_n_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH12; lia.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_2_split_goal_3 : mpn_add_n_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hsingle: list_within_bound UINT_MOD
    (unsigned_last_nbits
      (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  apply list_within_bound_concat; try exact PreH11; exact Hsingle.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_2 : mpn_add_n_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_2_split_goal_1.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_2_split_goal_2.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_3_split_goal_1 : mpn_add_n_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hout_range: 0 <= out < UINT_MOD).
  { subst out. unfold UINT_MOD in *. lia. }
  assert (Ha_range: 0 <= Znth i l_a 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  assert (Hb_range: 0 <= Znth i l_b 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hval_app:
    list_to_Z UINT_MOD (l_r_2 ++ out :: nil) =
    val_r_2 + out * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 l_r_2 out Hout_range).
    rewrite PreH10, PreH12; ring.
  }
  assert (Ha_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_a) =
    val_a_prefix_2 + Znth i l_a 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i).
    - rewrite PreH8; ring.
    - lia.
    - exact PreH17.
  }
  assert (Hb_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_b) =
    val_b_prefix_2 + Znth i l_b 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i).
    - rewrite PreH9; ring.
    - lia.
    - exact PreH19.
  }
  rewrite Hval_app, Ha_sub, Hb_sub.
  subst out.
  unfold UINT_MOD in *.
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
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_3_split_goal_2 : mpn_add_n_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH12; lia.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_3_split_goal_3 : mpn_add_n_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hsingle: list_within_bound UINT_MOD
    (unsigned_last_nbits
      (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  apply list_within_bound_concat; try exact PreH11; exact Hsingle.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_3 : mpn_add_n_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_3_split_goal_1.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_3_split_goal_2.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_3_split_goal_3.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_4_split_goal_1 : mpn_add_n_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (out := unsigned_last_nbits
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (HOut_range: 0 <= out < UINT_MOD).
  { subst out. unfold UINT_MOD in *. lia. }
  assert (Ha_range: 0 <= Znth i l_a 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  assert (Hb_range: 0 <= Znth i l_b 0 < UINT_MOD).
  { apply list_within_bound_Znth; try lia; try tauto. }
  pose proof (unsigned_Lastnbits_range (Znth i l_a 0 + cy) 32
    ltac:(lia)) as Hinner_range.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hval_app:
    list_to_Z UINT_MOD (l_r_2 ++ out :: nil) =
    val_r_2 + out * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 l_r_2 out HOut_range).
    rewrite PreH10, PreH12; ring.
  }
  assert (Ha_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_a) =
    val_a_prefix_2 + Znth i l_a 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i).
    - rewrite PreH8; ring.
    - lia.
    - exact PreH17.
  }
  assert (Hb_sub:
    list_to_Z UINT_MOD (sublist 0 (i + 1) l_b) =
    val_b_prefix_2 + Znth i l_b 0 * UINT_MOD ^ i).
  {
    rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i).
    - rewrite PreH9; ring.
    - lia.
    - exact PreH19.
  }
  rewrite Hval_app, Ha_sub, Hb_sub.
  subst out.
  unfold UINT_MOD in *.
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
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_4_split_goal_2 : mpn_add_n_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH12; lia.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_4_split_goal_3 : mpn_add_n_entail_wit_2_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32
    ltac:(lia)) as Houter_range.
  assert (Hsingle: list_within_bound UINT_MOD
    (unsigned_last_nbits
      (unsigned_last_nbits (Znth i l_a 0 + cy) 32 + Znth i l_b 0) 32 :: nil)).
  { simpl. unfold UINT_MOD in *. lia. }
  apply list_within_bound_concat; try exact PreH11; exact Hsingle.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2_4 : mpn_add_n_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_4_split_goal_1.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_4_split_goal_2.
  + Goal_apply proof_of_mpn_add_n_entail_wit_2_4_split_goal_3.
Qed.

Lemma proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdone : i = n_pre) by lia. subst i.
  assert (Hmain : val_r + cy * UINT_MOD ^ n_pre =
      val_a_implementation + val_b_implementation).
  {
    rewrite Hdone in PreH11.
    rewrite sublist_self in PreH6 by lia.
    rewrite sublist_self in PreH7 by lia.
    rewrite <- PreH6, <- PreH7 in PreH11.
    rewrite PreH14, PreH16 in PreH11.
    exact PreH11.
  }
  unfold mpd_store_Z, mpd_store_list.
  rewrite Hdone.
  rewrite UIntArray.undef_seg_empty.
  LLM_pre_process ltac:(lia || int_auto).
  Exists val_r l_a l_b l_r.
  split_pure_spatial.
  - rewrite Hdone, PreH12, PreH13; cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_add_return_wit_1 : mpn_add_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
    all : try apply list_within_bound_concat ; try tauto.
    all : unfold UINT_MOD in *.
  + replace (an_pre) with (bn_pre + (an_pre - bn_pre)) by lia.
    rewrite Z.pow_add_r by lia.
    replace (val_r_out_2 + val' * 4294967296 ^ bn_pre +
      retval * (4294967296 ^ bn_pre * 4294967296 ^ (an_pre - bn_pre)))
      with (val_r_out_2 + (val' + retval * 4294967296 ^ (an_pre - bn_pre)) *
        4294967296 ^ bn_pre) by ring.
    rewrite PreH13.
    replace (val_a_low + val_a_high * 4294967296 ^ bn_pre + val_b)
      with ((val_a_low + val_b) + val_a_high * 4294967296 ^ bn_pre) by ring.
    rewrite <- PreH12.
    rewrite PreH1.
    ring.
  + split.
    * rewrite list_to_Z_concat; try lia; try tauto.
      rewrite Hla_val, Hla'_val.
      rewrite <- H4.
      lia.
    * apply list_within_bound_concat; tauto.
  + split.
    * rewrite list_to_Z_concat; try lia; try tauto.
      rewrite PreH10, Hlr'_val.
      rewrite PreH9.
      lia.
    * apply list_within_bound_concat; tauto.
Qed.

Lemma proof_of_mpn_add_return_wit_2 : mpn_add_return_wit_2.
Proof. 
  LLM_pre_process ltac:(int_auto).
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
  rewrite UIntArray.full_empty.
  rewrite Zlength_nil.
  rewrite UIntArray.undef_full_empty.
  rewrite <- H0, <- H2.
  rewrite PreH9, PreH8.
  split_pure_spatial.
  - cancel.
    normalize.
    cancel.
    Intros_p Hzero.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + split.
      * rewrite Hla_val, PreH12; ring.
      * assumption.
    + split; assumption.
    + split; [reflexivity | assumption].
Qed.

Lemma proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
    all : try apply list_within_bound_sublist ; try lia ; try tauto.
    rewrite <- Hval.
    rewrite <- (sublist_self l an) at 1; try lia.
    rewrite (sublist_split 0 an bn) ; try lia.
    unfold UINT_MOD in *.
    rewrite list_to_Z_concat ; try lia.
    rewrite Zlength_sublist ; try lia.
    replace (bn - 0) with bn by lia.
    lia.
    + apply list_within_bound_sublist; try lia; try tauto.
    + apply list_within_bound_sublist; try lia; try tauto.
    + split; [reflexivity |].
      apply list_within_bound_sublist; try lia; try tauto.
    + split; [reflexivity |].
      apply list_within_bound_sublist; try lia; try tauto.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_2_split_goal_spatial : mpn_add_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply UIntArray.undef_full_split_to_undef_full ; try lia.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_add_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_3 : mpn_add_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z , mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + reflexivity.
    + destruct H; assumption.
    + destruct H; assumption.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_1_split_goal_1 : gmp_umul_ppmm_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  (* 证明数学等式：w1_value * UINT_MOD + w0_value = u_pre * v_pre *)
  (* 使用GmpAux.v中的umul_ppmm_correct_with_carry引理 *)
  unfold UINT_MOD.
  
  (* 定义算法中的各个部分 *)
  set (ul := Z.land u_pre 65535).
  set (uh := Z.shiftr u_pre 16).
  set (vl := Z.land v_pre 65535).
  set (vh := Z.shiftr v_pre 16).
  set (x0 := ul * vl).
  set (x1 := ul * vh).
  set (x2 := uh * vl).
  set (x3 := uh * vh).
  set (x1' := (x1 + Z.shiftr x0 16) mod 4294967296).
  set (x1'' := (x1' + x2) mod 4294967296).
  
  (* 定义w1和w0根据引理 *)
  set (w1 := ((x3 + 65536) mod 4294967296 + Z.shiftr x1'' 16) mod 4294967296).
  set (w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296).
  assert (Hu32: 0 <= u_pre < 4294967296) by lia.
  assert (Hv32: 0 <= v_pre < 4294967296) by lia.
  
  (* 使用umul_ppmm_correct_with_carry引理证明w1 * 4294967296 + w0 = u_pre * v_pre *)
  pose proof (umul_ppmm_correct_with_carry u_pre v_pre ul uh vl vh x0 x1 x2 x3
    Hu32
    Hv32
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as Hlemma.
  
  assert (Hcarry: x1'' < x2). {
    pose proof Hu32 as Hu.
    pose proof Hv32 as Hv.
    

    assert (Hx1_exp: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296).
    { pose proof (land_65535_bounds u_pre Hu32) as Hul.
      pose proof (shiftr_16_bounds v_pre Hv) as Hvh.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx0_exp: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296).
    { pose proof (land_65535_bounds u_pre Hu32) as Hul.
      pose proof (land_65535_bounds v_pre Hv32) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx2_exp: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296).
    { pose proof (shiftr_16_bounds u_pre Hu) as Huh.
      pose proof (land_65535_bounds v_pre Hv32) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }

    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.shiftr v_pre 16) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.land v_pre 65535) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.shiftr u_pre 16 * Z.land v_pre 65535) 32) in PreH1 by lia.
    unfold unsigned_last_nbits in PreH1.
    change (2 ^ 32) with 4294967296 in PreH1.
    unfold x1'', x1', x0, x1, x2, ul, uh, vl, vh.
    exact PreH1.
  }
  
  (* 应用引理获得结论 *)
  specialize (Hlemma Hcarry).
  
  (* 展开 let 绑定 *)
  unfold w1, w0 in Hlemma.
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul in Hlemma.
  
  (* 转换目标中的 unsigned_last_nbits 为 mod 形式 *)
  repeat (unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296).
  
  (* 展开目标中的变量定义 *)
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul.
  
  (* 使用VC前提中的局部range事实获取边界 *)
  pose proof Hu32 as Hu.
  pose proof Hv32 as Hv.
  
  
  (* 证明各部分在范围内 *)
  assert (Hul_bounds: 0 <= Z.land u_pre 65535 < 65536) by (apply land_65535_bounds; assumption).
  assert (Hvl_bounds: 0 <= Z.land v_pre 65535 < 65536) by (apply land_65535_bounds; assumption).
  assert (Huh_bounds: 0 <= Z.shiftr u_pre 16 < 65536) by (apply shiftr_16_bounds; exact Hu).
  assert (Hvh_bounds: 0 <= Z.shiftr v_pre 16 < 65536) by (apply shiftr_16_bounds; exact Hv).
  
  (* 各乘积在 [0, 2^32) 范围内 *)
  assert (Hx0_small: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx1_small: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296) by nia.
  assert (Hx2_small: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx3_small: 0 <= Z.shiftr u_pre 16 * Z.shiftr v_pre 16 < 4294967296) by nia.
  
  (* 简化 mod 操作 *)
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.shiftr v_pre 16) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.shiftr v_pre 16) 4294967296) by lia.
  
  exact Hlemma.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_1 : gmp_umul_ppmm_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_umul_ppmm_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_2_split_goal_1 : gmp_umul_ppmm_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  (* 证明数学等式：w1_value * UINT_MOD + w0_value = u_pre * v_pre *)
  (* 使用GmpAux.v中的umul_ppmm_correct_no_carry引理 *)
  unfold UINT_MOD.
  
  (* 定义算法中的各个部分 *)
  set (ul := Z.land u_pre 65535).
  set (uh := Z.shiftr u_pre 16).
  set (vl := Z.land v_pre 65535).
  set (vh := Z.shiftr v_pre 16).
  set (x0 := ul * vl).
  set (x1 := ul * vh).
  set (x2 := uh * vl).
  set (x3 := uh * vh).
  set (x1' := (x1 + Z.shiftr x0 16) mod 4294967296).
  set (x1'' := (x1' + x2) mod 4294967296).
  
  (* 定义w1和w0根据引理（无进位情况） *)
  set (w1 := (x3 + Z.shiftr x1'' 16) mod 4294967296).
  set (w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296).
  assert (Hu32: 0 <= u_pre < 4294967296) by lia.
  assert (Hv32: 0 <= v_pre < 4294967296) by lia.
  
  (* 使用umul_ppmm_correct_no_carry引理 *)
  pose proof (umul_ppmm_correct_no_carry u_pre v_pre ul uh vl vh x0 x1 x2 x3
    Hu32
    Hv32
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as Hlemma.
  
  assert (Hnocarry: x1'' >= x2). {
    pose proof Hu32 as Hu.
    pose proof Hv32 as Hv.
    

    assert (Hx1_exp: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296).
    { pose proof (land_65535_bounds u_pre Hu32) as Hul.
      pose proof (shiftr_16_bounds v_pre Hv) as Hvh.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx0_exp: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296).
    { pose proof (land_65535_bounds u_pre Hu32) as Hul.
      pose proof (land_65535_bounds v_pre Hv32) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx2_exp: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296).
    { pose proof (shiftr_16_bounds u_pre Hu) as Huh.
      pose proof (land_65535_bounds v_pre Hv32) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }

    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.shiftr v_pre 16) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.land v_pre 65535) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.shiftr u_pre 16 * Z.land v_pre 65535) 32) in PreH1 by lia.
    unfold unsigned_last_nbits in PreH1.
    change (2 ^ 32) with 4294967296 in PreH1.
    unfold x1'', x1', x0, x1, x2, ul, uh, vl, vh.
    exact PreH1.
  }
  
  (* 应用引理获得结论 *)
  specialize (Hlemma Hnocarry).
  
  (* 展开 let 绑定 *)
  unfold w1, w0 in Hlemma.
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul in Hlemma.
  
  (* 转换目标中的 unsigned_last_nbits 为 mod 形式 *)
  repeat (unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296).
  
  (* 展开目标中的变量定义 *)
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul.
  
  (* 现在需要证明两个表达式相等，它们形式上略有不同 *)
  (* Hlemma 中：直接的乘法表达式 *)
  (* 目标中：带有额外 mod 的表达式 *)
  (* 由于 x0, x1, x2, x3 都在 [0, 2^32) 范围内，mod 4294967296 是恒等变换 *)
  
  (* 使用VC前提中的局部range事实获取边界 *)
  pose proof Hu32 as Hu.
  pose proof Hv32 as Hv.
  
  
  (* 证明各部分在范围内 *)
  assert (Hul_bounds: 0 <= Z.land u_pre 65535 < 65536) by (apply land_65535_bounds; assumption).
  assert (Hvl_bounds: 0 <= Z.land v_pre 65535 < 65536) by (apply land_65535_bounds; assumption).
  assert (Huh_bounds: 0 <= Z.shiftr u_pre 16 < 65536) by (apply shiftr_16_bounds; exact Hu).
  assert (Hvh_bounds: 0 <= Z.shiftr v_pre 16 < 65536) by (apply shiftr_16_bounds; exact Hv).
  
  (* 各乘积在 [0, 2^32) 范围内 *)
  assert (Hx0_small: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx1_small: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296) by nia.
  assert (Hx2_small: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx3_small: 0 <= Z.shiftr u_pre 16 * Z.shiftr v_pre 16 < 4294967296) by nia.
  
  (* 简化 mod 操作 *)
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.shiftr v_pre 16) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.shiftr v_pre 16) 4294967296) by lia.
  
  exact Hlemma.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_2 : gmp_umul_ppmm_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_umul_ppmm_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1_split_goal_1 : mpn_mul_1_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1_split_goal_2 : mpn_mul_1_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1_split_goal_3 : mpn_mul_1_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_1 : mpn_mul_1_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_1 : mpn_mul_1_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (HM: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hcl: 0 <= cl < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hlpl: 0 <= lpl < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hres: 0 <= unsigned_last_nbits (lpl + cl) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound. lia. }
  assert (Hsum: lpl + cl = unsigned_last_nbits (lpl + cl) 32).
  { unfold unsigned_last_nbits. apply Z_mod_add_uncarry; unfold UINT_MOD, unsigned_last_nbits in *; lia. }
  rewrite (list_to_Z_concat_r UINT_MOD HM l_rp_2 (unsigned_last_nbits (lpl + cl) 32) Hres).
  rewrite PreH10.
  rewrite (list_to_Z_list_append UINT_MOD HM l i) by (auto; lia).
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  nia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_2 : mpn_mul_1_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply list_within_bound_concat; auto.
  simpl; split; auto.
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (lpl + cl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_3 : mpn_mul_1_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1 : mpn_mul_1_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_1_split_goal_3.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_1 : mpn_mul_1_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (HM: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hcl: 0 <= cl < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hlpl: 0 <= lpl < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hres: 0 <= unsigned_last_nbits (lpl + cl) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound. lia. }
  assert (Hsum: lpl + cl = unsigned_last_nbits (lpl + cl) 32 + UINT_MOD).
  { unfold unsigned_last_nbits. apply Z_mod_add_carry; try (unfold UINT_MOD; lia). exact PreH1. }
  assert (Hdigit: 0 <= Znth i l 0 < UINT_MOD).
  { apply list_within_bound_Znth_bound; auto; lia. }
  assert (Hprod: Znth i l 0 * vl_pre <= (UINT_MOD - 1) * (UINT_MOD - 1)).
  { apply Z.mul_le_mono_nonneg; unfold UINT_MOD in *; lia. }
  assert (Hhigh: hpl <= UINT_MOD - 2) by (unfold UINT_MOD in *; nia).
  assert (Hhighmod: unsigned_last_nbits (1 + hpl) 32 = 1 + hpl).
  { unfold unsigned_last_nbits. apply Z.mod_small. unfold UINT_MOD in *; lia. }
  rewrite Hhighmod.
  rewrite (list_to_Z_concat_r UINT_MOD HM l_rp_2 (unsigned_last_nbits (lpl + cl) 32) Hres).
  rewrite PreH10.
  rewrite (list_to_Z_list_append UINT_MOD HM l i) by (auto; lia).
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  nia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_2 : mpn_mul_1_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply list_within_bound_concat; auto.
  simpl; split; auto.
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (lpl + cl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_3 : mpn_mul_1_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_4 : mpn_mul_1_entail_wit_5_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (1 + hpl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_5 : mpn_mul_1_entail_wit_5_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold unsigned_last_nbits, UINT_MOD.
  pose proof (Z.mod_pos_bound (1 + hpl) (2 ^ 32)).
  lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2 : mpn_mul_1_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_3.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_4.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_5_2_split_goal_5.
Qed.

Lemma proof_of_mpn_mul_1_return_wit_1_split_goal_1 : mpn_mul_1_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq: i = n_pre) by lia.
  rewrite Hi_eq in *.
  rewrite (sublist_self l n_pre) in PreH8 by lia.
  exact PreH8.
Qed.

Lemma proof_of_mpn_mul_1_return_wit_1 : mpn_mul_1_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_mul_1_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_1_split_goal_1 : mpn_sub_1_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  ring_simplify.
  pose proof (list_within_bound_Znth_bound UINT_MOD l i ltac:(lia) PreH9).
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2 (Znth i l 0 - b)).
  rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l i).
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  lia.
  - lia.
  - assumption.
  - unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_1_split_goal_2 : mpn_sub_1_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l i ltac:(lia) PreH9).
  apply list_within_bound_app_single.
  - assumption.
  - unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_1_split_goal_3 : mpn_sub_1_entail_wit_1_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app.
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_1 : mpn_sub_1_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_1_1_split_goal_1.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_1_1_split_goal_2.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_1_1_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_2_split_goal_1 : mpn_sub_1_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Z.mul_1_l.
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
  replace (4294967296 ^ (i + 1)) with (4294967296 * 4294967296 ^ i)
    by (rewrite Z.pow_add_r by lia; ring).
  assert (Heq: list_to_Z 4294967296 data_rp_partial_2 =
    list_to_Z 4294967296 (sublist 0 i l) - b_pre + 4294967296 ^ i) by lia.
  rewrite Heq; ring.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_2_split_goal_2 : mpn_sub_1_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply list_within_bound_app_single.
  - assumption.
  - unfold unsigned_last_nbits, UINT_MOD.
    pose proof (Z.mod_pos_bound (Znth i l 0 - b) (2^32) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_2_split_goal_3 : mpn_sub_1_entail_wit_1_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app.
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_1_2 : mpn_sub_1_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_1_2_split_goal_1.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_1_2_split_goal_2.
  + Goal_apply proof_of_mpn_sub_1_entail_wit_1_2_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_2_1 : mpn_sub_1_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ((Znth 0 l 0 - b_pre) :: nil).
  split_pure_spatial.
  + sep_apply_l_atomic (UIntArray.seg_single rp_pre 0 (Znth 0 l 0 - b_pre)).
    cancel.
    replace (0 + 1) with 1 by lia.
    cancel.
  + repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    - unfold list_within_bound. simpl.
      unfold list_within_bound in PreH4.
      destruct l.
      { simpl. rewrite Zlength_nil in PreH2. lia. }
      { simpl in PreH4. destruct PreH4 as [[Hd_ge Hd_lt] _].
        unfold UINT_MOD in *.
        unfold Znth in PreH1. simpl in PreH1.
        change (Znth 0 (z :: l) 0) with z.
        change (Znth 0 (z :: l) 0) with z in PreH1.
        split; [lia | exact I]. }
    - simpl.
      unfold list_to_Z, sublist.
      simpl.
      destruct l.
      { simpl. rewrite Zlength_nil in PreH2. lia. }
      { simpl. unfold Znth. simpl. lia. }
Qed.

Lemma proof_of_mpn_sub_1_entail_wit_2_2 : mpn_sub_1_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ((unsigned_last_nbits (Znth 0 l 0 - b_pre) 32) :: nil).
  split_pure_spatial.
  + sep_apply_l_atomic
      (UIntArray.seg_single rp_pre 0 (unsigned_last_nbits (Znth 0 l 0 - b_pre) 32)).
    cancel.
    replace (0 + 1) with 1 by lia.
    cancel.
  + repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    - unfold list_within_bound. simpl.
      unfold unsigned_last_nbits, UINT_MOD.
      pose proof (Z.mod_pos_bound (Znth 0 l 0 - b_pre) (2^32)).
      lia.
    - simpl.
      unfold list_to_Z, sublist.
      simpl.
      destruct l.
      { simpl. rewrite Zlength_nil in PreH2. lia. }
      { simpl.
        unfold Znth in *. simpl in *.
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
        lia. }
Qed.

Lemma proof_of_mpn_sub_1_return_wit_1 : mpn_sub_1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq_n: i = n_pre) by lia.
  pose proof PreH11 as Hmain.
  rewrite Hi_eq_n in Hmain.
  rewrite sublist_self in Hmain by lia.
  rewrite PreH10 in Hmain.
  Exists (list_to_Z UINT_MOD data_rp_partial).
  unfold mpd_store_Z.
  Exists l.
  Exists data_rp_partial.
  unfold mpd_store_list.
  rewrite Hi_eq_n.
  rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
  split_pure_spatial.
  - rewrite PreH6.
    rewrite PreH7.
    rewrite Hi_eq_n.
    cancel.
    sep_apply UIntArray.seg_to_full.
    replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + split; assumption.
    + split; [reflexivity | assumption].
Qed.

Lemma proof_of_mpn_sub_1_which_implies_wit_1 : mpn_sub_1_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + reflexivity.
    + destruct H; assumption.
    + destruct H; assumption.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_split_goal_1 : mpn_sub_n_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_split_goal_2 : mpn_sub_n_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1_split_goal_3 : mpn_sub_n_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_1 : mpn_sub_n_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_mpn_sub_n_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_1_split_goal_1 : mpn_sub_n_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  try rewrite Z.mul_0_l; try rewrite Z.sub_0_r.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32)).
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i ltac:(lia) PreH11).
  rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i ltac:(lia) PreH12).
  rewrite Hulb_eq.
  lia.
  rewrite Hulb_eq. unfold UINT_MOD in *. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_1_split_goal_2 : mpn_sub_n_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hbp_cy_no_overflow: Znth i l_b 0 + cy < UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    apply ulb_ge_cy_implies_no_overflow; lia. }
  assert (Hulb_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 = Znth i l_b 0 + cy).
  { unfold unsigned_last_nbits, UINT_MOD in *. rewrite Z.mod_small; lia. }
  apply list_within_bound_app_single.
  - assumption.
  - rewrite Hulb_eq. unfold UINT_MOD in *. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_1_split_goal_3 : mpn_sub_n_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app.
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_1 : mpn_sub_n_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_1_split_goal_1.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_1_split_goal_2.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_2_split_goal_1 : mpn_sub_n_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  rewrite Z.mul_1_l.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2
    (unsigned_last_nbits (Znth i l_a 0 -
      unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32) Hnew_bound).
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
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_2_split_goal_2 : mpn_sub_n_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hnew_bound: 0 <= unsigned_last_nbits
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  apply list_within_bound_app_single; assumption.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_2_split_goal_3 : mpn_sub_n_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app.
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_2 : mpn_sub_n_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_2_split_goal_1.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_2_split_goal_2.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_3_split_goal_1 : mpn_sub_n_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  rewrite Z.mul_1_l.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32)).
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
  rewrite Hulb_bp_eq. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_3_split_goal_2 : mpn_sub_n_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_b i ltac:(lia) PreH12) as Hlb_range.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_a i ltac:(lia) PreH11) as Hla_range.
  assert (Hoverflow: Znth i l_b 0 + cy >= UINT_MOD).
  { unfold UINT_MOD, unsigned_last_nbits in *.
    destruct (Z_lt_dec (Znth i l_b 0 + cy) (2^32)).
    - exfalso. assert (Hulb_eq: (Znth i l_b 0 + cy) mod 2^32 =
        Znth i l_b 0 + cy) by (apply Z.mod_small; lia). lia.
    - lia. }
  assert (Hulb_bp_eq: unsigned_last_nbits (Znth i l_b 0 + cy) 32 =
    Znth i l_b 0 + cy - UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD in *.
    rewrite Z.mod_eq by lia.
    replace ((Znth i l_b 0 + cy) / 2^32) with 1.
    { ring. }
    apply Z.div_unique with (Znth i l_b 0 + cy - 2^32); lia. }
  apply list_within_bound_app_single.
  - assumption.
  - rewrite Hulb_bp_eq. unfold UINT_MOD in *. lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_3_split_goal_3 : mpn_sub_n_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app.
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_3 : mpn_sub_n_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_3_split_goal_1.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_3_split_goal_2.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_3_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_4_split_goal_1 : mpn_sub_n_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  replace (1 + 1) with 2 by lia.
  assert (Hmod_gt0: 0 < UINT_MOD) by (unfold UINT_MOD; lia).
  rewrite (list_to_Z_concat_r UINT_MOD Hmod_gt0 data_rp_partial_2
    (unsigned_last_nbits (Znth i l_a 0 -
      unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32) Hnew_bound).
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_a i ltac:(lia) PreH11).
  rewrite (list_to_Z_list_append UINT_MOD Hmod_gt0 l_b i ltac:(lia) PreH12).
  rewrite Hulb_eq.
  rewrite Hulb_eq in Hulb_range.
  unfold unsigned_last_nbits, UINT_MOD in *.
  assert (Hdiff_neg: Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) < 0) by lia.
  assert (Hdiff_bound: - 4294967296 <
    Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) by lia.
  assert (Hmod_eq: (Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296)) mod 2^32 =
                   Znth i l_a 0 - (Znth i l_b 0 + cy - 4294967296) + 4294967296).
  { symmetry. apply Z.mod_unique with (-1). left. lia. ring. }
  rewrite Hmod_eq.
  replace (i + 1) with (Z.succ i) by lia.
  rewrite Z.pow_succ_r by lia.
  nia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_4_split_goal_2 : mpn_sub_n_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hnew_bound: 0 <= unsigned_last_nbits
    (Znth i l_a 0 - unsigned_last_nbits (Znth i l_b 0 + cy) 32) 32 < UINT_MOD).
  { unfold unsigned_last_nbits, UINT_MOD. apply Z.mod_pos_bound; lia. }
  apply list_within_bound_app_single; assumption.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_4_split_goal_3 : mpn_sub_n_entail_wit_2_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app.
  match goal with
  | [ Hlen : Zlength data_rp_partial_2 = i |- _ ] => rewrite Hlen
  end.
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_sub_n_entail_wit_2_4 : mpn_sub_n_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_4_split_goal_1.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_4_split_goal_2.
  + Goal_apply proof_of_mpn_sub_n_entail_wit_2_4_split_goal_3.
Qed.

Lemma proof_of_mpn_sub_n_return_wit_1 : mpn_sub_n_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq: i = n_pre) by lia.
  pose proof PreH14 as Hmain.
  rewrite Hi_eq in Hmain.
  rewrite (sublist_self l_a n_pre) in Hmain by lia.
  rewrite (sublist_self l_b n_pre) in Hmain by lia.
  rewrite PreH12, PreH13 in Hmain.
  Exists (list_to_Z UINT_MOD data_rp_partial).
  unfold mpd_store_Z, mpd_store_list.
  Exists l_a.
  Exists l_b.
  Exists data_rp_partial.
  rewrite Hi_eq.
  rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
  split_pure_spatial.
  - rewrite PreH6, PreH7, PreH8, Hi_eq.
    cancel.
    sep_apply UIntArray.seg_to_full.
    replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + split; assumption.
    + split; assumption.
    + split; [reflexivity | assumption].
Qed.

Lemma proof_of_mpn_sub_n_which_implies_wit_1 : mpn_sub_n_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l_a.
  Intros l_b.
  Exists l_b.
  Exists l_a.
  rewrite <- H0. rewrite <- H2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + destruct H; assumption.
    + destruct H1; assumption.
Qed.

Lemma proof_of_mpn_sub_return_wit_1 : mpn_sub_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (list_to_Z UINT_MOD (l_r ++ data_r_hi) = val_r + val' * UINT_MOD ^ bn_pre) as Hval_r_out.
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite PreH12, Hdata_r_hi_val, PreH11. reflexivity. }
  assert (list_to_Z UINT_MOD (data_2 ++ data_hi) = val_a_implementation) as Hval_a_out.
  { rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hdata_lo_val, Hdata_hi_val, <- H4, <- PreH15. lia. }
  try rewrite Hval_r_out.
  try rewrite Hval_a_out.
  - dump_pre_spatial; lia.
  - split_pure_spatial.
    + replace (Zlength (l_r ++ data_r_hi)) with an_pre by (rewrite Zlength_app; lia).
    replace (Zlength (data_2 ++ data_hi)) with an_pre by (rewrite Zlength_app; lia).
    cancel.
    + repeat split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
    * rewrite PreH15.
      assert (Hr_eq: val_r = val_a_lo - val_b_implementation + retval_2 * UINT_MOD ^ bn_pre) by lia.
      rewrite Hr_eq.
      assert (Hhi_eq: val' = val_a_hi - retval_2 + retval * UINT_MOD ^ (an_pre - bn_pre)) by lia.
      rewrite Hhi_eq.
      replace (UINT_MOD ^ an_pre) with
        (UINT_MOD ^ bn_pre * UINT_MOD ^ (an_pre - bn_pre)) by
        (rewrite <- Z.pow_add_r; try lia; f_equal; lia).
      lia.
    * split.
      { rewrite list_to_Z_app by exact UINT_MOD_pos.
        rewrite Hdata_lo_val, Hdata_hi_val, <- H4, <- PreH15.
        lia. }
      { apply list_within_bound_concat; auto. }
    * rewrite Zlength_app; lia.
    * split; assumption.
    * split.
      { rewrite list_to_Z_app by exact UINT_MOD_pos.
        rewrite PreH12, Hdata_r_hi_val, PreH11.
        reflexivity. }
      { apply list_within_bound_concat; auto. }
    * rewrite Zlength_app; lia.
Qed.

Lemma proof_of_mpn_sub_return_wit_2 : mpn_sub_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Heq: an_pre = bn_pre) by lia. subst an_pre.
  Exists val_r.
  replace (bn_pre - bn_pre) with 0 by lia.
  sep_apply (mpd_store_Z_zero_to_emp (ap_pre + bn_pre * sizeof(UINT)) val_a_hi).
  Intros.
  assert (Hhi_zero: val_a_hi = 0) by lia.
  assert (Hval_eq: val_a_implementation = val_a_lo) by lia.
  subst val_a_implementation.
  sep_apply (UIntArray_full_to_mpd_store_Z_exact rp_pre bn_pre l_r val_r PreH8 PreH9 PreH10).
  rewrite UIntArray.undef_full_empty.
  rewrite Hhi_zero.
  replace (val_a_lo + 0 * UINT_MOD ^ bn_pre) with val_a_lo by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_1 : mpn_sub_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
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
    + split; [reflexivity |].
      destruct H as [_ Hbound].
      apply list_within_bound_sublist; try lia; try tauto.
    + split; [reflexivity |].
      destruct H as [_ Hbound].
      apply list_within_bound_sublist; try lia; try tauto.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_2_split_goal_spatial : mpn_sub_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply UIntArray.undef_full_split_to_undef_full; try lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_2 : mpn_sub_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_3 : mpn_sub_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l_r.
  Exists l_r.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + reflexivity.
    + destruct H; assumption.
    + destruct H; assumption.
Qed.

Lemma proof_of_mpz_clear_return_wit_2_split_goal_spatial : mpz_clear_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst cap_2.
  assert (Hsize_abs: Zabs size_2 = 0) by lia.
  rewrite Hsize_abs.
  rewrite UIntArray.undef_seg_empty.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  assert (data = nil).
  { apply Zlength_nil_inv. lia. }
  subst data.
  rewrite UIntArray.full_empty.
  cancel.
  normalize.
  cancel.
  Intros_p Hlen_nil.
  cancel.
Qed.

Lemma proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_clear_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_split_goal_spatial : mpz_realloc_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hold_zero: old = 0) by lia.
  subst old.
  change (Zabs 0) with 0 in *.
  rewrite PreH3.
  sep_apply (UIntArray.undef_full_to_undef_seg retval); try lia.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l.
  assert (l = nil).
  { apply Zlength_nil_inv. lia. }
  subst l.
  destruct H as [Hval [Hlast Hbound]].
  simpl in Hval.
  assert (Hn_abs_zero: Zabs n = 0) by lia.
  rewrite Hn_abs_zero in *.
  rewrite UIntArray.full_empty.
  rewrite PreH10.
  rewrite UIntArray.undef_seg_empty.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  try rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - cancel.
    normalize.
    Intros.
    cancel.
  - repeat split_pures; dump_pre_spatial; simpl; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_return_wit_3_split_goal_1 : mpz_realloc_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_3_split_goal_spatial : mpz_realloc_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_3 : mpz_realloc_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_realloc_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_mpz_realloc_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_return_wit_4_split_goal_1 : mpz_realloc_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_4 : mpz_realloc_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_realloc_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_2_pure_split_goal_1 : mpz_realloc_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_2_pure : mpz_realloc_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure_split_goal_1 : mpz_realloc_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pure_split_goal_1 : mpz_realloc_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure_split_goal_1 : mpz_realloc_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_1 : mrz_realloc_if_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_2 : mrz_realloc_if_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_spatial : mrz_realloc_if_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (Z.max n_pre cap) with cap by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_1 : mrz_realloc_if_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_2 : mrz_realloc_if_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_spatial : mrz_realloc_if_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (Z.max n_pre cap) with (Z.max n_pre 1) by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpz_sgn_return_wit_1_split_goal_1 : mpz_sgn_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold same_sign in PreH3.
  destruct PreH3 as [[_ Hsize_nonneg] | [Hn_neg _]]; [lia | exact Hn_neg].
Qed.

Lemma proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sgn_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpz_sgn_return_wit_2_split_goal_1 : mpz_sgn_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z.
  Exists ptr size cap.
  replace (Zabs size) with size by lia.
  subst size.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs n)).
  Intros.
  assert (n = 0) by lia.
  replace (Zabs n) with n by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_sgn_return_wit_3_split_goal_1 : mpz_sgn_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z.
  Exists ptr size cap.
  replace (Zabs size) with size by lia.
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
    (Zabs n) size ltac:(lia)).
  Intros.
  assert (Hn_pos: n > 0).
  { unfold same_sign in PreH3.
    match goal with
    | [ Habs_pos : Zabs n > 0 |- _ ] =>
        destruct PreH3 as [[Hn_nonneg _] | [_ Hsize_neg]]; lia
    end. }
  replace (Zabs n) with n by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_safety_wit_1_split_goal_1 : mpz_abs_add_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD aptr (Zabs n_new) an).
  Intros_p Hrange.
  match goal with
  | H : 0 <= an <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpz_abs_add_safety_wit_1_split_goal_2 : mpz_abs_add_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_safety_wit_1 : mpz_abs_add_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_1_split_goal_1 : mpz_abs_add_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_1_split_goal_2 : mpz_abs_add_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply perm_swap.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_1 : mpz_abs_add_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_1_1_split_goal_1 l m n size cap retval size_2 cap_2 retval_2 size_3 cap_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_1_1_split_goal_2 l m n a_pre b_pre size cap retval size_2 cap_2 retval_2 size_3 cap_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_2_split_goal_1 : mpz_abs_add_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_2_split_goal_2 : mpz_abs_add_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_2 : mpz_abs_add_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_1_2_split_goal_1 l m n size cap retval size_2 cap_2 retval_2 size_3 cap_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_1_2_split_goal_2 l m n a_pre b_pre size cap retval size_2 cap_2 retval_2 size_3 cap_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2 : mpz_abs_add_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (Z.max (Z.max (an + 1) 1) rcap_2)
    with (Z.max (an + 1) rcap_2) by lia.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l) (Zabs rsize_2) an
    (Z.max (an + 1) rcap_2)); try lia.
  Intros_p Hcompact.
  Exists bptr_2; Exists aptr_2; Exists retval; Exists z__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists bcap_2; Exists acap_2.
  Exists bsize_2; Exists asize_2; Exists n_new_2; Exists m_new_2.
  split_pure_spatial.
  - replace (Z.max (Z.max (an + 1) 1) rcap_2)
      with (Z.max (an + 1) rcap_2) by lia.
    cancel (UIntArray.undef_full retval an).
    cancel (UIntArray.undef_seg retval an
      (Z.max (an + 1) rcap_2)).
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_1_split_goal_spatial : mpz_abs_add_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (mpn_add_ret_0_or_1 aptr bptr rp (Zabs n_new) (Zabs m_new) val_r_out an bn retval
    ltac:(lia) ltac:(lia)) as Hadd_ret.
  prop_apply_p Hadd_ret.
  Intros_p Habs_return_1.
  prop_apply_p (store_int_range (&( r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) r__mp_alloc).
  Intros_p Habs_return_2.
  match goal with
  | Halloc : Int.min_signed <= r__mp_alloc <= Int.max_signed,
    Hz : r__mp_alloc = Z.max (Z.max (an + 1) 1) rcap |- _ =>
      assert (Han_int : an <= Int.max_signed) by (rewrite Hz in Halloc; lia)
  end.
  match goal with
  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval
  end.
  - assert (Hsize_ret : signed_last_nbits (unsigned_last_nbits an 32 + 0) 32 = an).
    {
      match goal with
      | Hc : is_compact_Z UINT_MOD (Zabs n_new) an |- _ =>
          pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an Hc)
            as [Han_nonneg _]
      end.
      assert (Han_u32 : 0 <= an < 2 ^ 32)
        by (change (2 ^ 32) with 4294967296; change Int.max_signed with 2147483647 in Han_int; lia).
      assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))
        by (change (2 ^ (32 - 1)) with 2147483648; change Int.max_signed with 2147483647 in Han_int; lia).
      rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
      replace (an + 0) with an by lia.
      rewrite signed_last_nbits_eq.
      2:{ lia. }
      2:{ exact Han_s32. }
      lia.
    }
    prop_apply_p (mpd_store_Z_bound rp val_r_out an).
    Intros_p Habs_return_3.
    assert (Hcompact_r : is_compact_Z UINT_MOD val_r_out an).
    {
      replace val_r_out with (Zabs n_new + Zabs m_new) by lia.
      replace an with (Z.max an bn) by lia.
      eapply is_compact_Z_add_0.
      - eassumption.
      - eassumption.
      - rewrite Z.max_l by lia; lia.
    }
    match goal with
    | Hperm : Permutation (Prod2 a n_new :: Prod2 b m_new :: nil)
                          (Prod2 a_pre n :: Prod2 b_pre m :: nil) |- _ =>
        pose proof (Permutation_length_2 Hperm) as HP
    end.
    destruct HP as [[Hpair1 Hpair2] | [Hpair1 Hpair2]].
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs an) with an by lia.
      replace (Zabs (Zabs n_new + Zabs m_new)) with (Zabs n_new + Zabs m_new) by lia.
      replace (Zabs n_new + Zabs m_new) with val_r_out by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp val_r_out an);
        try assumption.
      sep_apply (store_uint_undef_store_uint (rp + an * sizeof ( UINT )) 0);
        try lia.
      sep_apply (UIntArray.undef_seg_single rp an); try lia.
      sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
      rewrite PreH29, PreH30.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try (unfold same_sign; left; lia); lia.
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs an) with an by lia.
      replace (Zabs (Zabs m_new + Zabs n_new)) with (Zabs m_new + Zabs n_new) by lia.
      replace (Zabs m_new + Zabs n_new) with val_r_out by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp val_r_out an);
        try assumption.
      sep_apply (store_uint_undef_store_uint (rp + an * sizeof ( UINT )) 0);
        try lia.
      sep_apply (UIntArray.undef_seg_single rp an); try lia.
      sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
      rewrite PreH29, PreH30.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try (unfold same_sign; left; lia); lia.
  - assert (Han1 : an + 1 <= Int.max_signed).
    {
      match goal with
      | Halloc : Int.min_signed <= r__mp_alloc <= Int.max_signed,
        Hz : r__mp_alloc = Z.max (Z.max (an + 1) 1) rcap |- _ =>
          rewrite Hz in Halloc; lia
      end.
    }
    assert (Hsize_ret : signed_last_nbits (unsigned_last_nbits an 32 + 1) 32 = an + 1).
    {
      match goal with
      | Hc : is_compact_Z UINT_MOD (Zabs n_new) an |- _ =>
          pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an Hc)
            as [Han_nonneg _]
      end.
      assert (Han_u32 : 0 <= an < 2 ^ 32)
        by (change (2 ^ 32) with 4294967296; change Int.max_signed with 2147483647 in Han_int; lia).
      assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))
        by (change (2 ^ (32 - 1)) with 2147483648; change Int.max_signed with 2147483647 in Han1; lia).
      rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
      rewrite signed_last_nbits_eq.
      2:{ lia. }
      2:{ exact Han1_s32. }
      lia.
    }
    match goal with
    | Hperm : Permutation (Prod2 a n_new :: Prod2 b m_new :: nil)
                          (Prod2 a_pre n :: Prod2 b_pre m :: nil) |- _ =>
        pose proof (Permutation_length_2 Hperm) as HP
    end.
    destruct HP as [[Hpair1 Hpair2] | [Hpair1 Hpair2]].
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs (an + 1)) with (an + 1) by lia.
      replace (Zabs (Zabs n_new + Zabs m_new)) with (Zabs n_new + Zabs m_new) by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_append_one_compact rp val_r_out an).
      replace (val_r_out + UINT_MOD ^ an) with (Zabs n_new + Zabs m_new) by lia.
      rewrite PreH29, PreH30.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try lia.
        unfold same_sign; left.
        pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an PreH17)
          as [Han_nonneg _].
        pose proof (Z.pow_pos_nonneg UINT_MOD an UINT_MOD_pos (Z.ge_le _ _ Han_nonneg)).
        lia.
    + unfold Prod2 in Hpair1, Hpair2.
      inversion Hpair1; inversion Hpair2; subst a_pre n b_pre m; clear Hpair1 Hpair2.
      unfold store_Z at 1.
      Exists bptr; Exists bsize; Exists bcap.
      unfold store_Z at 1.
      Exists aptr; Exists asize; Exists acap.
      unfold store_Z_remain_size.
      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).
      rewrite Hsize_ret.
      replace (Zabs (an + 1)) with (an + 1) by lia.
      replace (Zabs (Zabs m_new + Zabs n_new)) with (Zabs m_new + Zabs n_new) by lia.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);
        try assumption.
      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);
        try assumption.
      sep_apply (mpd_store_Z_append_one_compact rp val_r_out an).
      replace (val_r_out + UINT_MOD ^ an) with (Zabs m_new + Zabs n_new) by lia.
      rewrite PreH29, PreH30.
      replace (Zabs asize) with an by lia.
      replace (Zabs bsize) with bn by lia.
      split_pure_spatial.
      * cancel.
      * split_pures; dump_pre_spatial.
        all: try assumption; try lia.
        unfold same_sign; left.
        pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an PreH17)
          as [Han_nonneg _].
        pose proof (Z.pow_pos_nonneg UINT_MOD an UINT_MOD_pos (Z.ge_le _ _ Han_nonneg)).
        lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_1 : mpz_abs_add_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_2_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (Z.abs_le size).
  destruct (Z_le_gt_dec 0 size); rewrite ?Z.abs_eq, ?Z.abs_neq in * by lia; lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_2_pure : mpz_abs_add_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_4_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof (Z.abs_le size).
  destruct (Z_le_gt_dec 0 size); rewrite ?Z.abs_eq, ?Z.abs_neq in * by lia; lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_4_pure : mpz_abs_add_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_7_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_7_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD aptr (Zabs n_new) an).
  Intros_p Hrange.
  match goal with
  | H : 0 <= an <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_7_pure : mpz_abs_add_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_8_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_8_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_8_pure : mpz_abs_add_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_1_split_goal_1 : mpz_abs_sub_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof (Z.abs_nonneg size_3).
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_1 : mpz_abs_sub_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_1_split_goal_1 l m n size cap retval size_2 cap_2 retval_2 retval_3 size_3 cap_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_2 : mpz_abs_sub_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec an 0) as [Han0 | Han0].
  - rewrite Han0.
    prop_apply_p (mpd_store_Z_compact_zero UINT_MOD a__mp_d_2 (Zabs n)).
    Intros_p Hzero.
    pose proof (Z.abs_nonneg m).
    exfalso. lia.
  - assert (Han : 0 < an) by
      (rewrite PreH9; pose proof (Z.abs_nonneg a__mp_size_2); lia).
    replace (Z.max (Z.max an 1) rcap_2) with (Z.max an rcap_2) by lia.
    sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
      retval (Zabs l) (Zabs rsize_2) an (Z.max an rcap_2)); try lia.
    Intros_p Hcompact.
    Exists b__mp_d_2 a__mp_d_2 retval z__mp_alloc rcap_2 rsize_2.
    Exists a__mp_alloc_2 a__mp_size_2 b__mp_alloc_2 b__mp_size_2.
    split_pure_spatial.
    + replace (Z.max (Z.max an 1) rcap_2) with (Z.max an rcap_2) by lia.
      cancel (UIntArray.undef_full retval an).
      cancel (UIntArray.undef_seg retval an (Z.max an rcap_2)).
      repeat cancel.
    + split_pures; dump_pre_spatial;
        try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_3_split_goal_1 : mpz_abs_sub_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof (Z.abs_nonneg size_3).
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_3 : mpz_abs_sub_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_3_split_goal_1 l m n size cap retval size_2 cap_2 retval_2 retval_3 size_3 cap_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_4 : mpz_abs_sub_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec bn 0) as [Hbn0 | Hbn0].
  - rewrite Hbn0.
    prop_apply_p (mpd_store_Z_compact_zero UINT_MOD b__mp_d_2 (Zabs m)).
    Intros_p Hzero.
    pose proof (Z.abs_nonneg n).
    exfalso. lia.
  - assert (Hbn : 0 < bn) by
      (rewrite PreH7; pose proof (Z.abs_nonneg b__mp_size_2); lia).
    replace (Z.max (Z.max bn 1) rcap_2) with (Z.max bn rcap_2) by lia.
    sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
      retval (Zabs l) (Zabs rsize_2) bn (Z.max bn rcap_2)); try lia.
    Intros_p Hcompact.
    Exists b__mp_d_2 a__mp_d_2 retval z__mp_alloc rcap_2 rsize_2.
    Exists a__mp_alloc_2 a__mp_size_2 b__mp_alloc_2 b__mp_size_2.
    split_pure_spatial.
    + replace (Z.max (Z.max bn 1) rcap_2) with (Z.max bn rcap_2) by lia.
      cancel (UIntArray.undef_full retval bn).
      cancel (UIntArray.undef_seg retval bn (Z.max bn rcap_2)).
      repeat cancel.
    + split_pures; dump_pre_spatial;
        try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_1_split_goal_spatial : mpz_abs_sub_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH8, PreH5.
  replace (Zabs n - Zabs m) with 0 by lia.
  sep_apply (store_Z_to_store_Z_remain_size_zero r_pre l).
  cancel.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_1 : mpz_abs_sub_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_2_split_goal_spatial : mpz_abs_sub_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (is_compact_Z_mono_size (Zabs m) (Zabs n) bn an ltac:(lia) PreH8 PreH9)
    as Hbn_ge_an.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n) an PreH9)
    as [Han_nonneg _].
  pose proof (mpn_sub_ret_0 b__mp_d a__mp_d rp
    (Zabs m) (Zabs n) val_r_out bn an retval retval_2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsub_ret.
  prop_apply_p Hsub_ret.
  Intros_p Habs_return_4.
  subst retval_2.
  prop_apply_p (mpd_store_Z_to_is_compact_Z rp val_r_out retval).
  Intros_p Habs_return_5.
  assert (Hretval_pos : retval > 0).
  { apply (is_compact_Z_positive_size val_r_out); try assumption; lia. }
  unfold store_Z_remain_size.
  Exists rp; Exists rsize; Exists r__mp_alloc.
  replace (Zabs a__mp_size) with an by lia.
  replace (Zabs b__mp_size) with bn by lia.
  replace (Zabs (- retval)) with retval by lia.
  assert (Habs_mn: Zabs (Zabs n - Zabs m) = Zabs m - Zabs n) by lia.
  rewrite Habs_mn.
  replace val_r_out with (Zabs m - Zabs n) by lia.
  rewrite PreH23, PreH24.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact b__mp_d (Zabs m) bn PreH8).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact a__mp_d (Zabs n) an PreH9).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold same_sign; right; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_2 : mpz_abs_sub_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_3_split_goal_spatial : mpz_abs_sub_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (is_compact_Z_mono_size (Zabs n) (Zabs m) an bn ltac:(lia) PreH9 PreH8)
    as Han_ge_bn.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs m) bn PreH8)
    as [Hbn_nonneg _].
  pose proof (mpn_sub_ret_0 a__mp_d b__mp_d rp
    (Zabs n) (Zabs m) val_r_out an bn retval retval_2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsub_ret.
  prop_apply_p Hsub_ret.
  Intros_p Habs_return_6.
  subst retval_2.
  prop_apply_p (mpd_store_Z_to_is_compact_Z rp val_r_out retval).
  Intros_p Habs_return_7.
  assert (Hretval_pos : retval > 0).
  { apply (is_compact_Z_positive_size val_r_out); try assumption; lia. }
  unfold store_Z_remain_size.
  Exists rp; Exists rsize; Exists r__mp_alloc.
  replace (Zabs a__mp_size) with an by lia.
  replace (Zabs b__mp_size) with bn by lia.
  assert (Habs_diff_nm: Zabs (Zabs n - Zabs m) = Zabs n - Zabs m) by lia.
  rewrite Habs_diff_nm.
  replace val_r_out with (Zabs n - Zabs m) by lia.
  rewrite PreH22, PreH23.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact a__mp_d (Zabs n) an PreH9).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact b__mp_d (Zabs m) bn PreH8).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
  replace (Zabs retval) with retval by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold same_sign; left; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_3 : mpz_abs_sub_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_2_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_2_pure : mpz_abs_sub_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_4_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_4_pure : mpz_abs_sub_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try dump_pre_spatial.
  all: pose proof (Z.abs_nonneg size).
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try dump_pre_spatial.
  all: pose proof (Z.abs_nonneg size_2).
  all: lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_pure : mpz_abs_sub_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_6_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_6_pure : mpz_abs_sub_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_6_pure_split_goal_1 l m n r_pre a_pre b_pre rptr rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc a__mp_d b__mp_d).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (mpd_store_Z_to_is_compact_Z a__mp_d (Zabs n) an).
  Intros_p Ha.
  prop_apply_p (mpd_store_Z_to_is_compact_Z b__mp_d (Zabs m) bn).
  Intros_p Hb.
  dump_pre_spatial.
  eapply (is_compact_Z_mono_size (Zabs n) (Zabs m)); eauto; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (mpd_store_Z_to_is_compact_Z a__mp_d (Zabs n) an).
  Intros_p Ha.
  prop_apply_p (mpd_store_Z_to_is_compact_Z b__mp_d (Zabs m) bn).
  Intros_p Hb.
  dump_pre_spatial.
  eapply (is_compact_Z_positive_size (Zabs n)); eauto.
  pose proof (Z.abs_nonneg m); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_pure_split_goal_3 : mpz_abs_sub_partial_solve_wit_7_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_pure : mpz_abs_sub_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_7_pure_split_goal_1 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_7_pure_split_goal_2 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_7_pure_split_goal_3 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_pure : mpz_abs_sub_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_8_pure_split_goal_1 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d val_r_out retval).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9_pure : mpz_abs_sub_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_9_pure_split_goal_1 l m n r_pre a_pre b_pre rptr rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc a__mp_d b__mp_d).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_10_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (mpd_store_Z_to_is_compact_Z a__mp_d (Zabs n) an).
  Intros_p Ha.
  prop_apply_p (mpd_store_Z_to_is_compact_Z b__mp_d (Zabs m) bn).
  Intros_p Hb.
  dump_pre_spatial.
  eapply (is_compact_Z_mono_size (Zabs m) (Zabs n)); eauto; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_10_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (mpd_store_Z_to_is_compact_Z a__mp_d (Zabs n) an).
  Intros_p Ha.
  prop_apply_p (mpd_store_Z_to_is_compact_Z b__mp_d (Zabs m) bn).
  Intros_p Hb.
  dump_pre_spatial.
  eapply (is_compact_Z_positive_size (Zabs m)); eauto.
  pose proof (Z.abs_nonneg n); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_10_pure_split_goal_3 : mpz_abs_sub_partial_solve_wit_10_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_10_pure : mpz_abs_sub_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_10_pure_split_goal_1 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_10_pure_split_goal_2 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_10_pure_split_goal_3 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_pure : mpz_abs_sub_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_11_pure_split_goal_1 l m n r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d val_r_out retval).
Qed.

Lemma proof_of_mpz_add_safety_wit_3_split_goal_1 : mpz_add_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z_remain_size.
  Intros rp oldsz rcap.

  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros_p Hcap.
  dump_pre_spatial.

  pose proof (Z.abs_spec retval) as Habs.
  change (retval <> -2147483648).
  change (-2147483648 <= rcap <= 2147483647) in Hcap.
  lia.
Qed.

Lemma proof_of_mpz_add_safety_wit_3 : mpz_add_safety_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_add_safety_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpz_add_safety_wit_5_split_goal_1 : mpz_add_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z_remain_size.
  Intros rp oldsz rcap.

  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros_p Hcap.
  dump_pre_spatial.

  pose proof (Z.abs_spec retval) as Habs.
  change (retval <> -2147483648).
  change (-2147483648 <= rcap <= 2147483647) in Hcap.
  lia.
Qed.

Lemma proof_of_mpz_add_safety_wit_5 : mpz_add_safety_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_add_safety_wit_5_split_goal_1.
Qed.

Lemma proof_of_mpz_add_return_wit_1_split_goal_1 : mpz_add_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n + Z.abs m = n + m).
  { assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
    assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
    rewrite (Z.abs_eq n), (Z.abs_eq m) by lia.
    lia. }
  dump_pre_spatial.
  rewrite Hidentity in *.
  unfold same_sign in *.
  lia.
Qed.

Lemma proof_of_mpz_add_return_wit_1_split_goal_spatial : mpz_add_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n + Z.abs m = n + m).
  { assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
    assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
    rewrite (Z.abs_eq n), (Z.abs_eq m) by lia.
    lia. }
  rewrite Hidentity.
  rewrite ?Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_add_return_wit_1 : mpz_add_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_add_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mpz_add_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpz_add_return_wit_2_split_goal_1 : mpz_add_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_add_return_wit_2_split_goal_2 : mpz_add_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n + Z.abs m = -(n + m)).
  { assert (Hn : n < 0) by (unfold same_sign in *; lia).
    assert (Hm : m < 0) by (unfold same_sign in *; lia).
    rewrite (Z.abs_neq n), (Z.abs_neq m) by lia.
    lia. }
  rewrite Hidentity in *.
  destruct (Z.eq_dec retval 0) as [Hz|Hnz].
  - subst retval. simpl Z.abs.
    prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Z.abs (-(n+m)))).
    Intros_p Hzero.
    dump_pre_spatial.
    pose proof (Z.abs_spec (-(n+m))).
    unfold same_sign in *. lia.
  - prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr_2
        (Z.abs (-(n+m))) (Z.abs retval) ltac:(pose proof (Z.abs_pos retval); lia)).
    Intros_p Hpositive.
    dump_pre_spatial.
    pose proof (Z.abs_spec (-(n+m))).
    unfold same_sign in *. lia.
Qed.

Lemma proof_of_mpz_add_return_wit_2_split_goal_spatial : mpz_add_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n + Z.abs m = -(n + m)).
  { assert (Hn : n < 0) by (unfold same_sign in *; lia).
    assert (Hm : m < 0) by (unfold same_sign in *; lia).
    rewrite (Z.abs_neq n), (Z.abs_neq m) by lia.
    lia. }
  rewrite Hidentity.
  rewrite ?Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_add_return_wit_2 : mpz_add_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_add_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mpz_add_return_wit_2_split_goal_1.
  - Goal_apply proof_of_mpz_add_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpz_add_return_wit_3_split_goal_1 : mpz_add_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n - Z.abs m = n + m).
  { assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
    assert (Hm : m < 0) by (unfold same_sign in *; lia).
    rewrite (Z.abs_eq n), (Z.abs_neq m) by lia.
    lia. }
  dump_pre_spatial.
  rewrite Hidentity in *.
  unfold same_sign in *.
  lia.
Qed.

Lemma proof_of_mpz_add_return_wit_3_split_goal_spatial : mpz_add_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n - Z.abs m = n + m).
  { assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
    assert (Hm : m < 0) by (unfold same_sign in *; lia).
    rewrite (Z.abs_eq n), (Z.abs_neq m) by lia.
    lia. }
  rewrite Hidentity.
  rewrite ?Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_add_return_wit_3 : mpz_add_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_add_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_mpz_add_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpz_add_return_wit_4_split_goal_1 : mpz_add_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_add_return_wit_4_split_goal_2 : mpz_add_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n - Z.abs m = -(n + m)).
  { assert (Hn : n < 0) by (unfold same_sign in *; lia).
    assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
    rewrite (Z.abs_neq n), (Z.abs_eq m) by lia.
    lia. }
  rewrite Hidentity in *.
  destruct (Z.eq_dec retval 0) as [Hz|Hnz].
  - subst retval. simpl Z.abs.
    prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Z.abs (-(n+m)))).
    Intros_p Hzero.
    dump_pre_spatial.
    pose proof (Z.abs_spec (-(n+m))).
    unfold same_sign in *. lia.
  - prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr_2
        (Z.abs (-(n+m))) (Z.abs retval) ltac:(pose proof (Z.abs_pos retval); lia)).
    Intros_p Hpositive.
    dump_pre_spatial.
    pose proof (Z.abs_spec (-(n+m))).
    unfold same_sign in *. lia.
Qed.

Lemma proof_of_mpz_add_return_wit_4_split_goal_spatial : mpz_add_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.lxor_nonneg size size_2) as Hxor.
  assert (Hidentity : Z.abs n - Z.abs m = -(n + m)).
  { assert (Hn : n < 0) by (unfold same_sign in *; lia).
    assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
    rewrite (Z.abs_neq n), (Z.abs_eq m) by lia.
    lia. }
  rewrite Hidentity.
  rewrite ?Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_add_return_wit_4 : mpz_add_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_add_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_mpz_add_return_wit_4_split_goal_1.
  - Goal_apply proof_of_mpz_add_return_wit_4_split_goal_2.
Qed.

Lemma proof_of_mpz_sub_safety_wit_3_split_goal_1 : mpz_sub_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z_remain_size.
  Intros rp old_size rcap.
  prop_apply_p (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros_p Hcap.
  dump_pre_spatial.
  change (-2147483648 <= rcap <= 2147483647) in Hcap.
  destruct (Z.abs_spec retval) as [[Hsgn Habs] | [Hsgn Habs]]; lia.
Qed.

Lemma proof_of_mpz_sub_safety_wit_3 : mpz_sub_safety_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sub_safety_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_safety_wit_5_split_goal_1 : mpz_sub_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z_remain_size.
  Intros rp old_size rcap.
  prop_apply_p (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros_p Hcap.
  dump_pre_spatial.
  change (-2147483648 <= rcap <= 2147483647) in Hcap.
  destruct (Z.abs_spec retval) as [[Hsgn Habs] | [Hsgn Habs]]; lia.
Qed.

Lemma proof_of_mpz_sub_safety_wit_5 : mpz_sub_safety_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sub_safety_wit_5_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_return_wit_1_split_goal_1 : mpz_sub_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 >= 0 |- _ => pose proof (lxor_nonneg_implies_same_sign size size_2 H) as Hxor end.
  assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
  assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n - Z.abs m) = n-m).
  { rewrite (Z.abs_eq n) by lia. rewrite (Z.abs_eq m) by lia. lia. }
  rewrite Hmag in *.
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_mpz_sub_return_wit_1_split_goal_spatial : mpz_sub_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 >= 0 |- _ => pose proof (lxor_nonneg_implies_same_sign size size_2 H) as Hxor end.
  assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
  assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n - Z.abs m) = n-m).
  { rewrite (Z.abs_eq n) by lia. rewrite (Z.abs_eq m) by lia. lia. }
  rewrite Hmag.
  cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_1 : mpz_sub_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_sub_return_wit_1_split_goal_spatial m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
  - Goal_apply (proof_of_mpz_sub_return_wit_1_split_goal_1 m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
Qed.

Lemma proof_of_mpz_sub_return_wit_2_split_goal_1 : mpz_sub_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).

Qed.

Lemma proof_of_mpz_sub_return_wit_2_split_goal_2 : mpz_sub_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 >= 0 |- _ => pose proof (lxor_nonneg_implies_same_sign size size_2 H) as Hxor end.
  assert (Hn : n < 0) by (unfold same_sign in *; lia).
  assert (Hm : m < 0) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n - Z.abs m) = -(n-m)).
  { rewrite (Z.abs_neq n) by lia. rewrite (Z.abs_neq m) by lia. lia. }
  prop_apply_p (mpd_store_Z_to_is_compact_Z ptr_2 (Z.abs (Z.abs n - Z.abs m)) (Z.abs retval)).
  Intros_p Hcompact.
  dump_pre_spatial.
  replace (n-m) with (-(Z.abs n - Z.abs m)) by lia.
  apply same_sign_opp_compact_abs; assumption.
Qed.

Lemma proof_of_mpz_sub_return_wit_2_split_goal_spatial : mpz_sub_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 >= 0 |- _ => pose proof (lxor_nonneg_implies_same_sign size size_2 H) as Hxor end.
  assert (Hn : n < 0) by (unfold same_sign in *; lia).
  assert (Hm : m < 0) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n - Z.abs m) = -(n-m)).
  { rewrite (Z.abs_neq n) by lia. rewrite (Z.abs_neq m) by lia. lia. }
  rewrite Hmag.
  rewrite !Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_2 : mpz_sub_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_sub_return_wit_2_split_goal_spatial m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
  - Goal_apply (proof_of_mpz_sub_return_wit_2_split_goal_1 m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
  - Goal_apply (proof_of_mpz_sub_return_wit_2_split_goal_2 m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
Qed.

Lemma proof_of_mpz_sub_return_wit_3_split_goal_1 : mpz_sub_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 < 0 |- _ => pose proof (lxor_negative_implies_opposite_signs_simple size size_2 H) as Hxor end.
  assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
  assert (Hm : m < 0) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n + Z.abs m) = n-m).
  { rewrite (Z.abs_eq n) by lia. rewrite (Z.abs_neq m) by lia. lia. }
  rewrite Hmag in *.
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_mpz_sub_return_wit_3_split_goal_spatial : mpz_sub_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 < 0 |- _ => pose proof (lxor_negative_implies_opposite_signs_simple size size_2 H) as Hxor end.
  assert (Hn : 0 <= n) by (unfold same_sign in *; lia).
  assert (Hm : m < 0) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n + Z.abs m) = n-m).
  { rewrite (Z.abs_eq n) by lia. rewrite (Z.abs_neq m) by lia. lia. }
  rewrite Hmag.
  cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_3 : mpz_sub_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_sub_return_wit_3_split_goal_spatial m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
  - Goal_apply (proof_of_mpz_sub_return_wit_3_split_goal_1 m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
Qed.

Lemma proof_of_mpz_sub_return_wit_4_split_goal_1 : mpz_sub_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).

Qed.

Lemma proof_of_mpz_sub_return_wit_4_split_goal_2 : mpz_sub_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 < 0 |- _ => pose proof (lxor_negative_implies_opposite_signs_simple size size_2 H) as Hxor end.
  assert (Hn : n < 0) by (unfold same_sign in *; lia).
  assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n + Z.abs m) = -(n-m)).
  { rewrite (Z.abs_neq n) by lia. rewrite (Z.abs_eq m) by lia. lia. }
  prop_apply_p (mpd_store_Z_to_is_compact_Z ptr_2 (Z.abs (Z.abs n + Z.abs m)) (Z.abs retval)).
  Intros_p Hcompact.
  dump_pre_spatial.
  replace (n-m) with (-(Z.abs n + Z.abs m)) by lia.
  apply same_sign_opp_compact_abs; assumption.
Qed.

Lemma proof_of_mpz_sub_return_wit_4_split_goal_spatial : mpz_sub_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Z.lxor size size_2 < 0 |- _ => pose proof (lxor_negative_implies_opposite_signs_simple size size_2 H) as Hxor end.
  assert (Hn : n < 0) by (unfold same_sign in *; lia).
  assert (Hm : 0 <= m) by (unfold same_sign in *; lia).
  assert (Hmag : (Z.abs n + Z.abs m) = -(n-m)).
  { rewrite (Z.abs_neq n) by lia. rewrite (Z.abs_eq m) by lia. lia. }
  rewrite Hmag.
  rewrite !Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_4 : mpz_sub_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_sub_return_wit_4_split_goal_spatial m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
  - Goal_apply (proof_of_mpz_sub_return_wit_4_split_goal_1 m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
  - Goal_apply (proof_of_mpz_sub_return_wit_4_split_goal_2 m n b_pre size cap size_2 cap_2 retval ptr size_3 cap_3 ptr_2 cap_4).
Qed.

Lemma proof_of_mpn_sub_implementation_entail_default : mpn_sub_implementation_entail_default.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists val_a val_b.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
    Intros_r retval.
    apply_sepcon_adjoint.
    Intros val_r.
    Exists val_r.
    split_pure_spatial.
    + sepcon_assoc_change. cancel.
    + split_pures; dump_pre_spatial; assumption.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpn_sub_n_implementation_entail_default : mpn_sub_n_implementation_entail_default.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists val_a val_b.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
    Intros_r retval.
    apply_sepcon_adjoint.
    Intros val_r.
    Exists val_r.
    split_pure_spatial.
    + sepcon_assoc_change; cancel.
    + split_pures; dump_pre_spatial; assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpn_add_n_implementation_entail_default : mpn_add_n_implementation_entail_default.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists val_a val_b.
  split_pure_spatial.
  - cancel (mpd_store_Z UINT_MOD ap_pre val_a n_pre).
    cancel (mpd_store_Z UINT_MOD bp_pre val_b n_pre).
    cancel (UIntArray.undef_full rp_pre n_pre).
    Intros_r retval.
    apply_sepcon_adjoint.
    asrt_simpl.
    reflexivity.
  - split_pures; dump_pre_spatial; auto.
Qed.

