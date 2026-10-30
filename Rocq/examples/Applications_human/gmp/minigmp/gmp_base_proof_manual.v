From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_base_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_base_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_base_lib.
Local Open Scope sac.

Lemma proof_of_gmp_abs_return_wit_1_split_goal_1 : gmp_abs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_gmp_abs_return_wit_1 : gmp_abs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_abs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gmp_abs_return_wit_2_split_goal_1 : gmp_abs_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_gmp_abs_return_wit_2 : gmp_abs_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_abs_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_gmp_max_return_wit_1_split_goal_1 : gmp_max_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_gmp_max_return_wit_1 : gmp_max_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_max_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gmp_max_return_wit_2_split_goal_1 : gmp_max_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_gmp_max_return_wit_2 : gmp_max_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_max_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1_split_goal_1 : mpn_cmp_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (n_pre - 1 + 1) with n_pre by lia.
  rewrite Zsublist_nil; try lia.
  rewrite Zsublist_nil; try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_2_split_goal_1 : mpn_cmp_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  replace (n - 1 + 1) with n by lia.
  assert (Heq : sublist n n_pre l1 = sublist n n_pre l2).
  { rewrite (sublist_split n n_pre (n + 1) l1) by lia.
    rewrite (sublist_split n n_pre (n + 1) l2) by lia.
    rewrite (sublist_single 0 n l1), (sublist_single 0 n l2) by lia.
    rewrite PreH1, PreH5. reflexivity. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1_split_goal_1 : mpn_cmp_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  assert (PreH11 : n_pre = Zlength l1) by lia.
  assert (PreH12 : n_pre = Zlength l2) by lia.
  dump_pre_spatial.
  replace (n + 1) with 0 in PreH4 by lia.
  rewrite PreH11, sublist_self in PreH4 by lia.
  rewrite <- PreH11, PreH12, sublist_self in PreH4 by lia.
  congruence.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1_split_goal_spatial : mpn_cmp_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  assert (PreH11 : n_pre = Zlength l1) by lia.
  assert (PreH12 : n_pre = Zlength l2) by lia.
  unfold mpd_store_Z_compact.
  Exists l1 l2.
  unfold mpd_store_list.
  split_pure_spatial.
  - rewrite <- PreH11, <- PreH12.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try (repeat split; assumption);
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1 : mpn_cmp_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_cmp_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mpn_cmp_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2_split_goal_1 : mpn_cmp_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  assert (PreH13 : n_pre = Zlength l1) by lia.
  assert (PreH14 : n_pre = Zlength l2) by lia.
  dump_pre_spatial.
  pose proof (list_to_Z_cmp_same_length 4294967296 (ltac:(lia)) l2 l1 n) as Hcmp.
  rewrite <- PreH13, <- PreH14 in Hcmp.
  unfold UINT_MOD in *.
  rewrite <- PreH7, <- PreH10.
  specialize (Hcmp (ltac:(lia)) (ltac:(lia)) (ltac:(auto)) PreH12 PreH9 (ltac:(lia))).
  lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2_split_goal_spatial : mpn_cmp_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  assert (PreH13 : n_pre = Zlength l1) by lia.
  assert (PreH14 : n_pre = Zlength l2) by lia.
  unfold mpd_store_Z_compact.
  Exists l1 l2.
  unfold mpd_store_list.
  split_pure_spatial.
  - rewrite <- PreH13, <- PreH14.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try (repeat split; assumption);
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_cmp_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mpn_cmp_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3_split_goal_1 : mpn_cmp_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  assert (PreH13 : n_pre = Zlength l1) by lia.
  assert (PreH14 : n_pre = Zlength l2) by lia.
  dump_pre_spatial.
  assert (Znth n l1 0 < Znth n l2 0) by lia.
  unfold UINT_MOD in *.
  rewrite <- PreH7, <- PreH10.
  apply (list_to_Z_cmp_same_length 4294967296 (ltac:(lia)) l1 l2 n); auto; try lia.
  rewrite <- PreH13, <- PreH14.
  auto.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3_split_goal_spatial : mpn_cmp_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply_p (UIntArray.full_Zlength ap_pre n_pre l1).
  prop_apply_p (UIntArray.full_Zlength bp_pre n_pre l2).
  Intros_p Hlen2.
  Intros_p Hlen1.
  assert (PreH13 : n_pre = Zlength l1) by lia.
  assert (PreH14 : n_pre = Zlength l2) by lia.
  unfold mpd_store_Z_compact.
  Exists l1 l2.
  unfold mpd_store_list.
  split_pure_spatial.
  - rewrite <- PreH13, <- PreH14.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try (repeat split; assumption);
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3 : mpn_cmp_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_cmp_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_mpn_cmp_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold UINT_MOD in *.
    all: destruct H as (? & ? & Hb1);
      destruct H1 as (? & ? & Hb2).
    + exact Hb1.
    + unfold UINT_MOD; exact Hb2.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1_split_goal_spatial : mpn_cmp4_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1 : mpn_cmp4_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2_split_goal_spatial : mpn_cmp4_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2 : mpn_cmp4_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_3_split_goal_spatial : mpn_cmp4_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  cancel.
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
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  unfold UINT_MOD in *.
  pose proof list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) l1 l2 (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_5_split_goal_1 : mpn_cmp4_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_cmp4_return_wit_5 : mpn_cmp4_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  unfold UINT_MOD in *.
  pose proof list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) l2 l1 (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia)).
  lia. 
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_1_split_goal_1 : gmp_umul_ppmm_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hu : 0 <= u_pre < 4294967296) by lia.
  assert (Hv : 0 <= v_pre < 4294967296) by lia.
  pose proof (land_65535_bounds u_pre Hu) as Hul.
  pose proof (land_65535_bounds v_pre Hv) as Hvl.
  pose proof (shiftr_16_bounds u_pre Hu) as Huh.
  pose proof (shiftr_16_bounds v_pre Hv) as Hvh.
  unfold unsigned_last_nbits, UINT_MOD in *.
  change (2 ^ 32) with 4294967296 in *.
  rewrite !half_product_mod__umul_product in * by lia.
  eapply (umul_ppmm_correct_with_carry u_pre v_pre
    (Z.land u_pre 65535) (Z.shiftr u_pre 16)
    (Z.land v_pre 65535) (Z.shiftr v_pre 16)
    (Z.land u_pre 65535 * Z.land v_pre 65535)
    (Z.land u_pre 65535 * Z.shiftr v_pre 16)
    (Z.shiftr u_pre 16 * Z.land v_pre 65535)
    (Z.shiftr u_pre 16 * Z.shiftr v_pre 16));
    try reflexivity; assumption.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_1 : gmp_umul_ppmm_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gmp_umul_ppmm_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_gmp_umul_ppmm_return_wit_2_split_goal_1 : gmp_umul_ppmm_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hu : 0 <= u_pre < 4294967296) by lia.
  assert (Hv : 0 <= v_pre < 4294967296) by lia.
  pose proof (land_65535_bounds u_pre Hu) as Hul.
  pose proof (land_65535_bounds v_pre Hv) as Hvl.
  pose proof (shiftr_16_bounds u_pre Hu) as Huh.
  pose proof (shiftr_16_bounds v_pre Hv) as Hvh.
  unfold unsigned_last_nbits, UINT_MOD in *.
  change (2 ^ 32) with 4294967296 in *.
  rewrite !half_product_mod__umul_product in * by lia.
  eapply (umul_ppmm_correct_no_carry u_pre v_pre
    (Z.land u_pre 65535) (Z.shiftr u_pre 16)
    (Z.land v_pre 65535) (Z.shiftr v_pre 16)
    (Z.land u_pre 65535 * Z.land v_pre 65535)
    (Z.land u_pre 65535 * Z.shiftr v_pre 16)
    (Z.shiftr u_pre 16 * Z.land v_pre 65535)
    (Z.shiftr u_pre 16 * Z.shiftr v_pre 16));
    try reflexivity; assumption.
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

Lemma proof_of_mpn_mul_1_entail_wit_1 : mpn_mul_1_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_mul_1_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_1 : mpn_mul_1_entail_wit_5_1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_mul_1_entail_wit_5_1_split_goal_2 : mpn_mul_1_entail_wit_5_1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpn_mul_1_entail_wit_5_1 : mpn_mul_1_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (UIntArray.full_Zlength up_pre n_pre l).
  Intros_p Hlen.
  prop_apply_p (UIntArray.seg_Zlength rp_pre 0 (i+1)
    (l_rp_2 ++ unsigned_last_nbits (lpl+cl) 32 :: nil)).
  Intros_p Hrlen.
  assert (Hr : Zlength l_rp_2 = i).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil in Hrlen; lia. }
  pose proof (mul_prefix_step__mul_transition l l_rp_2 n_pre i vl_pre cl lpl hpl
    Hlen Hr ltac:(lia) PreH17 PreH10
    ltac:(unfold UINT_MOD; lia) ltac:(unfold UINT_MOD; lia)
    ltac:(unfold UINT_MOD; lia) ltac:(unfold UINT_MOD; lia)
    PreH11 PreH12) as Hstep.
  change (unsigned_last_nbits (lpl+cl) 32) with ((lpl+cl) mod UINT_MOD) in *.
  cbn zeta in Hstep.
  destruct (Z_lt_dec ((lpl+cl) mod UINT_MOD) cl) as [Hcarry|Hnocarry]; try lia.
  simpl in Hstep.
  destruct Hstep as [Hk [Hdigits Hvalue]].
  Exists (l_rp_2 ++ ((lpl+cl) mod UINT_MOD) :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (store_uint_undef_store_uint (&("ul")) (Znth i l 0)).
    sep_apply_l_atomic (store_uint_undef_store_uint (&("lpl")) ((lpl+cl) mod UINT_MOD)).
    sep_apply_l_atomic (store_uint_undef_store_uint (&("hpl")) hpl).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_1 : mpn_mul_1_entail_wit_5_2_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_2 : mpn_mul_1_entail_wit_5_2_split_goal_2.
Proof. Abort.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_3 : mpn_mul_1_entail_wit_5_2_split_goal_3.
Proof. Abort.

Lemma proof_of_mpn_mul_1_entail_wit_5_2_split_goal_4 : mpn_mul_1_entail_wit_5_2_split_goal_4.
Proof. Abort.

Lemma proof_of_mpn_mul_1_entail_wit_5_2 : mpn_mul_1_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (UIntArray.full_Zlength up_pre n_pre l).
  Intros_p Hlen.
  prop_apply_p (UIntArray.seg_Zlength rp_pre 0 (i+1)
    (l_rp_2 ++ unsigned_last_nbits (lpl+cl) 32 :: nil)).
  Intros_p Hrlen.
  assert (Hr : Zlength l_rp_2 = i).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil in Hrlen; lia. }
  pose proof (mul_prefix_step__mul_transition l l_rp_2 n_pre i vl_pre cl lpl hpl
    Hlen Hr ltac:(lia) PreH17 PreH10
    ltac:(unfold UINT_MOD; lia) ltac:(unfold UINT_MOD; lia)
    ltac:(unfold UINT_MOD; lia) ltac:(unfold UINT_MOD; lia)
    PreH11 PreH12) as Hstep.
  change (unsigned_last_nbits (lpl+cl) 32) with ((lpl+cl) mod UINT_MOD) in *.
  cbn zeta in Hstep.
  destruct (Z_lt_dec ((lpl+cl) mod UINT_MOD) cl) as [Hcarry|Hnocarry]; try lia.
  simpl in Hstep.
  destruct Hstep as [Hk [Hdigits Hvalue]].
  assert (Hwrap : unsigned_last_nbits (1+hpl) 32 = hpl+1).
  { unfold unsigned_last_nbits; change ((1+hpl) mod UINT_MOD = hpl+1).
    rewrite Z.mod_small by lia; lia. }
  rewrite Hwrap.
  unfold UINT_MOD in Hk.
  Exists (l_rp_2 ++ ((lpl+cl) mod UINT_MOD) :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (store_uint_undef_store_uint (&("ul")) (Znth i l 0)).
    sep_apply_l_atomic (store_uint_undef_store_uint (&("lpl")) ((lpl+cl) mod UINT_MOD)).
    sep_apply_l_atomic (store_uint_undef_store_uint (&("hpl")) hpl).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_mul_1_return_wit_1_split_goal_1 : mpn_mul_1_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_mul_1_return_wit_1_split_goal_2 : mpn_mul_1_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_mpn_mul_1_return_wit_1 : mpn_mul_1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename PreH8 into Hcl_nonnegative.
  rename PreH12 into PreH8.
  prop_apply_p (UIntArray.full_Zlength up_pre n_pre l).
  Intros_p Hsource_length.
  prop_apply_p (UIntArray.seg_Zlength rp_pre 0 i l_rp).
  Intros_p Hresult_length.
  Exists (list_to_Z UINT_MOD l_rp) l_rp.
  split_pure_spatial.
  - assert (Hi_eq: i = n_pre) by lia. rewrite Hi_eq.
    rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
    normalize.
    cancel.
    sep_apply (UIntArray.seg_to_full rp_pre 0 n_pre l_rp).
    replace (rp_pre + 0 * sizeof ( UINT )) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    assert (Hi_eq: i = n_pre) by lia. rewrite Hi_eq in *.
    rewrite (sublist_self l n_pre) in PreH8 by lia. lia.
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
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs n)).
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
  prop_apply_p (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
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

