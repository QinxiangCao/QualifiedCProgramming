From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_rshift_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_rshift_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_1 : mpn_rshift_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (off_shifted + 0 + 1) with (off_shifted + 1) by lia.
  replace (0 - 0) with 0 by lia.
  rewrite Znth_sublist by lia.
  replace (0 + off_shifted) with off_shifted by lia.
  rewrite (mpn_lshift_list_to_Z_single_sublist UINT_MOD l_up_shifted off_shifted).
  2: { rewrite PreH8; lia. }
  rewrite list_to_Z_nil.
  rewrite Z.pow_0_r.
  dump_pre_spatial.
  ring_simplify.
  apply mpn_rshift_limb_decompose.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted off_shifted);
      try exact PreH9; lia.
  + lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_2 : mpn_rshift_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist by lia.
  replace (0 - 0 + off_shifted) with off_shifted by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_3 : mpn_rshift_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist by lia.
  replace (0 - 0 + off_shifted) with off_shifted by lia.
  replace (off_shifted + 0) with off_shifted by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  dump_pre_spatial.
  symmetry.
  apply Z.quot_div_nonneg.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted off_shifted);
      try exact PreH9; lia.
  + apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_4 : mpn_rshift_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist by lia.
  replace (0 - 0 + off_shifted) with off_shifted by lia.
  replace (off_shifted + 0) with off_shifted by lia.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_5 : mpn_rshift_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_6 : mpn_rshift_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_spatial : mpn_rshift_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst up_pre.
  rewrite <- (UIntArray.seg_shift rp_pre off_shifted 0 1
    (sublist off_shifted (off_shifted + 1) l_up_shifted)).
  replace (off_shifted + 0) with off_shifted by lia.
  replace (off_shifted + (0 + 1)) with (off_shifted + 1) by lia.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre off_shifted (off_shifted + 1)
    (n_pre + off_shifted)
    (sublist off_shifted (off_shifted + 1) l_up_shifted)
    (sublist (off_shifted + 1) (n_pre + off_shifted) l_up_shifted)).
  - dump_pre_spatial; lia.
  - rewrite <- (sublist_split off_shifted (n_pre + off_shifted)
      (off_shifted + 1) l_up_shifted) by lia.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 off_shifted
      (n_pre + off_shifted)
      (sublist 0 off_shifted l_up_shifted)
      (sublist off_shifted (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + rewrite <- (sublist_split 0 (n_pre + off_shifted) off_shifted l_up_shifted) by lia.
      cancel.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1 : mpn_rshift_entail_wit_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_spatial.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_1.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_2.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_3.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_4.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2 : mpn_rshift_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_3 : mpn_rshift_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  subst rp up up_pre.
  sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i_2 (i_2 + 1)
    (n_pre + off_shifted)
    (sublist i_2 (n_pre + off_shifted) l_up_shifted)).
  - dump_pre_spatial; lia.
  - repeat rewrite Zsublist_Zsublist by lia.
    replace (0 + i_2) with i_2 by lia.
    replace (i_2 + 1 - i_2 + i_2) with (i_2 + 1) by lia.
    replace (n_pre + off_shifted - i_2 + i_2) with (n_pre + off_shifted) by lia.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre (i_2 + 1)
      (off_shifted + i_2 + 1) (n_pre + off_shifted)
      (sublist (i_2 + 1) (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + repeat rewrite Zsublist_Zsublist by lia.
      replace (0 + (i_2 + 1)) with (i_2 + 1) by lia.
      replace (off_shifted + i_2 + 1 - (i_2 + 1) + (i_2 + 1))
        with (off_shifted + i_2 + 1) by lia.
      replace (n_pre + off_shifted - (i_2 + 1) + (i_2 + 1))
        with (n_pre + off_shifted) by lia.
      sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre
        (off_shifted + i_2 + 1) (off_shifted + i_2 + 2)
        (n_pre + off_shifted)
        (sublist (off_shifted + i_2 + 1)
          (n_pre + off_shifted) l_up_shifted)).
      * dump_pre_spatial; lia.
      * repeat rewrite Zsublist_Zsublist by lia.
        replace (0 + (off_shifted + i_2 + 1))
          with (off_shifted + i_2 + 1) by lia.
        replace (off_shifted + i_2 + 2 - (off_shifted + i_2 + 1)
          + (off_shifted + i_2 + 1)) with (off_shifted + i_2 + 2) by lia.
        replace (n_pre + off_shifted - (off_shifted + i_2 + 1)
          + (off_shifted + i_2 + 1)) with (n_pre + off_shifted) by lia.
        rewrite <- (UIntArray.seg_shift rp_pre i_2 0 1
          (sublist i_2 (i_2 + 1) l_up_shifted)).
        replace (rp_pre + off_shifted * sizeof(UINT) +
          (i_2 + 1) * sizeof(UINT))
          with (rp_pre + (off_shifted + i_2 + 1) * sizeof(UINT)) by lia.
        rewrite <- (UIntArray.seg_shift rp_pre (off_shifted + i_2 + 1) 0 1
          (sublist (off_shifted + i_2 + 1)
            (off_shifted + i_2 + 2) l_up_shifted)).
        repeat (replace (i_2 + 0) with i_2 by lia).
        repeat (replace (off_shifted + i_2 + 1 + 0)
          with (off_shifted + i_2 + 1) by lia).
        replace (off_shifted + i_2 + 1 + 1)
          with (off_shifted + i_2 + 2) by lia.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_4 : mpn_rshift_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (high_next := Znth (0 - 0)
    (sublist (off_shifted + i + 1) (off_shifted + i + 2) l_up_shifted) 0).
  set (joined := Z.lor low_limb
    (unsigned_last_nbits (Z.shiftl high_next tnc) 32)).
  set (cur := replace_Znth 0 joined (sublist i (i + 1) l_up_shifted)).
  Exists (l_done_2 ++ cur) (i + 1).
  subst rp up up_pre.
  sep_apply_l_atomic (UIntArray.full_to_seg (rp_pre + i * sizeof(UINT)) 1 cur).
  rewrite <- (UIntArray.seg_shift rp_pre i 0 1 cur).
    replace (i + 0) with i by lia.
    replace (rp_pre + off_shifted * sizeof(UINT) + (i + 1) * sizeof(UINT))
      with (rp_pre + (off_shifted + i + 1) * sizeof(UINT)) by lia.
    rewrite <- (UIntArray.seg_shift rp_pre (off_shifted + i + 1) 0 1
      (sublist (off_shifted + i + 1) (off_shifted + i + 2) l_up_shifted)).
    replace (off_shifted + i + 1 + 0) with (off_shifted + i + 1) by lia.
    replace (off_shifted + i + 1 + 1) with (off_shifted + i + 2) by lia.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1)
    l_done_2 cur).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre
        (off_shifted + i + 1) (off_shifted + i + 2)
        (n_pre + off_shifted)
        (sublist (off_shifted + i + 1) (off_shifted + i + 2) l_up_shifted)
        (sublist (off_shifted + i + 2) (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + rewrite <- (sublist_split (off_shifted + i + 1)
          (n_pre + off_shifted) (off_shifted + i + 2) l_up_shifted) by lia.
      sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre
          (i + 1) (off_shifted + i + 1) (n_pre + off_shifted)
          (sublist (i + 1) (off_shifted + i + 1) l_up_shifted)
          (sublist (off_shifted + i + 1) (n_pre + off_shifted) l_up_shifted)).
      * dump_pre_spatial; lia.
      * rewrite <- (sublist_split (i + 1) (n_pre + off_shifted)
             (off_shifted + i + 1) l_up_shifted) by lia.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; try assumption; try lia.
           ++ subst cur.
           rewrite Zlength_app.
           rewrite Zlength_replace_Znth.
           rewrite Zlength_sublist by lia.
           rewrite PreH15.
           lia.
           ++ subst cur high_next joined.
           assert (Hcur_single:
             replace_Znth 0
               (Z.lor low_limb
                 (unsigned_last_nbits
                   (Z.shiftl
                     (Znth (0 - 0)
                       (sublist (off_shifted + i + 1)
                         (off_shifted + i + 2) l_up_shifted) 0) tnc) 32))
               (sublist i (i + 1) l_up_shifted) =
             (Z.lor low_limb
                 (unsigned_last_nbits
                   (Z.shiftl
                     (Znth (off_shifted + i + 1) l_up_shifted 0) tnc) 32)) :: nil).
           {
             replace (0 - 0) with 0 by lia.
             rewrite Znth_sublist by lia.
             replace (0 + (off_shifted + i + 1)) with (off_shifted + i + 1) by lia.
             assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_shifted).
             { rewrite PreH14; lia. }
             rewrite (replace_Znth_sublist_head l_up_shifted i (i + 1)
               (Z.lor low_limb
                 (unsigned_last_nbits
                   (Z.shiftl (Znth (off_shifted + i + 1) l_up_shifted 0) tnc) 32))
               Hcond).
             rewrite Zsublist_nil by lia.
             reflexivity.
           }
           rewrite Hcur_single.
           apply list_within_bound_app_single.
           ** exact PreH17.
           ** rewrite PreH19.
              replace (Znth (off_shifted + i) l_up_shifted 0 ÷ 2 ^ cnt_pre)
                with (Z.shiftr (Znth (off_shifted + i) l_up_shifted 0) cnt_pre).
              rewrite PreH11.
              apply mpn_rshift_join_limb_bound.
              --- apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted
                   (off_shifted + i)); try exact PreH16; lia.
              --- lia.
              --- rewrite Z.shiftr_div_pow2 by lia.
                  symmetry.
                  apply Z.quot_div_nonneg.
                  +++ assert (Hbd:
                       0 <= Znth (off_shifted + i) l_up_shifted 0 < UINT_MOD).
                     { apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted
                         (off_shifted + i)); try exact PreH16; lia. }
                     lia.
                  +++ apply Z.pow_pos_nonneg; lia.
           ++ subst cur high_next joined.
           replace (0 - 0) with 0 by lia.
           rewrite Znth_sublist by lia.
           replace (0 + (off_shifted + i + 1)) with (off_shifted + (i + 1)) by lia.
           reflexivity.
           ++ subst high_next.
           replace (0 - 0) with 0 by lia.
           rewrite Znth_sublist by lia.
           replace (0 + (off_shifted + i + 1)) with (off_shifted + (i + 1)) by lia.
           rewrite Z.shiftr_div_pow2 by lia.
           symmetry.
           apply Z.quot_div_nonneg.
           ** assert (Hbd:
                0 <= Znth (off_shifted + (i + 1)) l_up_shifted 0 < UINT_MOD).
              { apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted
                  (off_shifted + (i + 1))); try exact PreH16; lia. }
              lia.
           ** apply Z.pow_pos_nonneg; lia.
           ++ subst cur high_next joined.
              set (lsrc := sublist off_shifted (off_shifted + n_pre) l_up_shifted).
              assert (Hls_len: Zlength lsrc = n_pre).
              { subst lsrc. rewrite Zlength_sublist by lia. lia. }
              assert (Hls_bound: list_within_bound UINT_MOD lsrc).
              { subst lsrc. apply list_within_bound_sublist.
                - lia.
                - rewrite PreH14; lia.
                - exact PreH16. }
              assert (Hlow_src: low_limb = Znth i lsrc 0 ÷ 2 ^ cnt_pre).
              { subst lsrc.
                rewrite Znth_sublist by lia.
                replace (i + off_shifted) with (off_shifted + i) by lia.
                exact PreH19. }
              assert (Hhigh_src:
                Znth (0 - 0)
                  (sublist (off_shifted + i + 1)
                    (off_shifted + i + 2) l_up_shifted) 0 =
                Znth (i + 1) lsrc 0).
              { subst lsrc.
                replace (0 - 0) with 0 by lia.
                rewrite Znth_sublist by lia.
                rewrite Znth_sublist by lia.
                replace (0 + (off_shifted + i + 1)) with (i + 1 + off_shifted) by lia.
                reflexivity. }
              assert (Hstep_src:
                list_to_Z UINT_MOD (sublist 0 (i + 1) lsrc) =
                (list_to_Z UINT_MOD l_done_2 + low_limb * UINT_MOD ^ i) *
                  2 ^ cnt_pre + retval ÷ 2 ^ tnc).
              { subst lsrc.
                rewrite Zsublist_Zsublist by lia.
                replace (0 + off_shifted) with off_shifted by lia.
                replace (i + 1 + off_shifted) with (off_shifted + i + 1) by lia.
                exact PreH21. }
              pose proof (mpn_rshift_step_equation lsrc l_done_2 n_pre (i + 1)
                cnt_pre retval (Znth (i + 1) lsrc 0) low_limb tnc
                ltac:(lia) ltac:(lia) ltac:(rewrite Hls_len; lia)
                ltac:(rewrite PreH15; lia) ltac:(lia) Hls_bound
                ltac:(replace (i + 1 - 1) with i by lia; exact Hlow_src)
                eq_refl PreH11
                ltac:(replace (i + 1 - 1) with i by lia; exact Hstep_src)) as Hstep.
              subst lsrc.
              rewrite Zsublist_Zsublist in Hstep by lia.
              replace (0 + off_shifted) with off_shifted in Hstep by lia.
              replace (i + 1 + 1 + off_shifted) with (off_shifted + (i + 1) + 1) in Hstep by lia.
              rewrite <- Hhigh_src in Hstep.
              match goal with
              | |- context[replace_Znth ?idx ?v (sublist i (i + 1) l_up_shifted)] =>
                  set (cur_replace := replace_Znth idx v (sublist i (i + 1) l_up_shifted))
              end.
              match type of Hstep with
              | context[replace_Znth ?idx ?v ?lst] =>
                  set (src_replace := replace_Znth idx v lst) in Hstep
              end.
              assert (Hreplace_eq: cur_replace = src_replace).
              {
                subst cur_replace src_replace.
                replace (i + 1 - 1) with i by lia.
                replace (i - i) with 0 by lia.
                replace (i + 1 - (i + 1)) with 0 by lia.
                set (joined := Z.lor low_limb
                  (unsigned_last_nbits
                    (Z.shiftl
                      (Znth (0 - 0)
                        (sublist (off_shifted + i + 1)
                          (off_shifted + i + 2) l_up_shifted) 0) tnc) 32)).
                assert (Hcur_cond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_shifted).
                { rewrite PreH14; lia. }
                pose proof (replace_Znth_sublist_head l_up_shifted i (i + 1)
                  joined Hcur_cond) as Hcur.
                assert (Hsrc_cond:
                  0 <= i /\ i < i + 1 /\
                  i + 1 <= Zlength (sublist off_shifted (off_shifted + n_pre) l_up_shifted)).
                { rewrite Zlength_sublist by lia; lia. }
                pose proof (replace_Znth_sublist_head
                  (sublist off_shifted (off_shifted + n_pre) l_up_shifted)
                  i (i + 1) joined Hsrc_cond) as Hsrc.
                rewrite Hcur, Hsrc.
                repeat rewrite Zsublist_nil by lia.
                reflexivity.
              }
              rewrite Hreplace_eq.
              exact Hstep.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5 : mpn_rshift_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_6 : mpn_rshift_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i_2 (i_2 + 1)
      (n_pre + off_shifted)
      (sublist i_2 (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + repeat rewrite Zsublist_Zsublist by lia.
      replace (0 + i_2) with i_2 by lia.
      replace (i_2 + 1 - i_2 + i_2) with (i_2 + 1) by lia.
      replace (n_pre + off_shifted - i_2 + i_2)
        with (n_pre + off_shifted) by lia.
      replace (UIntArray.seg rp_pre i_2 (i_2 + 1)
        (sublist i_2 (i_2 + 1) l_up_shifted))
        with (UIntArray.seg rp_pre (i_2 + 0) (i_2 + 1)
          (sublist i_2 (i_2 + 1) l_up_shifted)) by (f_equal; lia).
      rewrite (UIntArray.seg_shift rp_pre i_2 0 1
        (sublist i_2 (i_2 + 1) l_up_shifted)).
      rewrite PreH2.
      cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_7 : mpn_rshift_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_last: i = n_pre - 1) by lia.
  set (lsrc := sublist off_shifted (off_shifted + n_pre) l_up_shifted).
  set (cur := replace_Znth 0 low_limb (sublist i (i + 1) l_up_shifted)).
  Exists (l_done ++ cur).
  assert (Hls_len: Zlength lsrc = n_pre).
  { subst lsrc. rewrite Zlength_sublist by lia. lia. }
  assert (Hls_bound: list_within_bound UINT_MOD lsrc).
  { subst lsrc. apply list_within_bound_sublist.
    - lia.
    - rewrite PreH14; lia.
    - exact PreH16. }
  assert (Hlow_src: low_limb = Znth i lsrc 0 ÷ 2 ^ cnt_pre).
  { subst lsrc.
    rewrite Znth_sublist by lia.
    replace (i + off_shifted) with (off_shifted + i) by lia.
    exact PreH19. }
  assert (Hcur_single: cur = low_limb :: nil).
  {
    subst cur.
    assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_shifted).
    { rewrite PreH14; lia. }
    rewrite (replace_Znth_sublist_head l_up_shifted i (i + 1) low_limb Hcond).
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  assert (Hlast_single:
    replace_Znth (i - i) low_limb (sublist i (i + 1) lsrc) =
    low_limb :: nil).
  {
    replace (i - i) with 0 by lia.
    assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength lsrc).
    { rewrite Hls_len; lia. }
    rewrite (replace_Znth_sublist_head lsrc i (i + 1) low_limb Hcond).
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  sep_apply_l_atomic (UIntArray.full_to_seg rp 1 cur).
  subst rp.
  rewrite <- (UIntArray.seg_shift rp_pre i 0 1 cur).
  replace (i + 0) with i by lia.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1)
    l_done cur).
  - dump_pre_spatial; lia.
  - replace (i + 1) with n_pre by lia.
    split_pure_spatial.
    + sep_apply (store_uint_undef_store_uint &( "high_limb") high_limb).
      sep_apply (store_uint_undef_store_uint &( "low_limb") low_limb).
      cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
      * rewrite Hcur_single.
        rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil, ?PreH15.
        lia.
      * rewrite Hcur_single.
        apply list_within_bound_app_single.
        -- exact PreH17.
        -- rewrite Hlow_src.
           apply mpn_rshift_quot_limb_bound.
           ++ apply (list_within_bound_Znth_bound UINT_MOD lsrc i);
                try exact Hls_bound; rewrite Hls_len; lia.
           ++ lia.
      * assert (Hinv_src:
          list_to_Z UINT_MOD (sublist 0 n_pre lsrc) =
          (list_to_Z UINT_MOD l_done + low_limb * UINT_MOD ^ i) *
            2 ^ cnt_pre + retval ÷ 2 ^ tnc).
        {
          subst lsrc.
          rewrite Zsublist_Zsublist by lia.
          replace (0 + off_shifted) with off_shifted by lia.
          replace (n_pre + off_shifted) with (off_shifted + (i + 1)) by lia.
          replace (off_shifted + (i + 1)) with (off_shifted + i + 1) by lia.
          exact PreH21.
        }
        pose proof (mpn_rshift_return_equation lsrc l_done n_pre i cnt_pre
          retval low_limb tnc Hi_last Hls_len ltac:(rewrite PreH15; lia)
          PreH10 Hls_bound ltac:(lia) Hlow_src Hinv_src) as Hret.
        rewrite Hcur_single.
        rewrite PreH10.
        rewrite Hlast_single in Hret.
        exact Hret.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_1_split_goal_spatial : mpn_rshift_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst up_pre.
  sep_apply_l_atomic (UIntArray.full_split_to_seg rp_pre off_shifted
    (n_pre + off_shifted) l_up_shifted).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre off_shifted
      (off_shifted + 1) (n_pre + off_shifted)
      (sublist off_shifted (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + rewrite Zsublist_Zsublist by lia.
      rewrite Zsublist_Zsublist by lia.
      replace (0 + off_shifted) with off_shifted by lia.
      replace (1 + off_shifted) with (off_shifted + 1) by lia.
      replace (off_shifted + 1 - off_shifted + off_shifted)
        with (off_shifted + 1) by lia.
      replace (n_pre + off_shifted - off_shifted + off_shifted)
        with (n_pre + off_shifted) by lia.
      rewrite <- (UIntArray.seg_shift rp_pre off_shifted 0 1
        (sublist off_shifted (off_shifted + 1) l_up_shifted)).
      replace (off_shifted + 0) with off_shifted by lia.
      cancel.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_1 : mpn_rshift_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_rshift_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_rshift_shifted_entail_inplace : mpn_rshift_shifted_entail_inplace.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros.
  Exists l_up_inplace 0.
  replace (n_pre + 0) with n_pre by lia.
  replace (0 + n_pre) with n_pre by lia.
  replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
  rewrite sublist_self by lia.
  rewrite Zsublist_nil by lia.
  subst rp_pre.
  split_pure_spatial.
  - cancel.
    Intros_r retval.
    apply_sepcon_adjoint.
    Intros l_out.
    rewrite UIntArray.seg_empty.
    Intros.
    Exists l_out.
    sep_apply_l_atomic (UIntArray.seg_to_full up_pre 0 n_pre l_out).
    replace (up_pre + 0 * sizeof(UINT)) with up_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    split_pure_spatial; [cancel | repeat split_pures; dump_pre_spatial; auto].
  - repeat split_pures; dump_pre_spatial; auto; lia.
Qed.

