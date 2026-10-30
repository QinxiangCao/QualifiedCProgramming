From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P082_1989E_distance_to_different_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib.
Local Open Scope sac.

(* Part 16: entailment, return and partial-solve proofs. *)

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hk10 : k_pre <= 10).
  { change (k_pre <= Z.min n_pre 10) in PreH6.
    pose proof (Z.le_min_r n_pre 10). lia. }
  assert (Hmul : (n_pre + 1) * (k_pre + 1) <= 200001 * 11).
  { apply Z.mul_le_mono_nonneg; lia. }
  assert (Hsize : unsigned_last_nbits ((n_pre + 1) * (k_pre + 1)) 32 =
      (n_pre + 1) * (k_pre + 1)).
  { apply unsigned_last_nbits_eq.
    change (0 <= (n_pre + 1) * (k_pre + 1) < 4294967296).
    split; [nia|]. eapply Z.le_lt_trans; [exact Hmul|lia]. }
  rewrite Hsize.
  pose proof (P082InitArrays_zero__initialization_semantics
    n_pre k_pre ((n_pre + 1) * (k_pre + 1)) ltac:(lia) ltac:(lia)
    ltac:(reflexivity)) as [Hinit Hsem].
  Exists (repeat_Z 0 ((n_pre + 1) * (k_pre + 1)))
    (repeat_Z 0 ((n_pre + 1) * (k_pre + 1))).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. eapply Z.le_trans; [exact Hmul|lia].
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Hinit.
    + dump_pre_spatial. exact Hsem.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (P082InitRow_step__initialization_semantics
    n_pre k_pre i dl_2 pl_2 PreH11 ltac:(lia) PreH10 PreH17 PreH18)
    as [_ Hsem].
  exact Hsem.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (P082InitRow_step__initialization_semantics
    n_pre k_pre i dl_2 pl_2 PreH11 ltac:(lia) PreH10 PreH17 PreH18)
    as [Hstate _].
  exact Hstate.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre + 1) by lia. subst i.
  apply (P082SemanticProgress_complete n_pre k_pre 1 dl_2 pl_2).
  split.
  - unfold P082SemanticColumns. intros col row Hcol Hrow. lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre + 1) by lia. subst i.
  unfold P082ColumnsState. split.
  - apply P082InitState_complete; [lia|exact PreH11].
  - intros col row Hcol Hrow. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (P082SemanticColumns_start
    n_pre k_pre j dl_2 pl_2 PreH12) as Hstart.
  unfold P082SemanticProgress in *. destruct Hstart as [Hcols _].
  split; [exact Hcols|].
  intros row Hrow. assert (row = 0) by lia. subst row.
  destruct PreH11 as [[Hdl [Hpl [Hrange [Hone Hzero]]]] Hcells].
  specialize (Hzero j ltac:(lia)) as [Hdp Hpref].
  unfold P082SemanticCell. rewrite Hdp, Hpref. split.
  - destruct (Z_lt_dec j k_pre) as [Hlt|Hge].
    + rewrite P082ExactCoreCount_zero_too_many by lia.
      unfold P082Norm, P082Modulus. reflexivity.
    + assert (j = k_pre) by lia. subst j.
      rewrite P082SaturatedCoreCount_zero_too_many by lia.
      unfold P082Norm, P082Modulus. reflexivity.
  - rewrite P082PrefixCoreCount_zero_too_many by lia.
    unfold P082Norm, P082Modulus. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply P082Columns_start. exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst j; subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst j; subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst W; nia).
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_1 : solver_entail_wit_10_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_1 : solver_entail_wit_10_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_3_split_goal_1 : solver_entail_wit_11_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_4_split_goal_1 : solver_entail_wit_11_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  (* r6: keep normalization local to this semantic branch. *)
  LLM_pre_process ltac:(lia).
  assert (HCnorm : forall x,
    Z.rem (Z.rem x 998244353 + 998244353) 998244353 = P082Norm x).
  { intro x.
    pose proof (Z.rem_bound_abs x 998244353 ltac:(lia)) as Hbound.
    assert (Hnonneg : 0 <= Z.rem x 998244353 + 998244353).
    { destruct (Z_le_gt_dec 0 (Z.rem x 998244353)); [lia|].
      rewrite Z.abs_neq in Hbound by lia. lia. }
    rewrite Z.rem_mod_nonneg by lia.
    rewrite Z.rem_eq by lia.
    unfold P082Norm, P082Modulus.
    replace (x - 998244353 * (x ÷ 998244353) + 998244353)
      with (x + (1 - x ÷ 998244353) * 998244353) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (Hfour : forall a b c d,
    P082Norm (P082Norm a - P082Norm b + P082Norm c - P082Norm d) =
    P082Norm (a - b + c - d)).
  { intros a b c d. unfold P082Norm, P082Modulus.
    rewrite (Zminus_mod_idemp_r
      (a mod 998244353 - b mod 998244353 + c mod 998244353)
      d 998244353).
    replace (a mod 998244353 - b mod 998244353 + c mod 998244353 - d)
      with (c mod 998244353 + (a mod 998244353 - b mod 998244353 - d)) by ring.
    rewrite (Zplus_mod_idemp_l c
      (a mod 998244353 - b mod 998244353 - d) 998244353).
    replace (c + (a mod 998244353 - b mod 998244353 - d))
      with (a mod 998244353 + (c - b mod 998244353 - d)) by ring.
    rewrite (Zplus_mod_idemp_l a
      (c - b mod 998244353 - d) 998244353).
    replace (a + (c - b mod 998244353 - d))
      with (a + c - d - b mod 998244353) by ring.
    rewrite (Zminus_mod_idemp_r (a + c - d) b 998244353).
    f_equal. ring. }
  subst j. subst W.
  unfold P082SemanticProgress in *.
  destruct PreH41 as [Hcols Hrows].
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in PreH40.
  destruct PreH40 as [[[HlenD [HlenP Hbase]] Hdonecols] Hdone].
  split.
  - intros col row Hcol Hrow.
    specialize (Hcols col row ltac:(lia) Hrow).
    unfold P082SemanticCell in *.
    destruct Hcols as [Hd Hp].
    assert (Htarget : 0 <= P082Index k_pre row col < (n_pre + 1) * (k_pre + 1)).
    { apply P082Index_bounds; lia. }
    assert (Hneq : P082Index k_pre i k_pre <> P082Index k_pre row col).
    { intro Heq. unfold P082Index in Heq.
      destruct (Z_lt_ge_dec row i) as [Hri|Hri].
      - assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        lia.
      - destruct (Z.eq_dec row i) as [->|Hne]; [lia|].
        assert (Hmul : (i + 1) * (k_pre + 1) <= row * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        lia. }
    split.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenD. unfold P082Index. lia.
      * rewrite HlenD. exact Htarget.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenP. unfold P082Index. lia.
      * rewrite HlenP. exact Htarget.
  - intros row Hrow.
    destruct (Z_lt_ge_dec row i) as [Hlt|Hge].
    + specialize (Hrows row ltac:(lia)).
      unfold P082SemanticCell in *.
      destruct Hrows as [Hd Hp].
      assert (Htarget : 0 <= P082Index k_pre row k_pre < (n_pre + 1) * (k_pre + 1)).
      { apply P082Index_bounds; lia. }
      assert (Hneq : P082Index k_pre i k_pre <> P082Index k_pre row k_pre).
      { intro Heq. unfold P082Index in Heq.
        assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        lia. }
      split.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenD. unfold P082Index. lia.
        -- rewrite HlenD. exact Htarget.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenP. unfold P082Index. lia.
        -- rewrite HlenP. exact Htarget.
    + assert (row = i) by lia. subst row.
      pose proof (Hcols (k_pre - 1) (i - 1) ltac:(lia) ltac:(lia)) as Hkm1p.
      pose proof (Hcols (k_pre - 1) (i - 2) ltac:(lia) ltac:(lia)) as Hkm1d.
      pose proof (Hrows (i - 1) ltac:(lia)) as Hkp.
      pose proof (Hrows (i - 2) ltac:(lia)) as Hkd.
      unfold P082SemanticCell in Hkm1p, Hkm1d, Hkp, Hkd |- *.
      destruct Hkm1p as [Hkm1pd Hkm1pp].
      destruct Hkm1d as [Hkm1dd Hkm1dp].
      destruct Hkp as [Hkpd Hkpp].
      destruct Hkd as [Hkdd Hkdp].
      unfold P082Index in Hkm1pd, Hkm1pp, Hkm1dd, Hkm1dp,
        Hkpd, Hkpp, Hkdd, Hkdp.
      destruct (Z_lt_dec (k_pre - 1) k_pre) as [Hyes|Hno]; [|lia].
      destruct (Z_lt_dec k_pre k_pre) as [Hbad|Hnlt]; [lia|].
      split.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite HCnorm.
        rewrite Hkm1pp, Hkm1dd, Hkpp, Hkdd.
        rewrite Hfour.
        destruct (Z_le_dec k_pre i) as [Hki|Hki].
        -- rewrite <- P082SaturatedCoreCount_recurrence_large by lia.
           reflexivity.
        -- repeat rewrite P082PrefixCoreCount_zero_too_many by lia.
           repeat rewrite P082ExactCoreCount_zero_too_many by lia.
           repeat rewrite P082SaturatedCoreCount_zero_too_many by lia.
           unfold P082Norm, P082Modulus. reflexivity.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenP. unfold P082Index. lia. }
        rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite HCnorm.
        rewrite Hkm1pp, Hkm1dd, Hkpp, Hkdd.
        match goal with
        | |- Z.rem (P082Norm ?a + P082Norm ?b) 998244353 = _ =>
            pose proof (P082Norm_range a);
            pose proof (P082Norm_range b)
        end.
        rewrite Z.rem_mod_nonneg by lia.
        rewrite Hfour.
        destruct (Z_le_dec k_pre i) as [Hki|Hki].
        -- rewrite <- P082SaturatedCoreCount_recurrence_large by lia.
           unfold P082Norm.
           rewrite <- Zplus_mod.
           rewrite <- P082PrefixCoreCount_recurrence_saturated by lia.
           reflexivity.
        -- repeat rewrite P082PrefixCoreCount_zero_too_many by lia.
           repeat rewrite P082ExactCoreCount_zero_too_many by lia.
           repeat rewrite P082SaturatedCoreCount_zero_too_many by lia.
           unfold P082Norm, P082Modulus. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_2 : solver_entail_wit_12_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst j. subst W.
  pose proof PreH40 as Hstate.
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in Hstate.
  destruct Hstate as [[[HlenD [HlenP [Hrange [Hcol1 Hrow0]]]] Hold] Hcurrent].
  eapply P082ColumnProgress_step_saturated__saturated_updates;
    try eassumption; try lia.
  - unfold P082RawCell, P082Index.
    destruct (Z_le_dec 3 i); [|lia].
    destruct (Z.eq_dec k_pre k_pre); [|contradiction].
    rewrite P082Norm_c_normalize__semantic_updates. f_equal. ring.
  - rewrite Znth_replace_Znth_Same.
    2:{ rewrite HlenD. unfold P082Index. lia. }
    pose proof (Hrange (P082Index k_pre (i - 1) k_pre)
      ltac:(rewrite HlenD; apply P082Index_bounds; lia)) as [_ Holdrange].
    rewrite P082Norm_c_normalize__semantic_updates.
    match goal with
    | |- Z.rem (?a + P082Norm ?b) 998244353 = _ =>
        pose proof (P082Norm_range b) as Hnormrange
    end.
    unfold P082Index in Holdrange.
    unfold P082Norm, P082Modulus in Hnormrange |- *.
    rewrite Z.rem_mod_nonneg by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst j. subst W.
  unfold P082SemanticProgress in *.
  destruct PreH33 as [Hcols Hrows].
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in PreH32.
  destruct PreH32 as [[[HlenD [HlenP Hbase]] Hdonecols] Hdone].
  split.
  - intros col row Hcol Hrow.
    specialize (Hcols col row ltac:(lia) Hrow).
    unfold P082SemanticCell in *.
    destruct Hcols as [Hd Hp].
    assert (Htarget : 0 <= P082Index k_pre row col < (n_pre + 1) * (k_pre + 1)).
    { apply P082Index_bounds; lia. }
    assert (Hneq : P082Index k_pre i k_pre <> P082Index k_pre row col).
    { intro Heq. unfold P082Index in Heq.
      destruct (Z_lt_ge_dec row i) as [Hri|Hri].
      - assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia.
      - destruct (Z.eq_dec row i) as [->|Hne]; [lia|].
        assert (Hmul : (i + 1) * (k_pre + 1) <= row * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia. }
    split.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenD. unfold P082Index. lia.
      * rewrite HlenD. exact Htarget.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenP. unfold P082Index. lia.
      * rewrite HlenP. exact Htarget.
  - intros row Hrow.
    destruct (Z_lt_ge_dec row i) as [Hlt|Hge].
    + specialize (Hrows row ltac:(lia)).
      unfold P082SemanticCell in *.
      destruct Hrows as [Hd Hp].
      assert (Htarget : 0 <= P082Index k_pre row k_pre < (n_pre + 1) * (k_pre + 1)).
      { apply P082Index_bounds; lia. }
      assert (Hneq : P082Index k_pre i k_pre <> P082Index k_pre row k_pre).
      { intro Heq. unfold P082Index in Heq.
        assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia. }
      split.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenD. unfold P082Index. lia.
        -- rewrite HlenD. exact Htarget.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenP. unfold P082Index. lia.
        -- rewrite HlenP. exact Htarget.
    + assert (row = i) by lia. subst row.
      pose proof (Hcols (k_pre - 1) (i - 1) ltac:(lia) ltac:(lia)) as Hkm1.
      pose proof (Hrows (i - 1) ltac:(lia)) as Hk.
      unfold P082SemanticCell in Hkm1, Hk |- *.
      destruct Hkm1 as [Hkm1d Hkm1p]. destruct Hk as [Hkd Hkp].
      unfold P082Index in Hkm1d, Hkm1p, Hkd, Hkp.
      destruct (Z_lt_dec (k_pre - 1) k_pre); [|lia].
      destruct (Z_lt_dec k_pre k_pre); [lia|].
      split.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite P082Norm_c_normalize__semantic_updates.
        rewrite Hkm1p, Hkp.
        rewrite P082Norm_add_norm__semantic_updates.
        rewrite <- P082SaturatedCoreCount_recurrence_small by lia.
        reflexivity.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenP. unfold P082Index. lia. }
        rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite P082Norm_c_normalize__semantic_updates.
        rewrite Hkm1p, Hkp.
        match goal with
        | |- Z.rem (P082Norm ?a + P082Norm ?b) 998244353 = _ =>
            pose proof (P082Norm_range a); pose proof (P082Norm_range b)
        end.
        rewrite Z.rem_mod_nonneg by lia.
        rewrite P082Norm_add_norm__semantic_updates.
        rewrite <- P082SaturatedCoreCount_recurrence_small by lia.
        unfold P082Norm.
        rewrite <- Zplus_mod.
        rewrite <- P082PrefixCoreCount_recurrence_saturated by lia.
        reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_2 : solver_entail_wit_12_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst j. subst W.
  pose proof PreH32 as Hstate.
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in Hstate.
  destruct Hstate as [[[HlenD [HlenP [Hrange [Hcol1 Hrow0]]]] Hold] Hcurrent].
  eapply P082ColumnProgress_step_saturated__saturated_updates;
    try eassumption; try lia.
  - unfold P082RawCell, P082Index.
    destruct (Z_le_dec 3 i); [lia|].
    destruct (Z.eq_dec k_pre k_pre); [|contradiction].
    rewrite P082Norm_c_normalize__semantic_updates. f_equal. ring.
  - rewrite Znth_replace_Znth_Same.
    2:{ rewrite HlenD. unfold P082Index. lia. }
    pose proof (Hrange (P082Index k_pre (i - 1) k_pre)
      ltac:(rewrite HlenD; apply P082Index_bounds; lia)) as [_ Holdrange].
    rewrite P082Norm_c_normalize__semantic_updates.
    match goal with
    | |- Z.rem (?a + P082Norm ?b) 998244353 = _ =>
        pose proof (P082Norm_range b) as Hnormrange
    end.
    unfold P082Index in Holdrange.
    unfold P082Norm, P082Modulus in Hnormrange |- *.
    rewrite Z.rem_mod_nonneg by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_1 : solver_entail_wit_12_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  unfold P082SemanticProgress in *.
  destruct PreH30 as [Hcols Hrows].
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in PreH29.
  destruct PreH29 as [[[HlenD [HlenP Hbase]] Hdonecols] Hdone].
  split.
  - intros col row Hcol Hrow.
    specialize (Hcols col row ltac:(lia) Hrow).
    unfold P082SemanticCell in *.
    destruct Hcols as [Hd Hp].
    assert (Htarget : 0 <= P082Index k_pre row col < (n_pre + 1) * (k_pre + 1)).
    { apply P082Index_bounds; lia. }
    assert (Hneq : P082Index k_pre i j <> P082Index k_pre row col).
    { intro Heq. unfold P082Index in Heq.
      destruct (Z_lt_ge_dec row i) as [Hri|Hri].
      - assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia.
      - destruct (Z.eq_dec row i) as [->|Hne]; [lia|].
        assert (Hmul : (i + 1) * (k_pre + 1) <= row * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia. }
    split.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenD. unfold P082Index. lia.
      * rewrite HlenD. exact Htarget.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenP. unfold P082Index. lia.
      * rewrite HlenP. exact Htarget.
  - intros row Hrow.
    destruct (Z_lt_ge_dec row i) as [Hlt|Hge].
    + specialize (Hrows row ltac:(lia)).
      unfold P082SemanticCell in *.
      destruct Hrows as [Hd Hp].
      assert (Htarget : 0 <= P082Index k_pre row j < (n_pre + 1) * (k_pre + 1)).
      { apply P082Index_bounds; lia. }
      assert (Hneq : P082Index k_pre i j <> P082Index k_pre row j).
      { intro Heq. unfold P082Index in Heq.
        assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia. }
      split.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenD. unfold P082Index. lia.
        -- rewrite HlenD. exact Htarget.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenP. unfold P082Index. lia.
        -- rewrite HlenP. exact Htarget.
    + assert (row = i) by lia. subst row.
      pose proof (Hcols (j - 1) (i - 1) ltac:(lia) ltac:(lia)) as Hjm1p.
      pose proof (Hcols (j - 1) (i - 2) ltac:(lia) ltac:(lia)) as Hjm1d.
      pose proof (Hrows (i - 1) ltac:(lia)) as Hj.
      unfold P082SemanticCell in Hjm1p, Hjm1d, Hj |- *.
      destruct Hjm1p as [Hjm1pd Hjm1pp].
      destruct Hjm1d as [Hjm1dd Hjm1dp].
      destruct Hj as [Hjd Hjp].
      unfold P082Index in Hjm1pd, Hjm1pp, Hjm1dd, Hjm1dp, Hjd, Hjp.
      destruct (Z_lt_dec (j - 1) k_pre); [|lia].
      destruct (Z_lt_dec j k_pre); [|lia].
      split.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite P082Norm_c_normalize__semantic_updates.
        rewrite Hjm1pp, Hjm1dd.
        rewrite P082Norm_sub_norm__semantic_updates.
        rewrite <- P082ExactCoreCount_recurrence_large by lia.
        reflexivity.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenP. unfold P082Index. lia. }
        rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite P082Norm_c_normalize__semantic_updates.
        rewrite Hjm1pp, Hjm1dd, Hjp.
        match goal with
        | |- Z.rem (P082Norm ?a + P082Norm ?b) 998244353 = _ =>
            pose proof (P082Norm_range a); pose proof (P082Norm_range b)
        end.
        rewrite Z.rem_mod_nonneg by lia.
        rewrite P082Norm_sub_norm__semantic_updates.
        rewrite <- P082ExactCoreCount_recurrence_large by lia.
        unfold P082Norm.
        rewrite <- Zplus_mod.
        rewrite <- P082PrefixCoreCount_recurrence_exact by lia.
        reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_2 : solver_entail_wit_12_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  pose proof PreH29 as Hstate.
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in Hstate.
  destruct Hstate as [[[HlenD [HlenP [Hrange [Hcol1 Hrow0]]]] Hold] Hcurrent].
  eapply P082ColumnProgress_step_ordinary__ordinary_updates;
    try eassumption; try lia.
  - unfold P082RawCell, P082Index.
    destruct (Z_le_dec 3 i); [|lia].
    destruct (Z.eq_dec j k_pre); [contradiction|].
    rewrite P082Norm_c_normalize__semantic_updates. f_equal. ring.
  - match goal with
    | |- _ = Z.rem (_ + Znth ?idx (replace_Znth ?idx ?v ?l) 0) _ =>
        assert (Hsame : Znth idx (replace_Znth idx v l) 0 = v)
    end.
    { apply Znth_replace_Znth_Same. rewrite HlenD. unfold P082Index. lia. }
    unfold P082Index in Hsame |- *.
    rewrite Hsame. unfold P082Modulus. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_1 : solver_entail_wit_12_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  unfold P082SemanticProgress in *.
  destruct PreH26 as [Hcols Hrows].
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in PreH25.
  destruct PreH25 as [[[HlenD [HlenP Hbase]] Hdonecols] Hdone].
  split.
  - intros col row Hcol Hrow.
    specialize (Hcols col row ltac:(lia) Hrow).
    unfold P082SemanticCell in *.
    destruct Hcols as [Hd Hp].
    assert (Htarget : 0 <= P082Index k_pre row col < (n_pre + 1) * (k_pre + 1)).
    { apply P082Index_bounds; lia. }
    assert (Hneq : P082Index k_pre i j <> P082Index k_pre row col).
    { intro Heq. unfold P082Index in Heq.
      destruct (Z_lt_ge_dec row i) as [Hri|Hri].
      - assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia.
      - destruct (Z.eq_dec row i) as [->|Hne]; [lia|].
        assert (Hmul : (i + 1) * (k_pre + 1) <= row * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia. }
    split.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenD. unfold P082Index. lia.
      * rewrite HlenD. exact Htarget.
    + rewrite Znth_replace_Znth_Diff; try assumption.
      * rewrite HlenP. unfold P082Index. lia.
      * rewrite HlenP. exact Htarget.
  - intros row Hrow.
    destruct (Z_lt_ge_dec row i) as [Hlt|Hge].
    + specialize (Hrows row ltac:(lia)).
      unfold P082SemanticCell in *.
      destruct Hrows as [Hd Hp].
      assert (Htarget : 0 <= P082Index k_pre row j < (n_pre + 1) * (k_pre + 1)).
      { apply P082Index_bounds; lia. }
      assert (Hneq : P082Index k_pre i j <> P082Index k_pre row j).
      { intro Heq. unfold P082Index in Heq.
        assert (Hmul : row * (k_pre + 1) <= (i - 1) * (k_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. } lia. }
      split.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenD. unfold P082Index. lia.
        -- rewrite HlenD. exact Htarget.
      * rewrite Znth_replace_Znth_Diff; try assumption.
        -- rewrite HlenP. unfold P082Index. lia.
        -- rewrite HlenP. exact Htarget.
    + assert (row = i) by lia. subst row.
      pose proof (Hcols (j - 1) (i - 1) ltac:(lia) ltac:(lia)) as Hjm1p.
      pose proof (Hrows (i - 1) ltac:(lia)) as Hj.
      unfold P082SemanticCell in Hjm1p, Hj |- *.
      destruct Hjm1p as [Hjm1pd Hjm1pp].
      destruct Hj as [Hjd Hjp].
      unfold P082Index in Hjm1pd, Hjm1pp, Hjd, Hjp.
      destruct (Z_lt_dec (j - 1) k_pre); [|lia].
      destruct (Z_lt_dec j k_pre); [|lia].
      split.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite P082Norm_c_normalize__semantic_updates.
        rewrite Hjm1pp.
        rewrite <- P082ExactCoreCount_recurrence_small by lia.
        unfold P082Norm, P082Modulus.
        rewrite Z.mod_mod by lia.
        reflexivity.
      * rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenP. unfold P082Index. lia. }
        rewrite Znth_replace_Znth_Same.
        2:{ rewrite HlenD. unfold P082Index. lia. }
        rewrite P082Norm_c_normalize__semantic_updates.
        rewrite Hjm1pp, Hjp.
        match goal with
        | |- Z.rem (P082Norm ?a + P082Norm ?b) 998244353 = _ =>
            pose proof (P082Norm_range a); pose proof (P082Norm_range b)
        end.
        rewrite Z.rem_mod_nonneg by lia.
        rewrite <- P082ExactCoreCount_recurrence_small by lia.
        unfold P082Norm, P082Modulus.
        repeat rewrite Z.mod_mod by lia.
        rewrite <- Zplus_mod.
        rewrite <- P082PrefixCoreCount_recurrence_exact by lia.
        reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_2 : solver_entail_wit_12_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst W.
  pose proof PreH25 as Hstate.
  unfold P082ColumnProgress, P082ColumnsState, P082BaseColumns in Hstate.
  destruct Hstate as [[[HlenD [HlenP [Hrange [Hcol1 Hrow0]]]] Hold] Hcurrent].
  eapply P082ColumnProgress_step_ordinary__ordinary_updates;
    try eassumption; try lia.
  - unfold P082RawCell, P082Index.
    destruct (Z_le_dec 3 i); [lia|].
    destruct (Z.eq_dec j k_pre); [contradiction|].
    rewrite P082Norm_c_normalize__semantic_updates. f_equal. ring.
  - match goal with
    | |- _ = Z.rem (_ + Znth ?idx (replace_Znth ?idx ?v ?l) 0) _ =>
        assert (Hsame : Znth idx (replace_Znth idx v l) 0 = v)
    end.
    { apply Znth_replace_Znth_Same. rewrite HlenD. unfold P082Index. lia. }
    unfold P082Index in Hsame |- *.
    rewrite Hsame. unfold P082Modulus. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    eapply P082SemanticProgress_complete;
    replace (n_pre + 1) with i by lia;
    assumption).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    eapply P082ColumnProgress_complete;
    replace (n_pre + 1) with i by lia;
    assumption).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_16_split_goal_1 : solver_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = k_pre + 1) by lia.
  subst W.
  assert (Hkn : k_pre <= n_pre).
  { unfold Zmin in PreH15.
    pose proof (Z.le_min_l n_pre 10).
    lia. }
  pose proof PreH20 as Hstate.
  unfold P082ColumnsState, P082BaseColumns in Hstate.
  destruct Hstate as [[Hdl [Hpl [Hrange [Hbase Hzero]]]] Hcells].
  pose proof (Hrange (n_pre * (k_pre + 1) + k_pre)
    ltac:(rewrite Hdl; exact (conj PreH8 PreH9))) as [Hnonneg1 Hupper1].
  pose proof (Hrange ((n_pre - 2) * (k_pre + 1) + (k_pre - 1))
    ltac:(rewrite Hdl; exact (conj PreH1 PreH2))) as [Hnonneg2 Hupper2].
  pose proof (Hrange ((n_pre - 2) * (k_pre + 1) + k_pre)
    ltac:(rewrite Hdl; exact (conj PreH3 PreH4))) as [Hnonneg3 Hupper3].
  pose proof (P082Semantic_final_cells n_pre k_pre dl pl_2
    PreH14 PreH12 ltac:(rewrite <- Hj; exact PreH21)) as Hfinal_cells.
  unfold P082FinalValue.
  split.
  - unfold P082FinalExpression, P082Norm, P082Modulus, P082Index.
    rewrite Z.rem_mod_nonneg by lia.
    reflexivity.
  - rewrite Z.rem_mod_nonneg by lia.
    change (Spec n_pre k_pre (P082FinalExpression k_pre n_pre dl)).
    rewrite (P082Semantic_final_expression n_pre k_pre dl pl_2
      PreH14 PreH12).
    + apply P082Spec_CanonicalAnswer; lia.
    + rewrite <- Hj. exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold P082FinalValue in *; tauto).
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range
         ((n_pre + 1) * (k_pre + 1)) 32 ltac:(lia));
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range
         ((n_pre + 1) * (k_pre + 1)) 32 ltac:(lia));
    lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
Qed.
