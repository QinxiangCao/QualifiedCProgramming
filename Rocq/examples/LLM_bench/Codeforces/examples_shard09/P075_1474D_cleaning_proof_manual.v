From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P075_1474D_cleaning_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P075_1474D_cleaning_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH4 (i - 1) ltac:(lia)).
  specialize (PreH10 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  replace ((i - 1) - 0) with (i - 1) by lia.
  rewrite app_Znth1 by lia.
  change INT64_MAX with 9223372036854775807.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH4 (i - 1) ltac:(lia)).
  specialize (PreH10 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  replace ((i - 1) - 0) with (i - 1) by lia.
  rewrite app_Znth1 by lia.
  change INT64_MIN with (-9223372036854775808).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH4 (i - 1) ltac:(lia)).
  specialize (PreH16 0 ltac:(lia)).
  rewrite Znth_cons by lia.
  replace ((i + 1) - (i + 1)) with 0 by lia.
  change INT64_MAX with 9223372036854775807.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH4 (i - 1) ltac:(lia)).
  specialize (PreH16 0 ltac:(lia)).
  rewrite Znth_cons by lia.
  replace ((i + 1) - (i + 1)) with 0 by lia.
  change INT64_MIN with (-9223372036854775808).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_1 : solver_safety_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH7 i ltac:(lia)).
  specialize (PreH17 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  change INT64_MAX with 9223372036854775807.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_38_split_goal_2 : solver_safety_wit_38_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH7 i ltac:(lia)).
  specialize (PreH17 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  change INT64_MIN with (-9223372036854775808).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_38_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_44_split_goal_1 : solver_safety_wit_44_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH8 (i - 1) ltac:(lia)) as Hprev_value.
  pose proof (PreH8 i ltac:(lia)) as Hcur_value.
  specialize (PreH18 (i - 1) ltac:(lia)).
  repeat rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  change INT64_MAX with 9223372036854775807.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_44_split_goal_2 : solver_safety_wit_44_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH8 (i - 1) ltac:(lia)) as Hprev_value.
  pose proof (PreH8 i ltac:(lia)) as Hcur_value.
  specialize (PreH18 (i - 1) ltac:(lia)).
  repeat rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  change INT64_MIN with (-9223372036854775808).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_44_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_44_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (1 :: nil) (0 :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_single pre_pre 0 0).
    sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
        pre_pre 0 (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (CharArray.seg_single okpre_pre 0 1).
      sep_apply_l_atomic
        (CharArray.missing_i_shape_to_seg_shape_head
          okpre_pre 0 (n_pre + 1)).
      * dump_pre_spatial. lia.
      * replace (0 + 1) with 1 by lia.
        repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + apply prefix_residual_state_init__prefix_construction.
    + intros k Hk.
      apply prefix_residual_init_bound__prefix_construction.
      exact Hk.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpre_shape :
    Int64Array.seg_shape pre_pre (i + 1) (n_pre + 1) |--
    Int64Array.missing_i_shape pre_pre i i (n_pre + 1)).
  { rewrite Int64Array.missing_i_shape_unfold by lia.
    Left.
    split_pure_spatial.
    - cancel (Int64Array.seg_shape pre_pre (i + 1) (n_pre + 1)).
    - dump_pre_spatial. lia. }
  assert (Hokpre_shape :
    CharArray.seg_shape okpre_pre (i + 1) (n_pre + 1) |--
    CharArray.missing_i_shape okpre_pre i i (n_pre + 1)).
  { rewrite CharArray.missing_i_shape_unfold by lia.
    Left.
    split_pure_spatial.
    - cancel (CharArray.seg_shape okpre_pre (i + 1) (n_pre + 1)).
    - dump_pre_spatial. lia. }
  sep_apply_r_atomic Hpre_shape.
  sep_apply_r_atomic Hokpre_shape.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i - 1) - 0) with (i - 1) in * by lia.
  assert (Hcurrent_value :
    Znth i (0 :: values) 0 = Znth (i - 1) values 0).
  { rewrite Znth_cons by lia.
    replace (i - 1) with (i - 1) by lia.
    reflexivity. }
  assert (Hprevious_residual :
    Znth (i - 1) (pre_values_2 ++ old_pre_i :: nil) 0 =
    Znth (i - 1) pre_values_2 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  assert (Hprevious_flag :
    Znth (i - 1) (okpre_values_2 ++ old_okpre_i :: nil) 0 =
    Znth (i - 1) okpre_values_2 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  rewrite Hcurrent_value, Hprevious_residual, Hprevious_flag in *.
  set (r :=
    Znth (i - 1) values 0 - Znth (i - 1) pre_values_2 0).
  assert (Hpre_replace :
    replace_Znth i r (pre_values_2 ++ old_pre_i :: nil) =
    pre_values_2 ++ r :: nil).
  { rewrite <- PreH8.
    apply replace_Znth_app_last__prefix_construction. }
  assert (Hflag_replace :
    replace_Znth i 0 (okpre_values_2 ++ old_okpre_i :: nil) =
    okpre_values_2 ++ 0 :: nil).
  { rewrite <- PreH9.
    apply replace_Znth_app_last__prefix_construction. }
  rewrite Hpre_replace, Hflag_replace.
  Exists (okpre_values_2 ++ 0 :: nil) (pre_values_2 ++ r :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
        pre_pre i (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.missing_i_shape_to_seg_shape_head
          okpre_pre i (n_pre + 1)).
      * dump_pre_spatial. lia.
      * sep_apply_l_atomic
          (Int64Array.full_to_seg pre_pre (i + 1)
            (pre_values_2 ++ r :: nil)).
        sep_apply_l_atomic
          (CharArray.full_to_seg okpre_pre (i + 1)
            (okpre_values_2 ++ 0 :: nil)).
        repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + subst r.
      eapply prefix_residual_extend_prior_false__prefix_construction;
        eauto; reflexivity.
    + subst r.
      eapply prefix_residual_extend_bound__prefix_construction;
        eauto; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i - 1) - 0) with (i - 1) in * by lia.
  assert (Hcurrent_value :
    Znth i (0 :: values) 0 = Znth (i - 1) values 0).
  { rewrite Znth_cons by lia.
    replace (i - 1) with (i - 1) by lia.
    reflexivity. }
  assert (Hprevious_residual :
    Znth (i - 1) (pre_values_2 ++ old_pre_i :: nil) 0 =
    Znth (i - 1) pre_values_2 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  assert (Hprevious_flag :
    Znth (i - 1) (okpre_values_2 ++ old_okpre_i :: nil) 0 =
    Znth (i - 1) okpre_values_2 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  rewrite Hcurrent_value, Hprevious_residual, Hprevious_flag in *.
  set (r :=
    Znth (i - 1) values 0 - Znth (i - 1) pre_values_2 0).
  assert (Hrnonneg : 0 <= r).
  { subst r.
    rewrite Znth_replace_Znth_Same in PreH1.
    - lia.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia. }
  assert (Hpre_replace :
    replace_Znth i r (pre_values_2 ++ old_pre_i :: nil) =
    pre_values_2 ++ r :: nil).
  { rewrite <- PreH9.
    apply replace_Znth_app_last__prefix_construction. }
  assert (Hflag_replace :
    replace_Znth i 1 (okpre_values_2 ++ old_okpre_i :: nil) =
    okpre_values_2 ++ 1 :: nil).
  { rewrite <- PreH10.
    apply replace_Znth_app_last__prefix_construction. }
  rewrite Hpre_replace, Hflag_replace.
  Exists (okpre_values_2 ++ 1 :: nil) (pre_values_2 ++ r :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
        pre_pre i (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.missing_i_shape_to_seg_shape_head
          okpre_pre i (n_pre + 1)).
      * dump_pre_spatial. lia.
      * sep_apply_l_atomic
          (Int64Array.full_to_seg pre_pre (i + 1)
            (pre_values_2 ++ r :: nil)).
        sep_apply_l_atomic
          (CharArray.full_to_seg okpre_pre (i + 1)
            (okpre_values_2 ++ 1 :: nil)).
        repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + subst r.
      eapply prefix_residual_extend_success__prefix_construction;
        eauto.
    + subst r.
      eapply prefix_residual_extend_bound__prefix_construction;
        eauto; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i - 1) - 0) with (i - 1) in * by lia.
  assert (Hcurrent_value :
    Znth i (0 :: values) 0 = Znth (i - 1) values 0).
  { rewrite Znth_cons by lia.
    replace (i - 1) with (i - 1) by lia.
    reflexivity. }
  assert (Hprevious_residual :
    Znth (i - 1) (pre_values_2 ++ old_pre_i :: nil) 0 =
    Znth (i - 1) pre_values_2 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  assert (Hprevious_flag :
    Znth (i - 1) (okpre_values_2 ++ old_okpre_i :: nil) 0 =
    Znth (i - 1) okpre_values_2 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  rewrite Hcurrent_value, Hprevious_residual, Hprevious_flag in *.
  set (r :=
    Znth (i - 1) values 0 - Znth (i - 1) pre_values_2 0).
  assert (Hrneg : r < 0).
  { subst r.
    rewrite Znth_replace_Znth_Same in PreH1.
    - exact PreH1.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia. }
  assert (Hpre_replace :
    replace_Znth i r (pre_values_2 ++ old_pre_i :: nil) =
    pre_values_2 ++ r :: nil).
  { rewrite <- PreH9.
    apply replace_Znth_app_last__prefix_construction. }
  assert (Hflag_replace :
    replace_Znth i 0 (okpre_values_2 ++ old_okpre_i :: nil) =
    okpre_values_2 ++ 0 :: nil).
  { rewrite <- PreH10.
    apply replace_Znth_app_last__prefix_construction. }
  rewrite Hpre_replace, Hflag_replace.
  Exists (okpre_values_2 ++ 0 :: nil) (pre_values_2 ++ r :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
        pre_pre i (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (CharArray.missing_i_shape_to_seg_shape_head
          okpre_pre i (n_pre + 1)).
      * dump_pre_spatial. lia.
      * sep_apply_l_atomic
          (Int64Array.full_to_seg pre_pre (i + 1)
            (pre_values_2 ++ r :: nil)).
        sep_apply_l_atomic
          (CharArray.full_to_seg okpre_pre (i + 1)
            (okpre_values_2 ++ 0 :: nil)).
        repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + subst r.
      eapply prefix_residual_extend_current_false__prefix_construction;
        eauto.
    + subst r.
      eapply prefix_residual_extend_bound__prefix_construction;
        eauto; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with (n_pre + 1) in * by lia.
  rewrite Int64Array.seg_shape_empty.
  rewrite CharArray.seg_shape_empty.
  sep_apply_l_atomic
    (Int64Array.seg_to_full pre_pre 0 (n_pre + 1) pre_values_2).
  replace (pre_pre + 0 * sizeof(INT64)) with pre_pre by lia.
  replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
  sep_apply_l_atomic
    (CharArray.seg_to_full okpre_pre 0 (n_pre + 1) okpre_values_2).
  replace (okpre_pre + 0 * sizeof(CHAR)) with okpre_pre by lia.
  replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
  sep_apply_l_atomic
    (Int64Array.full_shape_split_to_missing_i_shape
       suf_pre (n_pre + 1) (n_pre + 2)).
  - dump_pre_spatial. lia.
  - Intros old_suf_terminal.
    sep_apply_l_atomic
      (CharArray.full_shape_split_to_missing_i_shape
         oksuf_pre (n_pre + 1) (n_pre + 2)).
    + dump_pre_spatial. lia.
    + Intros old_oksuf_terminal.
      Exists old_oksuf_terminal old_suf_terminal
        okpre_values_2 pre_values_2.
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial; try lia; try assumption.
        all: try (rewrite Zlength_cons, Zlength_nil; lia).
        intros k Hk. apply PreH11. lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape64 : forall x lo hi,
    lo < hi ->
    Int64Array.missing_i_shape x (hi - 1) lo hi |--
      Int64Array.seg_shape x lo (hi - 1)).
  {
    intros x lo hi Hbound.
    unfold Int64Array.missing_i_shape, Int64Array.seg_shape.
    replace (Z.to_nat (hi - lo)) with
      (S (Z.to_nat (hi - (lo + 1)))) by lia.
    replace (hi - 1 - lo) with (hi - (lo + 1)) by lia.
    simpl.
    set (len := Z.to_nat (hi - (lo + 1))).
    assert (Hlen : len = Z.to_nat (hi - (lo + 1))) by lia.
    clearbody len. generalize dependent lo. revert hi.
    induction len; intros; simpl in *.
    - Split.
      + LLM_pre_process ltac:(lia || int_auto).
      + Intros x0. contradiction.
    - Split.
      + Intros x0.
        replace (hi - (lo + 1)) with 0 in Hlen by lia.
        simpl in Hlen. discriminate.
      + LLM_pre_process ltac:(lia || int_auto).
        Split.
        * Intros x0. Exists x0.
          sep_apply_r_atomic (IHlen hi (lo + 1)).
          -- dump_pre_spatial. lia.
          -- dump_pre_spatial.
             replace (hi - (lo + 1 + 1)) with 0 by lia.
             replace (hi - (lo + 1)) with 1 in Hlen by lia.
             simpl in *. lia.
          -- Left.
             LLM_pre_process ltac:(lia || int_auto).
        * Intros x0 x1. Exists x0.
          sep_apply_r_atomic (IHlen hi (lo + 1)).
          -- dump_pre_spatial. lia.
          -- dump_pre_spatial.
             replace (Z.to_nat (hi - (lo + 1))) with
               (S (Z.to_nat (hi - (lo + 1 + 1)))) in Hlen by lia.
             inversion Hlen. reflexivity.
          -- Right. Exists x1.
             LLM_pre_process ltac:(lia || int_auto).
  }
  assert (Hshape8 : forall x lo hi,
    lo < hi ->
    CharArray.missing_i_shape x (hi - 1) lo hi |--
      CharArray.seg_shape x lo (hi - 1)).
  {
    intros x lo hi Hbound.
    unfold CharArray.missing_i_shape, CharArray.seg_shape.
    replace (Z.to_nat (hi - lo)) with
      (S (Z.to_nat (hi - (lo + 1)))) by lia.
    replace (hi - 1 - lo) with (hi - (lo + 1)) by lia.
    simpl.
    set (len := Z.to_nat (hi - (lo + 1))).
    assert (Hlen : len = Z.to_nat (hi - (lo + 1))) by lia.
    clearbody len. generalize dependent lo. revert hi.
    induction len; intros; simpl in *.
    - Split.
      + LLM_pre_process ltac:(lia || int_auto).
      + Intros x0. contradiction.
    - Split.
      + Intros x0.
        replace (hi - (lo + 1)) with 0 in Hlen by lia.
        simpl in Hlen. discriminate.
      + LLM_pre_process ltac:(lia || int_auto).
        Split.
        * Intros x0. Exists x0.
          sep_apply_r_atomic (IHlen hi (lo + 1)).
          -- dump_pre_spatial. lia.
          -- dump_pre_spatial.
             replace (hi - (lo + 1 + 1)) with 0 by lia.
             replace (hi - (lo + 1)) with 1 in Hlen by lia.
             simpl in *. lia.
          -- Left.
             LLM_pre_process ltac:(lia || int_auto).
        * Intros x0 x1. Exists x0.
          sep_apply_r_atomic (IHlen hi (lo + 1)).
          -- dump_pre_spatial. lia.
          -- dump_pre_spatial.
             replace (Z.to_nat (hi - (lo + 1))) with
               (S (Z.to_nat (hi - (lo + 1 + 1)))) in Hlen by lia.
             inversion Hlen. reflexivity.
          -- Right. Exists x1.
             LLM_pre_process ltac:(lia || int_auto).
  }
  pose proof (Hshape64 suf_pre 0 (n_pre + 2) ltac:(lia)) as Hshape64_here.
  replace (n_pre + 2 - 1) with (n_pre + 1) in Hshape64_here by lia.
  sep_apply_l_atomic Hshape64_here.
  sep_apply_l_atomic (Int64Array.seg_single suf_pre (n_pre + 1) 0).
    replace (n_pre + 1 + 1) with (n_pre + 2) by lia.
    pose proof (Hshape8 oksuf_pre 0 (n_pre + 2) ltac:(lia)) as Hshape8_here.
    replace (n_pre + 2 - 1) with (n_pre + 1) in Hshape8_here by lia.
    sep_apply_l_atomic Hshape8_here.
    sep_apply_l_atomic (CharArray.seg_single oksuf_pre (n_pre + 1) 1).
      replace (n_pre + 1 + 1) with (n_pre + 2) by lia.
      Exists (1 :: nil) (0 :: nil) okpre_values_2 pre_values_2.
      split_pure_spatial.
      * repeat cancel.
      * split_pures; dump_pre_spatial; try lia; try assumption.
        -- rewrite Zlength_cons, Zlength_nil. lia.
        -- rewrite Zlength_cons, Zlength_nil. lia.
        -- replace (n_pre + 1) with (Zlength values + 1) by lia.
           apply suffix_residual_state_terminal_init__suffix_setup.
        -- intros q Hq.
           rewrite Zlength_cons, Zlength_nil in Hq.
           assert (q = 0) by lia. subst q.
           rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmat64 : forall x lo hi,
    lo <= hi ->
    Int64Array.seg_shape x lo hi |--
      EX l : list Z,
        “ Zlength l = hi - lo ” && Int64Array.seg x lo hi l).
  {
    intros x lo hi Hbound.
    unfold Int64Array.seg_shape, Int64Array.seg.
    set (len := Z.to_nat (hi - lo)).
    assert (Hlen : len = Z.to_nat (hi - lo)) by lia.
    clearbody len. generalize dependent lo. revert hi.
    induction len; intros; simpl in *.
    - Exists (@nil Z).
      simpl.
      LLM_pre_process ltac:(lia || int_auto).
      split_pure_spatial.
      + cancel.
      + split_pures; dump_pre_spatial.
        * rewrite Zlength_nil. lia.
        * lia.
        * reflexivity.
    - Intros x0.
      assert (Htail : len = Z.to_nat (hi - (lo + 1))).
      { replace (Z.to_nat (hi - lo)) with
          (S (Z.to_nat (hi - (lo + 1)))) in Hlen by lia.
        inversion Hlen. reflexivity. }
      sep_apply_l_atomic (IHlen hi (lo + 1) ltac:(lia) Htail).
      Intros tail.
      Exists (x0 :: tail).
      simpl.
      split_pure_spatial.
      + cancel.
      + dump_pre_spatial. rewrite Zlength_cons. lia.
  }
  assert (Hmat8 : forall x lo hi,
    lo <= hi ->
    CharArray.seg_shape x lo hi |--
      EX l : list Z,
        “ Zlength l = hi - lo ” && CharArray.seg x lo hi l).
  {
    intros x lo hi Hbound.
    unfold CharArray.seg_shape, CharArray.seg.
    set (len := Z.to_nat (hi - lo)).
    assert (Hlen : len = Z.to_nat (hi - lo)) by lia.
    clearbody len. generalize dependent lo. revert hi.
    induction len; intros; simpl in *.
    - Exists (@nil Z).
      simpl.
      LLM_pre_process ltac:(lia || int_auto).
      split_pure_spatial.
      + cancel.
      + split_pures; dump_pre_spatial.
        * rewrite Zlength_nil. lia.
        * lia.
        * reflexivity.
    - Intros x0.
      assert (Htail : len = Z.to_nat (hi - (lo + 1))).
      { replace (Z.to_nat (hi - lo)) with
          (S (Z.to_nat (hi - (lo + 1)))) in Hlen by lia.
        inversion Hlen. reflexivity. }
      sep_apply_l_atomic (IHlen hi (lo + 1) ltac:(lia) Htail).
      Intros tail.
      Exists (x0 :: tail).
      simpl.
      split_pure_spatial.
      + cancel.
      + dump_pre_spatial. rewrite Zlength_cons. lia.
  }
  sep_apply_l_atomic (Hmat64 suf_pre 0 (i + 1) ltac:(lia)).
  Intros suf_prefix.
  sep_apply_l_atomic (Hmat8 oksuf_pre 0 (i + 1) ltac:(lia)).
  Intros oksuf_prefix.
  Exists oksuf_prefix suf_prefix oksuf_values_2 suf_values_2
    okpre_values_2 pre_values_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) - (i + 1)) with 0 by lia.
  rewrite Znth_cons by lia.
  replace (i - 1) with (i - 1) by lia.
  set (new_suf_i := Znth (i - 1) values 0 - Znth 0 suf_values_2 0).
  set (suf_leading := sublist 0 i suf_prefix).
  assert (Hsuf_leading_len : Zlength suf_leading = i).
  { unfold suf_leading. rewrite Zlength_sublist; lia. }
  assert (Hsuf_prefix_split :
    suf_prefix = suf_leading ++ (Znth i suf_prefix 0 :: nil)).
  { unfold suf_leading.
    rewrite <- (sublist_self suf_prefix (i + 1)) at 1 by lia.
    rewrite (sublist_split 0 (i + 1) i suf_prefix) by lia.
    rewrite (sublist_single 0 i suf_prefix) by lia.
    reflexivity. }
  assert (Hreplace :
    replace_Znth i new_suf_i suf_prefix = suf_leading ++ (new_suf_i :: nil)).
  { rewrite Hsuf_prefix_split, <- Hsuf_leading_len.
    apply replace_Znth_app_last__suffix_step. }
  rewrite Hreplace.
  assert (Hnew_bounds :
    -1000000000 * (n_pre - i + 1) <= new_suf_i /\
    new_suf_i <= 1000000000 * (n_pre - i + 1)).
  { unfold new_suf_i.
    pose proof (PreH4 (i - 1) ltac:(lia)) as Hvalue.
    pose proof (PreH16 0 ltac:(lia)) as Htail.
    lia. }
  Exists new_suf_i oksuf_prefix_2 suf_leading oksuf_values_2
    suf_values_2 okpre_values_2 pre_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.full_to_seg suf_pre (i + 1)
        (suf_leading ++ (new_suf_i :: nil))).
    sep_apply_l_atomic
      (Int64Array.seg_split_to_seg suf_pre 0 i (i + 1)
        (suf_leading ++ (new_suf_i :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (suf_leading ++ (new_suf_i :: nil)))
      with suf_leading by
      (symmetry; rewrite <- Hsuf_leading_len;
       replace (Zlength suf_leading - 0) with (Zlength suf_leading) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0)
      (suf_leading ++ (new_suf_i :: nil))) with (new_suf_i :: nil).
    2: { rewrite <- Hsuf_leading_len.
         rewrite sublist_split_app_r with (len := Zlength suf_leading) by lia.
         replace (Zlength suf_leading - 0 - Zlength suf_leading) with 0 by lia.
         replace (Zlength suf_leading + 1 - 0 - Zlength suf_leading) with 1 by lia.
         reflexivity. }
    rewrite (Int64Array.seg_unfold suf_pre i (i + 1) nil new_suf_i) by lia.
    rewrite Int64Array.seg_empty.
    cancel (Int64Array.full a_pre (n_pre + 1) (0 :: values)).
    cancel (Int64Array.full pre_pre (n_pre + 1) pre_values_2).
    cancel (Int64Array.seg suf_pre 0 i suf_leading).
    cancel (((suf_pre + i * sizeof(INT64))) # Int64 |-> new_suf_i).
    cancel (Int64Array.seg suf_pre (i + 1) (n_pre + 2) suf_values_2).
    cancel (CharArray.full okpre_pre (n_pre + 1) okpre_values_2).
    cancel (CharArray.seg oksuf_pre 0 (i + 1) oksuf_prefix_2).
    cancel (CharArray.seg oksuf_pre (i + 1) (n_pre + 2) oksuf_values_2).
    Intros_p Htrivial. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) - (i + 1)) with 0 in PreH1 by lia.
  set (oksuf_leading := sublist 0 i oksuf_prefix).
  assert (Hleading_len : Zlength oksuf_leading = i).
  { unfold oksuf_leading. rewrite Zlength_sublist; lia. }
  assert (Hprefix_split :
    oksuf_prefix = oksuf_leading ++ (Znth i oksuf_prefix 0 :: nil)).
  { unfold oksuf_leading.
    rewrite <- (sublist_self oksuf_prefix (i + 1)) at 1 by lia.
    rewrite (sublist_split 0 (i + 1) i oksuf_prefix) by lia.
    rewrite (sublist_single 0 i oksuf_prefix) by lia. reflexivity. }
  assert (Hreplace : replace_Znth i 0 oksuf_prefix = oksuf_leading ++ (0 :: nil)).
  { rewrite Hprefix_split, <- Hleading_len.
    apply replace_Znth_app_last__suffix_step. }
  rewrite Hreplace.
  Left.
  Exists 0 new_suf_i_2 oksuf_leading suf_leading_2 oksuf_values_2
    suf_values_2 okpre_values_2 pre_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.full_to_seg oksuf_pre (i + 1) (oksuf_leading ++ (0 :: nil))).
    sep_apply_l_atomic
      (CharArray.seg_split_to_seg oksuf_pre 0 i (i + 1)
        (oksuf_leading ++ (0 :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (oksuf_leading ++ (0 :: nil)))
      with oksuf_leading by
      (symmetry; rewrite <- Hleading_len;
       replace (Zlength oksuf_leading - 0) with (Zlength oksuf_leading) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0) (oksuf_leading ++ (0 :: nil)))
      with (0 :: nil).
    2: { rewrite <- Hleading_len.
         rewrite sublist_split_app_r with (len := Zlength oksuf_leading) by lia.
         replace (Zlength oksuf_leading - 0 - Zlength oksuf_leading) with 0 by lia.
         replace (Zlength oksuf_leading + 1 - 0 - Zlength oksuf_leading) with 1 by lia.
         reflexivity. }
    rewrite (CharArray.seg_unfold oksuf_pre i (i + 1) nil 0) by lia.
    rewrite CharArray.seg_empty.
    sep_apply_l_atomic
      (Int64Array.seg_split_to_seg suf_pre 0 i (i + 1)
        (suf_leading_2 ++ (new_suf_i_2 :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (suf_leading_2 ++ (new_suf_i_2 :: nil)))
      with suf_leading_2 by
      (symmetry; rewrite <- PreH12;
       replace (Zlength suf_leading_2 - 0) with (Zlength suf_leading_2) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0)
      (suf_leading_2 ++ (new_suf_i_2 :: nil))) with (new_suf_i_2 :: nil).
    2: { rewrite <- PreH12.
         rewrite sublist_split_app_r with (len := Zlength suf_leading_2) by lia.
         replace (Zlength suf_leading_2 - 0 - Zlength suf_leading_2) with 0 by lia.
         replace (Zlength suf_leading_2 + 1 - 0 - Zlength suf_leading_2) with 1 by lia.
         reflexivity. }
    rewrite (Int64Array.seg_unfold suf_pre i (i + 1) nil new_suf_i_2) by lia.
    rewrite Int64Array.seg_empty.
    repeat cancel.
    Intros_p Htrivial1. Intros_p Htrivial2. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) - (i + 1)) with 0 in PreH2 by lia.
  assert (Hnew_nonneg : 0 <= new_suf_i_2).
  { rewrite app_Znth2 in PreH1 by lia.
    replace (i - 0 - Zlength suf_leading_2) with 0 in PreH1 by lia.
    rewrite Znth0_cons in PreH1. lia. }
  assert (Htail_one : Znth 0 oksuf_values_2 0 = 1).
  { pose proof (suffix_residual_flag_boolean values (i + 1)
      suf_values_2 oksuf_values_2 0 PreH16 ltac:(lia)) as Hbool.
    destruct Hbool; [contradiction|assumption]. }
  set (oksuf_leading := sublist 0 i oksuf_prefix).
  assert (Hleading_len : Zlength oksuf_leading = i).
  { unfold oksuf_leading. rewrite Zlength_sublist; lia. }
  assert (Hprefix_split :
    oksuf_prefix = oksuf_leading ++ (Znth i oksuf_prefix 0 :: nil)).
  { unfold oksuf_leading.
    rewrite <- (sublist_self oksuf_prefix (i + 1)) at 1 by lia.
    rewrite (sublist_split 0 (i + 1) i oksuf_prefix) by lia.
    rewrite (sublist_single 0 i oksuf_prefix) by lia. reflexivity. }
  assert (Hreplace : replace_Znth i 1 oksuf_prefix = oksuf_leading ++ (1 :: nil)).
  { rewrite Hprefix_split, <- Hleading_len.
    apply replace_Znth_app_last__suffix_step. }
  rewrite Hreplace.
  Right.
  Exists 1 new_suf_i_2 oksuf_leading suf_leading_2 oksuf_values_2
    suf_values_2 okpre_values_2 pre_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.full_to_seg oksuf_pre (i + 1) (oksuf_leading ++ (1 :: nil))).
    sep_apply_l_atomic
      (CharArray.seg_split_to_seg oksuf_pre 0 i (i + 1)
        (oksuf_leading ++ (1 :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (oksuf_leading ++ (1 :: nil)))
      with oksuf_leading by
      (symmetry; rewrite <- Hleading_len;
       replace (Zlength oksuf_leading - 0) with (Zlength oksuf_leading) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0) (oksuf_leading ++ (1 :: nil)))
      with (1 :: nil).
    2: { rewrite <- Hleading_len.
         rewrite sublist_split_app_r with (len := Zlength oksuf_leading) by lia.
         replace (Zlength oksuf_leading - 0 - Zlength oksuf_leading) with 0 by lia.
         replace (Zlength oksuf_leading + 1 - 0 - Zlength oksuf_leading) with 1 by lia.
         reflexivity. }
    rewrite (CharArray.seg_unfold oksuf_pre i (i + 1) nil 1) by lia.
    rewrite CharArray.seg_empty.
    sep_apply_l_atomic
      (Int64Array.seg_split_to_seg suf_pre 0 i (i + 1)
        (suf_leading_2 ++ (new_suf_i_2 :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (suf_leading_2 ++ (new_suf_i_2 :: nil)))
      with suf_leading_2 by
      (symmetry; rewrite <- PreH13;
       replace (Zlength suf_leading_2 - 0) with (Zlength suf_leading_2) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0)
      (suf_leading_2 ++ (new_suf_i_2 :: nil))) with (new_suf_i_2 :: nil).
    2: { rewrite <- PreH13.
         rewrite sublist_split_app_r with (len := Zlength suf_leading_2) by lia.
         replace (Zlength suf_leading_2 - 0 - Zlength suf_leading_2) with 0 by lia.
         replace (Zlength suf_leading_2 + 1 - 0 - Zlength suf_leading_2) with 1 by lia.
         reflexivity. }
    rewrite (Int64Array.seg_unfold suf_pre i (i + 1) nil new_suf_i_2) by lia.
    rewrite Int64Array.seg_empty.
    repeat cancel.
    Intros_p Htrivial1. Intros_p Htrivial2. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) - (i + 1)) with 0 in PreH2 by lia.
  assert (Hnew_negative : new_suf_i_2 < 0).
  { rewrite app_Znth2 in PreH1 by lia.
    replace (i - 0 - Zlength suf_leading_2) with 0 in PreH1 by lia.
    rewrite Znth0_cons in PreH1. exact PreH1. }
  set (oksuf_leading := sublist 0 i oksuf_prefix).
  assert (Hleading_len : Zlength oksuf_leading = i).
  { unfold oksuf_leading. rewrite Zlength_sublist; lia. }
  assert (Hprefix_split :
    oksuf_prefix = oksuf_leading ++ (Znth i oksuf_prefix 0 :: nil)).
  { unfold oksuf_leading.
    rewrite <- (sublist_self oksuf_prefix (i + 1)) at 1 by lia.
    rewrite (sublist_split 0 (i + 1) i oksuf_prefix) by lia.
    rewrite (sublist_single 0 i oksuf_prefix) by lia. reflexivity. }
  assert (Hreplace : replace_Znth i 0 oksuf_prefix = oksuf_leading ++ (0 :: nil)).
  { rewrite Hprefix_split, <- Hleading_len.
    apply replace_Znth_app_last__suffix_step. }
  rewrite Hreplace.
  Left.
  Exists 0 new_suf_i_2 oksuf_leading suf_leading_2 oksuf_values_2
    suf_values_2 okpre_values_2 pre_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.full_to_seg oksuf_pre (i + 1) (oksuf_leading ++ (0 :: nil))).
    sep_apply_l_atomic
      (CharArray.seg_split_to_seg oksuf_pre 0 i (i + 1)
        (oksuf_leading ++ (0 :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (oksuf_leading ++ (0 :: nil)))
      with oksuf_leading by
      (symmetry; rewrite <- Hleading_len;
       replace (Zlength oksuf_leading - 0) with (Zlength oksuf_leading) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0) (oksuf_leading ++ (0 :: nil)))
      with (0 :: nil).
    2: { rewrite <- Hleading_len.
         rewrite sublist_split_app_r with (len := Zlength oksuf_leading) by lia.
         replace (Zlength oksuf_leading - 0 - Zlength oksuf_leading) with 0 by lia.
         replace (Zlength oksuf_leading + 1 - 0 - Zlength oksuf_leading) with 1 by lia.
         reflexivity. }
    rewrite (CharArray.seg_unfold oksuf_pre i (i + 1) nil 0) by lia.
    rewrite CharArray.seg_empty.
    sep_apply_l_atomic
      (Int64Array.seg_split_to_seg suf_pre 0 i (i + 1)
        (suf_leading_2 ++ (new_suf_i_2 :: nil)) ltac:(lia)).
    replace (sublist 0 (i - 0) (suf_leading_2 ++ (new_suf_i_2 :: nil)))
      with suf_leading_2 by
      (symmetry; rewrite <- PreH13;
       replace (Zlength suf_leading_2 - 0) with (Zlength suf_leading_2) by lia;
       apply sublist_app_exact1).
    replace (sublist (i - 0) (i + 1 - 0)
      (suf_leading_2 ++ (new_suf_i_2 :: nil))) with (new_suf_i_2 :: nil).
    2: { rewrite <- PreH13.
         rewrite sublist_split_app_r with (len := Zlength suf_leading_2) by lia.
         replace (Zlength suf_leading_2 - 0 - Zlength suf_leading_2) with 0 by lia.
         replace (Zlength suf_leading_2 + 1 - 0 - Zlength suf_leading_2) with 1 by lia.
         reflexivity. }
    rewrite (Int64Array.seg_unfold suf_pre i (i + 1) nil new_suf_i_2) by lia.
    rewrite Int64Array.seg_empty.
    repeat cancel.
    Intros_p Htrivial1. Intros_p Htrivial2. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew_state : SuffixResidualState values i
    (new_suf_i :: suf_values_2) (new_oksuf_i :: oksuf_values_2)).
  { apply (suffix_residual_prepend_core__suffix_step values i
      suf_values_2 oksuf_values_2 new_suf_i new_oksuf_i).
    - lia.
    - lia.
    - exact PreH14.
    - exact PreH15.
    - left. exact PreH16.
    - split; assumption. }
  assert (Hnew_bound : forall q,
    0 <= q < Zlength (new_suf_i :: suf_values_2) ->
    -1000000000 * (n_pre - (i - 1) - q) <=
      Znth q (new_suf_i :: suf_values_2) 0 /\
    Znth q (new_suf_i :: suf_values_2) 0 <=
      1000000000 * (n_pre - (i - 1) - q)).
  { eapply suffix_residual_prepend_bound__suffix_step; eauto. }
  Exists (new_oksuf_i :: oksuf_values_2) (new_suf_i :: suf_values_2)
    okpre_values_2 pre_values_2.
  split_pure_spatial.
  - replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic
      (Int64Array.seg_single suf_pre i new_suf_i).
    sep_apply_l_atomic
      (CharArray.seg_single oksuf_pre i new_oksuf_i).
    sep_apply_l_atomic
      (Int64Array.seg_merge_to_seg suf_pre i (i + 1) (n_pre + 2)
        (new_suf_i :: nil) suf_values_2 ltac:(lia)).
    sep_apply_l_atomic
      (CharArray.seg_merge_to_seg oksuf_pre i (i + 1) (n_pre + 2)
        (new_oksuf_i :: nil) oksuf_values_2 ltac:(lia)).
    change ((new_suf_i :: nil) ++ suf_values_2) with (new_suf_i :: suf_values_2).
    change ((new_oksuf_i :: nil) ++ oksuf_values_2) with
      (new_oksuf_i :: oksuf_values_2).
    sep_apply_l_atomic (Int64Array.seg_to_seg_shape suf_pre 0 i suf_leading).
    sep_apply_l_atomic (CharArray.seg_to_seg_shape oksuf_pre 0 i oksuf_leading).
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons; lia);
      try (replace (i - 1 + 1) with i by lia; exact Hnew_state).
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnew_state : SuffixResidualState values i
    (new_suf_i :: suf_values_2) (new_oksuf_i :: oksuf_values_2)).
  { apply (suffix_residual_prepend_core__suffix_step values i
      suf_values_2 oksuf_values_2 new_suf_i new_oksuf_i).
    - lia.
    - lia.
    - exact PreH14.
    - exact PreH15.
    - right. exact PreH16.
    - split; assumption. }
  assert (Hnew_bound : forall q,
    0 <= q < Zlength (new_suf_i :: suf_values_2) ->
    -1000000000 * (n_pre - (i - 1) - q) <=
      Znth q (new_suf_i :: suf_values_2) 0 /\
    Znth q (new_suf_i :: suf_values_2) 0 <=
      1000000000 * (n_pre - (i - 1) - q)).
  { eapply suffix_residual_prepend_bound__suffix_step; eauto. }
  Exists (new_oksuf_i :: oksuf_values_2) (new_suf_i :: suf_values_2)
    okpre_values_2 pre_values_2.
  split_pure_spatial.
  - replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic
      (Int64Array.seg_single suf_pre i new_suf_i).
    sep_apply_l_atomic
      (CharArray.seg_single oksuf_pre i new_oksuf_i).
    sep_apply_l_atomic
      (Int64Array.seg_merge_to_seg suf_pre i (i + 1) (n_pre + 2)
        (new_suf_i :: nil) suf_values_2 ltac:(lia)).
    sep_apply_l_atomic
      (CharArray.seg_merge_to_seg oksuf_pre i (i + 1) (n_pre + 2)
        (new_oksuf_i :: nil) oksuf_values_2 ltac:(lia)).
    change ((new_suf_i :: nil) ++ suf_values_2) with (new_suf_i :: suf_values_2).
    change ((new_oksuf_i :: nil) ++ oksuf_values_2) with
      (new_oksuf_i :: oksuf_values_2).
    sep_apply_l_atomic (Int64Array.seg_to_seg_shape suf_pre 0 i suf_leading).
    sep_apply_l_atomic (CharArray.seg_to_seg_shape oksuf_pre 0 i oksuf_leading).
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons; lia);
      try (replace (i - 1 + 1) with i by lia; exact Hnew_state).
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = 0) by lia.
  subst i.
  assert (Hdirect :
    ~ DirectResidualSuccess pre_values_2 okpre_values_2 (Zlength values)).
  {
    unfold DirectResidualSuccess.
    intros [Hok _].
    rewrite <- PreH5 in Hok.
    lia.
  }
  pose proof
    (checked_swap_prefix_init values pre_values_2 suf_values_2
       okpre_values_2 oksuf_values_2 Hdirect) as Hchecked.
  Exists oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2.
  split_pure_spatial.
  - replace (0 + 1) with 1 by lia.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    intros q Hq.
    specialize (PreH16 q ltac:(rewrite PreH11; lia)).
    replace (n_pre - 0 - q) with (n_pre - q) in PreH16 by lia.
    exact PreH16.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = 0) by lia.
  subst i.
  assert (Hdirect :
    ~ DirectResidualSuccess pre_values_2 okpre_values_2 (Zlength values)).
  {
    unfold DirectResidualSuccess.
    intros [_ Hres].
    rewrite <- PreH6 in Hres.
    contradiction.
  }
  pose proof
    (checked_swap_prefix_init values pre_values_2 suf_values_2
       okpre_values_2 oksuf_values_2 Hdirect) as Hchecked.
  Exists oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2.
  split_pure_spatial.
  - replace (0 + 1) with 1 by lia.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
    intros q Hq.
    specialize (PreH17 q ltac:(rewrite PreH12; lia)).
    replace (n_pre - 0 - q) with (n_pre - q) in PreH17 by lia.
    exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply checked_swap_prefix_step; [exact PreH19 |].
  unfold SwapResidualSuccess.
  cbn.
  intros (_ & _ & _ & _ & Heq).
  rewrite !Znth_cons in PreH1 by lia.
  replace (i + 1 - 1) with i in PreH1 by lia.
  replace (i + 2 - 1) with (i + 1) in PreH1 by lia.
  apply PreH1.
  exact Heq.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply checked_swap_prefix_step; [exact PreH15 |].
  unfold SwapResidualSuccess.
  cbn.
  intros (Hflag & _).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_1 : solver_entail_wit_12_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply checked_swap_prefix_step; [exact PreH16 |].
  unfold SwapResidualSuccess.
  cbn.
  intros (_ & Hflag & _).
  replace (i + 2 - 1) with (i + 1) in PreH1 by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_1 : solver_entail_wit_12_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply checked_swap_prefix_step; [exact PreH17 |].
  unfold SwapResidualSuccess.
  cbn.
  intros (_ & _ & Hx & _).
  rewrite Znth_cons in PreH1 by lia.
  replace (i + 1 - 1) with i in PreH1 by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_1 : solver_entail_wit_12_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply checked_swap_prefix_step; [exact PreH18 |].
  unfold SwapResidualSuccess.
  cbn.
  intros (_ & _ & _ & Hy & _).
  rewrite !Znth_cons in PreH1 by lia.
  replace (i + 1 - 1) with i in PreH1 by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_5_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i = n_pre) by lia.
  subst i.
  unfold Spec.
  right.
  split; [reflexivity|].
  intro Hclean.
  pose proof (proj1
    (cleanable_residual_characterization__final_result
      values pre_values suf_values okpre_values oksuf_values
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH12 PreH13)
    Hclean) as Hcases.
  unfold CheckedSwapPrefix in PreH14.
  destruct PreH14 as [Hdirect Hswaps].
  destruct Hcases as [Hcase | [j [Hj Hcase]]].
  - exact (Hdirect Hcase).
  - exact (Hswaps j ltac:(lia) Hcase).
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (Int64Array.full_to_full_shape pre_pre (n_pre + 1) pre_values).
  sep_apply_l_atomic
    (Int64Array.seg_to_seg_shape suf_pre 1 (n_pre + 2) suf_values).
  sep_apply_l_atomic
    (Int64Array.seg_shape_merge_to_seg_shape suf_pre 0 1 (n_pre + 2)
      ltac:(lia)).
  sep_apply_l_atomic
    (Int64Array.seg_shape_to_full_shape suf_pre 0 (n_pre + 2)).
  sep_apply_l_atomic
    (CharArray.full_to_full_shape okpre_pre (n_pre + 1) okpre_values).
  sep_apply_l_atomic
    (CharArray.seg_to_seg_shape oksuf_pre 1 (n_pre + 2) oksuf_values).
  sep_apply_l_atomic
    (CharArray.seg_shape_merge_to_seg_shape oksuf_pre 0 1 (n_pre + 2)
      ltac:(lia)).
  sep_apply_l_atomic
    (CharArray.seg_shape_to_full_shape oksuf_pre 0 (n_pre + 2)).
  replace (suf_pre + 0 * sizeof(INT64)) with suf_pre by lia.
  replace (n_pre + 2 - 0) with (n_pre + 2) by lia.
  replace (oksuf_pre + 0 * sizeof(CHAR)) with oksuf_pre by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hokpre : Znth (i - 1) okpre_values 0 = 1).
  { pose proof (prefix_residual_flag_boolean
      values pre_values okpre_values (i - 1) PreH17 ltac:(lia)) as Hflag.
    destruct Hflag; [lia|assumption]. }
  assert (Hoksuf : Znth (i + 1) oksuf_values 0 = 1).
  { pose proof (suffix_residual_flag_boolean
      values 1 suf_values oksuf_values (i + 1) PreH18 ltac:(lia)) as Hflag.
    destruct Hflag as [Hzero|Hone]; [|exact Hone].
    exfalso. apply PreH4.
    replace (i + 2 - 1) with (i + 1) by lia.
    exact Hzero. }
  assert (Hswap :
    SwapResidualSuccess values pre_values suf_values okpre_values oksuf_values i).
  { unfold SwapResidualSuccess. cbn.
    repeat split; try assumption.
    - rewrite Znth_cons in PreH3 by lia.
      replace (i + 1 - 1) with i in PreH3 by lia.
      lia.
    - rewrite Znth_cons in PreH2 by lia.
      replace (i - 1) with (i - 1) in PreH2 by lia.
      rewrite Znth_cons in PreH2 by lia.
      replace (i + 1 - 1) with i in PreH2 by lia.
      lia.
    - rewrite Znth_cons in PreH1 by lia.
      replace (i - 1) with (i - 1) in PreH1 by lia.
      rewrite Znth_cons in PreH1 by lia.
      replace (i + 1 - 1) with i in PreH1 by lia.
      replace (i + 2 - 1) with (i + 1) in PreH1 by lia.
      exact PreH1. }
  assert (Hclean : Cleanable values).
  { apply (proj2
      (cleanable_residual_characterization__final_result
        values pre_values suf_values okpre_values oksuf_values
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH17 PreH18)).
    right. exists i. split; [lia|exact Hswap]. }
  unfold Spec. left. split; [reflexivity|exact Hclean].
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_spatial : solver_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (Int64Array.full_to_full_shape pre_pre (n_pre + 1) pre_values).
  sep_apply_l_atomic
    (Int64Array.seg_to_seg_shape suf_pre 1 (n_pre + 2) suf_values).
  sep_apply_l_atomic
    (Int64Array.seg_shape_merge_to_seg_shape suf_pre 0 1 (n_pre + 2)
      ltac:(lia)).
  sep_apply_l_atomic
    (Int64Array.seg_shape_to_full_shape suf_pre 0 (n_pre + 2)).
  sep_apply_l_atomic
    (CharArray.full_to_full_shape okpre_pre (n_pre + 1) okpre_values).
  sep_apply_l_atomic
    (CharArray.seg_to_seg_shape oksuf_pre 1 (n_pre + 2) oksuf_values).
  sep_apply_l_atomic
    (CharArray.seg_shape_merge_to_seg_shape oksuf_pre 0 1 (n_pre + 2)
      ltac:(lia)).
  sep_apply_l_atomic
    (CharArray.seg_shape_to_full_shape oksuf_pre 0 (n_pre + 2)).
  replace (suf_pre + 0 * sizeof(INT64)) with suf_pre by lia.
  replace (n_pre + 2 - 0) with (n_pre + 2) by lia.
  replace (oksuf_pre + 0 * sizeof(CHAR)) with oksuf_pre by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i = 0) by lia.
  subst i.
  assert (Hokpre : Znth n_pre okpre_values 0 = 1).
  { pose proof (prefix_residual_flag_boolean
      values pre_values okpre_values n_pre PreH14 ltac:(lia)) as Hflag.
    destruct Hflag; [lia|assumption]. }
  assert (Hdirect : DirectResidualSuccess pre_values okpre_values (Zlength values)).
  { unfold DirectResidualSuccess. rewrite <- PreH6. split; assumption. }
  assert (Hclean : Cleanable values).
  { apply (proj2
      (cleanable_residual_characterization__final_result
        values pre_values suf_values okpre_values oksuf_values
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15)).
    left. exact Hdirect. }
  unfold Spec. left. split; [reflexivity|exact Hclean].
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_spatial : solver_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 0) by lia.
  subst i.
  sep_apply_l_atomic
    (Int64Array.full_to_full_shape pre_pre (n_pre + 1) pre_values).
  sep_apply_l_atomic
    (Int64Array.seg_to_seg_shape suf_pre (0 + 1) (n_pre + 2) suf_values).
  sep_apply_l_atomic
    (Int64Array.seg_shape_merge_to_seg_shape suf_pre 0 (0 + 1) (n_pre + 2)
      ltac:(lia)).
  sep_apply_l_atomic
    (Int64Array.seg_shape_to_full_shape suf_pre 0 (n_pre + 2)).
  sep_apply_l_atomic
    (CharArray.full_to_full_shape okpre_pre (n_pre + 1) okpre_values).
  sep_apply_l_atomic
    (CharArray.seg_to_seg_shape oksuf_pre (0 + 1) (n_pre + 2) oksuf_values).
  sep_apply_l_atomic
    (CharArray.seg_shape_merge_to_seg_shape oksuf_pre 0 (0 + 1) (n_pre + 2)
      ltac:(lia)).
  sep_apply_l_atomic
    (CharArray.seg_shape_to_full_shape oksuf_pre 0 (n_pre + 2)).
  replace (suf_pre + 0 * sizeof(INT64)) with suf_pre by lia.
  replace (n_pre + 2 - 0) with (n_pre + 2) by lia.
  replace (oksuf_pre + 0 * sizeof(CHAR)) with oksuf_pre by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.
