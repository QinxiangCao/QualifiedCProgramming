From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P031_1311C_perform_the_combo_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P031_1311C_perform_the_combo_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P031_1311C_perform_the_combo_lib.
Local Open Scope sac.

Lemma proof_of_memset_entail_wit_1_split_goal_1 : memset_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold repeat_Z; reflexivity).
Qed.

Lemma proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_memset_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_memset_entail_wit_2_split_goal_1 : memset_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply repeat_Z_tail.
  lia.
Qed.

Lemma proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_memset_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_memset_return_wit_1_split_goal_spatial : memset_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  cancel (UCharArray.full dst_pre n_pre (repeat_Z 0 n_pre)).
Qed.

Lemma proof_of_memset_return_wit_1 : memset_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_memset_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH7 i ltac:(lia)) as Htry.
  specialize (PreH13 (Znth i tries 0) ltac:(lia)) as Hbounds.
  unfold DifferencePrefix in PreH12.
  destruct PreH12 as [Hlen [Hzero Hpoint]].
  rewrite Znth_replace_Znth_Diff by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  specialize (PreH7 i ltac:(lia)) as Htry.
  specialize (PreH13 (Znth i tries 0) ltac:(lia)) as Hbounds.
  unfold DifferencePrefix in PreH12.
  destruct PreH12 as [Hlen [Hzero Hpoint]].
  rewrite Znth_replace_Znth_Diff by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (Int64Array.undef_full_split_to_undef_missing_i (&( "diff" )) 0 (n_pre + 1)).
  - dump_pre_spatial. lia.
  - prop_apply (valid_undef_store_int64 (&( "diff" ) + 0 * sizeof(INT64))).
    Intros_p Hvalid.
    dump_pre_spatial.
    unfold valid_object in Hvalid.
    tauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma int64_undef_to_uchar8 : forall p,
  p # Int64 |->_ |-- UCharArray.undef_full p 8.
Proof.
  intros p.
  unfold UCharArray.undef_full, store_undef_array.
  simpl.
  unfold StoreUCharAsElement.undefstoreA.
  rewrite (undef_store_int_expand 8 4 p).
  rewrite ?(undef_store_int_expand 1 1).
  Intros_p Hvalid.
  cbn [undef_store_bytes].
  normalize.
  split_pure_spatial.
  - simpl.
    replace (p + 0) with p by lia.
    replace (p + 0 + 1) with (p + 1) by lia.
    replace (p + 0 + 2) with (p + 2) by lia.
    replace (p + 0 + 3) with (p + 3) by lia.
    replace (p + 0 + 4) with (p + 4) by lia.
    replace (p + 0 + 5) with (p + 5) by lia.
    replace (p + 0 + 6) with (p + 6) by lia.
    replace (p + 0 + 7) with (p + 7) by lia.
    replace (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) with (p + 7) by lia.
    replace (p + 1 + 1 + 1 + 1 + 1 + 1) with (p + 6) by lia.
    replace (p + 1 + 1 + 1 + 1 + 1) with (p + 5) by lia.
    replace (p + 1 + 1 + 1 + 1) with (p + 4) by lia.
    replace (p + 1 + 1 + 1) with (p + 3) by lia.
    replace (p + 1 + 1) with (p + 2) by lia.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: unfold aligned, Arch.aligned in *.
    all: rewrite ?Z.mod_1_r.
    all: lia.
Qed.

Lemma int64_undef_full_to_uchar8 : forall p,
  Int64Array.undef_full p 1 |-- UCharArray.undef_full p 8.
Proof.
  intros p.
  rewrite (Int64Array.undef_full_unfold p 0 (@nil Z)) by lia.
  replace (p + 0 * sizeof(INT64)) with p by lia.
  sep_apply (int64_undef_to_uchar8 p).
  replace (0 + 1) with 1 by lia.
  rewrite Int64Array.undef_seg_empty.
  rewrite sepcon_emp_equiv.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof int64_undef_full_to_uchar8 as Hone.
  assert (Hall : forall p k, 0 <= k ->
    Int64Array.undef_full p k |-- UCharArray.undef_full p (8 * k)).
  {
    intros p k Hk.
    remember (Z.to_nat k) as q eqn:Hq.
    replace k with (Z.of_nat q) by lia.
    clear Hk Hq k.
    revert p.
    induction q as [|q IHq]; intros p.
    - rewrite Int64Array.undef_full_empty.
      replace (8 * 0) with 0 by lia.
      rewrite UCharArray.undef_full_empty.
      cancel emp.
    - replace (Z.of_nat (S q)) with (Z.of_nat q + 1) by lia.
      sep_apply_l_atomic
        (Int64Array.undef_full_split_to_undef_full p (Z.of_nat q)
          (Z.of_nat q + 1)).
      + dump_pre_spatial.
        lia.
      + sep_apply (IHq p).
        replace (Z.of_nat q + 1 - Z.of_nat q) with 1 by lia.
        sep_apply (Hone (p + Z.of_nat q * sizeof(INT64))).
        sep_apply_r_atomic
          (UCharArray.undef_full_merge_to_undef_full p (8 * Z.of_nat q)
            (8 * (Z.of_nat q + 1))).
        * dump_pre_spatial. lia.
        * rewrite sizeof_int64, sizeof_uchar.
          replace (8 * (Z.of_nat q + 1) - 8 * Z.of_nat q) with 8 by lia.
          replace (p + Z.of_nat q * 8) with (p + 8 * Z.of_nat q) by lia.
          cancel (UCharArray.undef_full p (8 * Z.of_nat q)).
          replace (p + 8 * Z.of_nat q * 1) with (p + 8 * Z.of_nat q) by lia.
          cancel (UCharArray.undef_full (p + 8 * Z.of_nat q) 8).
  }
  sep_apply_l_atomic (Hall (&( "diff" )) (n_pre + 1) ltac:(lia)).
  rewrite sizeof_int64.
  replace (&( "diff" ) + 0 * 8) with (&( "diff" )) by lia.
  cancel (UCharArray.undef_full (&( "diff" )) (8 * (n_pre + 1))).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hone : forall p,
    aligned_4 p ->
    UCharArray.full p 8 (repeat_Z 0 8) |--
    Int64Array.full p 1 (repeat_Z 0 1)).
  {
    intros p Halign.
    unfold UCharArray.full, Int64Array.full, store_array, repeat_Z.
    simpl.
    unfold StoreUCharAsElement.storeA, StoreInt64AsElement.storeA.
    rewrite store_int64_store_uchar.
    Exists 0 0 0 0 0 0 0 0.
    LLM_pre_process ltac:(lia || int_auto).
    split_pure_spatial.
    - replace (p + 0) with p by lia.
      replace (p + 0 + 1) with (p + 1) by lia.
      replace (p + 0 + 2) with (p + 2) by lia.
      replace (p + 0 + 3) with (p + 3) by lia.
      replace (p + 0 + 4) with (p + 4) by lia.
      replace (p + 0 + 5) with (p + 5) by lia.
      replace (p + 0 + 6) with (p + 6) by lia.
      replace (p + 0 + 7) with (p + 7) by lia.
      repeat cancel.
    - split_pures.
      all: dump_pre_spatial.
      all: try reflexivity.
      all: try (vm_compute; split; intros Hbad; discriminate Hbad).
      all: try (vm_compute; split; reflexivity).
      replace (p + 0) with p by lia.
      exact Halign.
  }
  assert (Hall : forall p k, 0 <= k -> aligned_4 p ->
    UCharArray.full p (8 * k) (repeat_Z 0 (8 * k)) |--
    Int64Array.full p k (repeat_Z 0 k)).
  {
    intros p k Hk.
    remember (Z.to_nat k) as q eqn:Hq.
    replace k with (Z.of_nat q) by lia.
    clear Hk Hq k.
    revert p.
    induction q as [|q IHq]; intros p Halign.
    - unfold repeat_Z; simpl.
      rewrite UCharArray.full_empty, Int64Array.full_empty.
      LLM_pre_process ltac:(lia || int_auto).
    - replace (Z.of_nat (S q)) with (Z.of_nat q + 1) by lia.
      sep_apply_l_atomic
        (UCharArray.full_split_to_full p (8 * Z.of_nat q)
          (8 * (Z.of_nat q + 1))
          (repeat_Z 0 (8 * (Z.of_nat q + 1)))).
      + dump_pre_spatial. lia.
      + assert (Hrep : repeat_Z 0 (8 * (Z.of_nat q + 1)) =
            repeat_Z 0 (8 * Z.of_nat q) ++ repeat_Z 0 8).
        { unfold repeat_Z.
          replace (Z.to_nat (8 * (Z.of_nat q + 1))) with
            ((Z.to_nat (8 * Z.of_nat q) + Z.to_nat 8)%nat) by lia.
          rewrite repeat_app. reflexivity. }
        assert (Hprefix : sublist 0 (8 * Z.of_nat q)
            (repeat_Z 0 (8 * (Z.of_nat q + 1))) =
            repeat_Z 0 (8 * Z.of_nat q)).
        { rewrite Hrep.
          assert (Hlen : Zlength (repeat_Z 0 (8 * Z.of_nat q)) =
              8 * Z.of_nat q).
          { unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia. }
          rewrite <- Hlen at 1.
          apply sublist_app_exact1. }
        assert (Hsuffix : sublist (8 * Z.of_nat q) (8 * (Z.of_nat q + 1))
            (repeat_Z 0 (8 * (Z.of_nat q + 1))) = repeat_Z 0 8).
        { rewrite Hrep.
          rewrite (sublist_split_app_r (8 * Z.of_nat q)
            (8 * (Z.of_nat q + 1)) (8 * Z.of_nat q)
            (repeat_Z 0 (8 * Z.of_nat q)) (repeat_Z 0 8)).
          - replace (8 * (Z.of_nat q + 1) - 8 * Z.of_nat q) with 8 by lia.
            replace (8 * Z.of_nat q - 8 * Z.of_nat q) with 0 by lia.
            apply sublist_self.
            unfold repeat_Z. rewrite Zlength_correct, repeat_length. reflexivity.
          - unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
          - lia. }
        rewrite Hprefix, Hsuffix.
        replace (8 * (Z.of_nat q + 1) - 8 * Z.of_nat q) with 8 by lia.
        rewrite sizeof_uchar.
        replace (p + 8 * Z.of_nat q * 1) with (p + 8 * Z.of_nat q) by lia.
        sep_apply (IHq p Halign).
        sep_apply (Hone (p + 8 * Z.of_nat q)
          ltac:(unfold aligned_4 in *;
            replace (p + 8 * Z.of_nat q) with
              (p + (2 * Z.of_nat q) * 4) by ring;
            rewrite Z.add_mod by lia;
            rewrite Z.mul_mod by lia;
            rewrite Halign;
            rewrite Z.mod_same by lia;
            rewrite Z.mul_0_r;
            repeat rewrite Z.mod_0_l by lia;
            reflexivity)).
        rewrite repeat_Z_tail by lia.
        replace (repeat_Z 0 1) with (0 :: nil) by reflexivity.
        sep_apply_r_atomic
          (Int64Array.full_merge_to_full p (Z.of_nat q) (Z.of_nat q + 1)
            (repeat_Z 0 (Z.of_nat q)) (repeat_Z 0 1)).
        * dump_pre_spatial. lia.
        * rewrite sizeof_int64.
          replace (Z.of_nat q + 1 - Z.of_nat q) with 1 by lia.
          cancel (Int64Array.full p (Z.of_nat q) (repeat_Z 0 (Z.of_nat q))).
          replace (p + Z.of_nat q * 8) with (p + 8 * Z.of_nat q) by lia.
          replace (repeat_Z 0 1) with (0 :: nil) by reflexivity.
          cancel (Int64Array.full (p + 8 * Z.of_nat q) 1 (0 :: nil)).
  }
  rewrite sizeof_int64.
  replace (&( "diff" ) + 0 * 8) with (&( "diff" )) by lia.
  sep_apply_l_atomic
    (Hall (&( "diff" )) (n_pre + 1) ltac:(lia)
      ltac:(replace (&( "diff" )) with
        (&( "diff" ) + 0 * sizeof(INT64)) by ring; exact PreH11)).
  cancel (Int64Array.full (&( "diff" )) (n_pre + 1)
    (repeat_Z 0 (n_pre + 1))).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Znth_repeat.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DifferencePrefix.
  split.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    lia.
  - split.
    + unfold repeat_Z.
      rewrite Znth_repeat.
      reflexivity.
    + intros k Hk.
      unfold repeat_Z.
      rewrite Znth_repeat.
      unfold Count.
      rewrite Zsublist_nil by lia.
      unfold SpecHelpers.set_card, SumLib.Sum.sum.
      cbn [SumLib.ZRange.finite_Z_range' SumLib.ZRange.finite_Z_range].
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6. exact H.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5. exact H.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply difference_prefix_step__difference_updates.
  - lia.
  - intros j Hj. apply PreH7. lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (Int64Array.undef_full_split_to_undef_full cnt_pre 1 26).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic
      (Int64Array.undef_full_unfold cnt_pre 0 (@nil Z)).
    + dump_pre_spatial. lia.
    + replace (cnt_pre + 0 * sizeof(INT64)) with cnt_pre by lia.
      prop_apply_p (valid_undef_store_int64 cnt_pre).
      Intros_p Hvalid.
      dump_pre_spatial.
      unfold valid_object in Hvalid.
      tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hi : i = m_pre) by lia.
  subst i.
  unfold DifferencePrefix in PreH12.
  destruct PreH12 as [Hlen [Hzero Hpoint]].
  intros k Hk.
  destruct (Z.eq_dec k 0) as [Heq | Hneq].
  - subst k.
    rewrite Znth_replace_Znth_Same by lia.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (PreH13 k ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply (difference_ready_at_exit__difference_updates
    tries n_pre i diff_l_2).
  - lia.
  - lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcell : forall p,
    p # Int64 |->_ |-- UCharArray.undef_full p 8).
  {
    intros p.
    apply int64_undef_to_uchar8.
  }
  assert (Harray : forall p (k : nat),
    Int64Array.undef_full p (Z.of_nat k) |--
    UCharArray.undef_full p (8 * Z.of_nat k)).
  {
    intros p k.
    revert p.
    induction k as [|k IH]; intros p.
    - simpl.
      rewrite Int64Array.undef_full_empty.
      rewrite UCharArray.undef_full_empty.
      cancel.
    - rewrite Nat2Z.inj_succ.
      rewrite (Int64Array.undef_full_unfold
        p (Z.of_nat k) (@nil Z)) by lia.
      sep_apply_l_atomic
        (Int64Array.undef_seg_to_undef_full
          p 1 (Z.succ (Z.of_nat k))).
      replace (p + 0 * sizeof(INT64)) with p by lia.
      sep_apply_l_atomic (Hcell p).
      try rewrite sizeof_int64 in *.
      try rewrite sizeof_uchar in *.
      replace (p + 1 * 8) with (p + 8) by lia.
      replace (Z.succ (Z.of_nat k) - 1) with (Z.of_nat k) by lia.
      sep_apply_l_atomic (IH (p + 8)).
      replace (8 * Z.succ (Z.of_nat k))
        with (8 + 8 * Z.of_nat k) by lia.
      sep_apply_r_atomic
        (UCharArray.undef_full_merge_to_undef_full
          p 8 (8 + 8 * Z.of_nat k)).
      + dump_pre_spatial. pose proof (Nat2Z.is_nonneg k). lia.
      + replace (p + 8 * 1) with (p + 8) by lia.
        replace (8 + 8 * Z.of_nat k - 8)
          with (8 * Z.of_nat k) by lia.
        cancel.
      rewrite sizeof_uchar.
      replace (p + 8 * 1) with (p + 8) by lia.
      cancel.
  }
  sep_apply_l_atomic (Harray cnt_pre 26%nat).
  rewrite sizeof_int64.
  replace (Z.of_nat 26) with 26 by reflexivity.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_spatial : solver_entail_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hblock : forall p,
    aligned_4 p ->
    UCharArray.full p 8 (repeat 0 8%nat) |--
    Int64Array.full p 1 (repeat 0 1%nat)).
  {
    intros p Halign.
    unfold UCharArray.full, Int64Array.full, store_array.
    unfold StoreUCharAsElement.storeA, StoreInt64AsElement.storeA.
    rewrite sizeof_int64, sizeof_uchar.
    cbn.
    replace (p + 0) with p by lia.
    rewrite store_int64_store_uchar.
    Exists 0 0 0 0 0 0 0 0.
    split_pure_spatial.
    - Intros_p H8. Intros_p Hnil.
      cancel (store_uchar p 0).
      cancel (store_uchar (p + 1) 0).
      cancel (store_uchar (p + 2) 0).
      cancel (store_uchar (p + 3) 0).
      cancel (store_uchar (p + 4) 0).
      cancel (store_uchar (p + 5) 0).
      cancel (store_uchar (p + 6) 0).
      cancel (store_uchar (p + 7) 0).
    - split_pures.
      all: dump_pre_spatial.
      all: try (unfold merge_int64; reflexivity).
      all: try int_auto.
      all: auto.
  }
  assert (Harray : forall (n : nat) p,
    aligned_4 p ->
    UCharArray.full p (8 * Z.of_nat n) (repeat 0 (8 * n)%nat) |--
    Int64Array.full p (Z.of_nat n) (repeat 0 n)).
  {
    induction n as [|n IH]; intros p Halign.
    - unfold UCharArray.full, Int64Array.full, store_array.
      cbn.
      Intros_p Hzero. Intros_p Hnil.
      split_pure_spatial.
      + cancel emp.
      + split_pures; dump_pre_spatial; auto.
    - replace (repeat 0 (8 * S n)%nat)
        with (repeat 0 8%nat ++ repeat 0 (8 * n)%nat).
      2:{ rewrite <- repeat_app. f_equal. lia. }
      replace (repeat 0 (S n)) with (0 :: repeat 0 n) by reflexivity.
      sep_apply_l_atomic
        (UCharArray.full_to_seg p (8 * Z.of_nat (S n))
          (repeat 0 8%nat ++ repeat 0 (8 * n)%nat)).
      sep_apply_l_atomic
        (UCharArray.seg_split_to_seg p 0 8 (8 * Z.of_nat (S n))
          (repeat 0 8%nat ++ repeat 0 (8 * n)%nat) ltac:(lia)).
      replace (8 - 0) with (Zlength (repeat 0 8%nat)) by
        (rewrite Zlength_correct, repeat_length; lia).
      rewrite sublist_app_exact1.
      rewrite (sublist_split_app_r (Zlength (repeat 0 8%nat))
        (8 * Z.of_nat (S n) - 0) 8
        (repeat 0 8%nat) (repeat 0 (8 * n)%nat)) by
          (rewrite Zlength_correct, repeat_length; lia).
      replace (8 * Z.of_nat (S n) - 8) with (8 * Z.of_nat n) by lia.
      rewrite sublist_self by
        (rewrite Zlength_correct, repeat_length; lia).
      sep_apply_l_atomic
        (UCharArray.seg_to_full p 0 8 (repeat 0 8%nat)).
      sep_apply_l_atomic
        (UCharArray.seg_to_full p 8 (8 * Z.of_nat (S n))
          (repeat 0 (8 * n)%nat)).
      replace (p + 0 * sizeof(UCHAR)) with p by
        (rewrite sizeof_uchar; lia).
      replace (p + 8 * sizeof(UCHAR)) with (p + 8) by
        (rewrite sizeof_uchar; lia).
      sep_apply_l_atomic (Hblock p Halign).
      assert (Halign8 : aligned_4 (p + 8)).
      {
        unfold aligned_4 in *.
        rewrite Z.add_mod by lia.
        rewrite Halign.
        reflexivity.
      }
      replace (8 * Z.of_nat (S n) - 8) with (8 * Z.of_nat n) by lia.
      sep_apply_l_atomic (IH (p + 8) Halign8).
      pose proof
        (Int64Array.full_merge_to_full p 1 (Z.of_nat (S n))
          (repeat 0 1%nat) (repeat 0 n) ltac:(lia)) as Hmerge.
      replace (p + 1 * sizeof(INT64)) with (p + 8) in Hmerge by
        (rewrite sizeof_int64; lia).
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in Hmerge by lia.
      sep_apply Hmerge.
      cbn.
      reflexivity.
  }
  change
    (UCharArray.full cnt_pre (8 * Z.of_nat 26%nat)
      (repeat 0 (8 * 26)%nat) |--
     Int64Array.full cnt_pre (Z.of_nat 26%nat) (repeat 0 26%nat)).
  apply Harray. exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Znth_repeat.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PartialSpec.
  split.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    reflexivity.
  - intros c Hc.
    unfold repeat_Z.
    rewrite Znth_repeat.
    rewrite Zsublist_nil by lia.
    simpl.
    assert (Hall : Forall (fun p => 1 <= p) tries).
    {
      apply Forall_forall.
      intros p Hin.
      destruct (@In_nth Z tries p 0 Hin) as [i [Hi Hip]].
      specialize (PreH6 (Z.of_nat i)).
      unfold Znth in PreH6.
      rewrite Nat2Z.id in PreH6.
      rewrite Hip in PreH6.
      assert (Hzi : 0 <= Z.of_nat i < m_pre).
      { rewrite PreH8, Zlength_correct. lia. }
      specialize (PreH6 Hzi).
      lia.
    }
    clear PreH6 PreH8 PreH9.
    induction Hall as [|p tries Hp Hall IH].
    + simpl. lia.
    + simpl.
      rewrite Z.min_r by lia.
      rewrite Zsublist_nil by lia.
      rewrite Count_nil__count_initialization.
      rewrite <- IH.
      reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH10 k_3 H).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH6 k_2 H).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_6 : solver_entail_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (coverage_prefix_step__coverage_and_output_step
    tries n_pre diff_l j cover PreH12 ltac:(lia)
    ltac:(intros i Hi; apply PreH7; lia) PreH14) as Hstep.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (coverage_prefix_step__coverage_and_output_step
    tries n_pre diff_l j cover PreH12 ltac:(lia)
    ltac:(intros i Hi; apply PreH7; lia) PreH14) as Hstep.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (coverage_prefix_step__coverage_and_output_step
    tries n_pre diff_l j cover PreH12 ltac:(lia)
    ltac:(intros i Hi; apply PreH7; lia) PreH14) as Hstep.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_6 : solver_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_7 : solver_entail_wit_8_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hchar := PreH5 j ltac:(lia)).
  destruct PreH16 as [Houtlen Hpartial].
  destruct (Z.eq_dec k_4 (Znth j text 0 - 97)) as [Heq | Hneq].
  - subst k_4.
    rewrite Znth_replace_Znth_Same by lia.
    specialize (PreH17 (Znth j text 0 - 97) ltac:(lia)).
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (PreH17 k_4 ltac:(lia)).
    nia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (partial_spec_step__coverage_and_output_step
    text tries diff_l_2 n_pre j cover out_2 PreH11 ltac:(lia) PreH7
    ltac:(intros i Hi; apply PreH6; lia)
    ltac:(apply PreH5; lia) PreH13 PreH16).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_5 : solver_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_5.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DifferenceReady in *.
  tauto.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_2 : solver_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply partial_spec_complete__final_result with (done := j).
  - lia.
  - intros k Hk.
    specialize (PreH7 k ltac:(lia)).
    lia.
  - exact PreH17.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_2.
Qed.
