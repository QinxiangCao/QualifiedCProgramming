From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P068_1416C_xor_inverse_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P068_1416C_xor_inverse_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P068_1416C_xor_inverse_lib.
Local Open Scope sac.

Lemma proof_of_solve_safety_wit_9_split_goal_1 : solve_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CostBound in PreH20.
  destruct PreH20 as [_ [Hcostlen Hcells]].
  specialize (Hcells bit_pre 1 ltac:(lia) ltac:(lia)).
  unfold CostAt in Hcells.
  pose proof (Znth_indep current_costs bit_pre
    __default__List_Z (@nil Z) ltac:(lia)) as Hrow.
  rewrite Hrow.
  assert (Hzeros : zeros <= i - l_pre) by lia.
  assert (Hstep : i - l_pre + 1 <= r_pre - l_pre) by lia.
  assert (Hseg : 0 <= r_pre - l_pre) by lia.
  assert (Hsq :
    (i - l_pre) * (i - l_pre) + zeros <=
    (r_pre - l_pre) * (r_pre - l_pre)).
  {
    assert (Hleft :
      (i - l_pre) * (i - l_pre) + zeros <=
      (i - l_pre) * (i - l_pre + 1)).
    {
      replace ((i - l_pre) * (i - l_pre + 1))
        with ((i - l_pre) * (i - l_pre) + (i - l_pre)) by ring.
      lia.
    }
    assert (Hmiddle :
      (i - l_pre) * (i - l_pre + 1) <=
      (r_pre - l_pre) * (i - l_pre + 1)).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hright :
      (r_pre - l_pre) * (i - l_pre + 1) <=
      (r_pre - l_pre) * (r_pre - l_pre)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    lia.
  }
  assert (Hfactor :
    (r_pre - l_pre) * (r_pre - l_pre) <=
    (bit_pre + 1) * (r_pre - l_pre) * (r_pre - l_pre)).
  {
    assert (Hsquare_nonneg :
      0 <= (r_pre - l_pre) * (r_pre - l_pre)).
    { apply Z.square_nonneg. }
    pose proof (Z.mul_le_mono_nonneg_r 1 (bit_pre + 1)
      ((r_pre - l_pre) * (r_pre - l_pre)) Hsquare_nonneg ltac:(lia))
      as Hmul.
    replace (1 * ((r_pre - l_pre) * (r_pre - l_pre)))
      with ((r_pre - l_pre) * (r_pre - l_pre)) in Hmul by ring.
    replace ((bit_pre + 1) * (r_pre - l_pre) * (r_pre - l_pre))
      with ((bit_pre + 1) * ((r_pre - l_pre) * (r_pre - l_pre))) by ring.
    exact Hmul.
  }
  assert (Hfinal :
    Znth 1 (Znth bit_pre current_costs (@nil Z)) 0 + zeros <= INT64_MAX)
    by lia.
  dump_pre_spatial.
  exact Hfinal.
Qed.

Lemma proof_of_solve_safety_wit_9_split_goal_2 : solve_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CostBound in PreH20.
  destruct PreH20 as [_ [Hcostlen Hcells]].
  specialize (Hcells bit_pre 1 ltac:(lia) ltac:(lia)).
  unfold CostAt in Hcells.
  pose proof (Znth_indep current_costs bit_pre
    __default__List_Z (@nil Z) ltac:(lia)) as Hrow.
  rewrite Hrow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_13_split_goal_1 : solve_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CostBound in PreH20.
  destruct PreH20 as [_ [Hcostlen Hcells]].
  specialize (Hcells bit_pre 0 ltac:(lia) ltac:(lia)).
  unfold CostAt in Hcells.
  pose proof (Znth_indep current_costs bit_pre
    __default__List_Z (@nil Z) ltac:(lia)) as Hrow.
  rewrite Hrow.
  assert (Hones : ones <= i - l_pre) by lia.
  assert (Hstep : i - l_pre + 1 <= r_pre - l_pre) by lia.
  assert (Hseg : 0 <= r_pre - l_pre) by lia.
  assert (Hsq :
    (i - l_pre) * (i - l_pre) + ones <=
    (r_pre - l_pre) * (r_pre - l_pre)).
  {
    assert (Hleft :
      (i - l_pre) * (i - l_pre) + ones <=
      (i - l_pre) * (i - l_pre + 1)).
    {
      replace ((i - l_pre) * (i - l_pre + 1))
        with ((i - l_pre) * (i - l_pre) + (i - l_pre)) by ring.
      lia.
    }
    assert (Hmiddle :
      (i - l_pre) * (i - l_pre + 1) <=
      (r_pre - l_pre) * (i - l_pre + 1)).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hright :
      (r_pre - l_pre) * (i - l_pre + 1) <=
      (r_pre - l_pre) * (r_pre - l_pre)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    lia.
  }
  assert (Hfactor :
    (r_pre - l_pre) * (r_pre - l_pre) <=
    (bit_pre + 1) * (r_pre - l_pre) * (r_pre - l_pre)).
  {
    assert (Hsquare_nonneg :
      0 <= (r_pre - l_pre) * (r_pre - l_pre)).
    { apply Z.square_nonneg. }
    pose proof (Z.mul_le_mono_nonneg_r 1 (bit_pre + 1)
      ((r_pre - l_pre) * (r_pre - l_pre)) Hsquare_nonneg ltac:(lia))
      as Hmul.
    replace (1 * ((r_pre - l_pre) * (r_pre - l_pre)))
      with ((r_pre - l_pre) * (r_pre - l_pre)) in Hmul by ring.
    replace ((bit_pre + 1) * (r_pre - l_pre) * (r_pre - l_pre))
      with ((bit_pre + 1) * ((r_pre - l_pre) * (r_pre - l_pre))) by ring.
    exact Hmul.
  }
  assert (Hfinal :
    Znth 0 (Znth bit_pre current_costs (@nil Z)) 0 + ones <= INT64_MAX)
    by lia.
  dump_pre_spatial.
  exact Hfinal.
Qed.

Lemma proof_of_solve_safety_wit_13_split_goal_2 : solve_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CostBound in PreH20.
  destruct PreH20 as [_ [Hcostlen Hcells]].
  specialize (Hcells bit_pre 0 ltac:(lia) ltac:(lia)).
  unfold CostAt in Hcells.
  pose proof (Znth_indep current_costs bit_pre
    __default__List_Z (@nil Z) ltac:(lia)) as Hrow.
  rewrite Hrow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists cost_before.
  split_pure_spatial.
  - cancel (IntArray.full a_p n_total before).
    cancel (IntArray.mixed_full tmp_p n_total scratch).
    unfold Int64Array2.full, store_array.
    sep_apply_l_atomic
      (store_array_rec_split_to_rec__solve_counting
         (list Z) (Int64Array2.row_store 2) ( &( "cost" ) )
         0 bit_pre 30 cost_before ltac:(lia)).
    replace (bit_pre - 0) with bit_pre by lia.
    replace (30 - 0) with 30 by lia.
    sep_apply_l_atomic
      (store_array_rec_split_to_rec__solve_counting
         (list Z) (Int64Array2.row_store 2) ( &( "cost" ) )
         bit_pre (bit_pre + 1) 30
         (sublist bit_pre 30 cost_before) ltac:(lia)).
    replace (bit_pre + 1 - bit_pre) with 1 by lia.
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + bit_pre) with bit_pre by lia.
    replace (1 + bit_pre) with (bit_pre + 1) by lia.
    replace (30 - bit_pre + bit_pre) with 30 by lia.
    rewrite (sublist_single __default__List_Z bit_pre cost_before) by lia.
    pose proof (PreH15 bit_pre ltac:(lia)) as Hrow_shape.
    destruct Hrow_shape as [[Hrow_len Hrow_nonneg0] Hrow_nonneg1].
    remember (Znth bit_pre cost_before __default__List_Z) as row
      eqn:Hrow.
    rewrite Zlength_correct in Hrow_len.
    change (Z.of_nat (length row) = Z.of_nat 2%nat) in Hrow_len.
    apply Nat2Z.inj in Hrow_len.
    destruct row as [|v0 row]; simpl in Hrow_len; [discriminate |].
    destruct row as [|v1 row]; simpl in Hrow_len; [discriminate |].
    destruct row as [|v2 row]; [| simpl in Hrow_len; discriminate].
    cbn [store_array_rec].
    unfold Int64Array2.row_store, Int64Array2.row_addr,
      Int64Array2.ElemArray.full, store_array.
    cbn [store_array_rec].
    sep_apply_l_atomic
      (int64array2_rec_shift__solve_counting
         ( &( "cost" ) ) 2 (bit_pre + 1) (bit_pre + 1) 30
         (sublist (bit_pre + 1) 30 cost_before)).
    unfold Int64Array2.row_store, Int64Array2.row_addr,
      Int64Array2.ElemArray.full, store_array.
    rewrite sizeof_int64 in *.
    rewrite Znth0_cons, Znth_cons by lia.
    rewrite Znth0_cons.
    replace (( &( "cost" ) ) + bit_pre * 2 * 8 + 0 * 8) with
      (( &( "cost" ) ) + bit_pre * (8 * 2) + 0 * 8) by ring.
    replace (( &( "cost" ) ) + bit_pre * 2 * 8 + (0 + 1) * 8) with
      (( &( "cost" ) ) + bit_pre * (8 * 2) + 1 * 8) by ring.
    replace (( &( "cost" ) ) + (bit_pre + 1) * (2 * 8)) with
      (( &( "cost" ) ) + (bit_pre + 1) * (8 * 2)) by ring.
    replace (bit_pre + 1 - (bit_pre + 1)) with 0 by lia.
    replace (30 - (bit_pre + 1)) with (30 - bit_pre - 1) by lia.
    LLM_pre_process ltac:(lia || int_auto).
  - split_pures.
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; exact PreH16).
    all: try (dump_pre_spatial;
      apply solve_count_prefix_empty__solve_counting;
      [exact PreH11 |];
      intros b Hb;
      pose proof (PreH15 b Hb) as [[Hrow_len _] _];
      rewrite (Znth_default_irrelevant__solve_counting
                 (list Z) cost_before b __default__List_Z nil) in Hrow_len
        by lia;
      exact Hrow_len).
    all: try (dump_pre_spatial;
      replace (capacity + (l_pre - l_pre) * (l_pre - l_pre)) with capacity
        by ring;
      exact PreH14).
Qed.

Lemma proof_of_solve_entail_wit_2_1_split_goal_1 : solve_entail_wit_2_1_split_goal_1.
Proof. Abort.

Lemma proof_of_solve_entail_wit_2_1_split_goal_2 : solve_entail_wit_2_1_split_goal_2.
Proof. Abort.

Lemma proof_of_solve_entail_wit_2_1_split_goal_3 : solve_entail_wit_2_1_split_goal_3.
Proof. Abort.

Lemma proof_of_solve_entail_wit_2_1 : solve_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose (updated_costs :=
    replace_Znth bit_pre
      (replace_Znth 1 (CostAt current_costs_2 bit_pre 1 + zeros)
        (Znth bit_pre current_costs_2 nil)) current_costs_2).
  Exists updated_costs.
  pose proof PreH19 as Hsolve_shape.
  unfold SolveCountPrefix in Hsolve_shape.
  destruct Hsolve_shape as [_ [_ [_ [Hcurrent_len [Hrows _]]]]].
  pose proof (Hrows bit_pre ltac:(lia)) as [_ Hrow_len].
  assert (Hnew_one : BitAt (Znth i before 0) bit_pre = 1).
  { apply bit_at_one_of_nonzero__solve_counting. exact PreH21. }
  split_pure_spatial.
  - unfold updated_costs.
    rewrite (sublist_replace_Znth_prefix__solve_counting
      nil (replace_Znth 1 (CostAt current_costs_2 bit_pre 1 + zeros)
        (Znth bit_pre current_costs_2 nil)) current_costs_2 bit_pre) by lia.
    rewrite (sublist_replace_Znth_suffix__solve_counting
      nil (replace_Znth 1 (CostAt current_costs_2 bit_pre 1 + zeros)
        (Znth bit_pre current_costs_2 nil)) current_costs_2 bit_pre 30) by lia.
    rewrite !Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    unfold CostAt.
    rewrite (Znth_default_irrelevant__solve_counting
      (list Z) current_costs_2 bit_pre __default__List_Z nil) by lia.
    cancel (IntArray.full a_p n_total before).
    cancel (IntArray.mixed_full tmp_p n_total scratch).
    cancel (Int64Array2.full ( &( "cost" ) ) bit_pre 2
      (sublist 0 bit_pre current_costs_2)).
    cancel ((( &( "a" ) )) # Ptr |-> a_p).
    cancel ((( &( "tmp" ) )) # Ptr |-> tmp_p).
    LLM_pre_process ltac:(lia || int_auto).
  - split_pures.
    all: unfold updated_costs.
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; exact PreH13).
    all: try (dump_pre_spatial;
      eapply solve_count_prefix_step_one__solve_counting;
      [lia | lia | lia | exact PreH19 | exact Hnew_one]).
    all: try (dump_pre_spatial;
      eapply cost_bound_update_cell__solve_counting;
      [lia | lia | exact Hrow_len | lia | | exact PreH20];
      nia).
Qed.

Lemma proof_of_solve_entail_wit_2_2_split_goal_1 : solve_entail_wit_2_2_split_goal_1.
Proof. Abort.

Lemma proof_of_solve_entail_wit_2_2_split_goal_2 : solve_entail_wit_2_2_split_goal_2.
Proof. Abort.

Lemma proof_of_solve_entail_wit_2_2_split_goal_3 : solve_entail_wit_2_2_split_goal_3.
Proof. Abort.

Lemma proof_of_solve_entail_wit_2_2 : solve_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose (updated_costs :=
    replace_Znth bit_pre
      (replace_Znth 0 (CostAt current_costs_2 bit_pre 0 + ones)
        (Znth bit_pre current_costs_2 nil)) current_costs_2).
  Exists updated_costs.
  pose proof PreH19 as Hsolve_shape.
  unfold SolveCountPrefix in Hsolve_shape.
  destruct Hsolve_shape as [_ [_ [_ [Hcurrent_len [Hrows _]]]]].
  pose proof (Hrows bit_pre ltac:(lia)) as [_ Hrow_len].
  assert (Hnew_zero : BitAt (Znth i before 0) bit_pre = 0) by exact PreH21.
  split_pure_spatial.
  - unfold updated_costs.
    rewrite (sublist_replace_Znth_prefix__solve_counting
      nil (replace_Znth 0 (CostAt current_costs_2 bit_pre 0 + ones)
        (Znth bit_pre current_costs_2 nil)) current_costs_2 bit_pre) by lia.
    rewrite (sublist_replace_Znth_suffix__solve_counting
      nil (replace_Znth 0 (CostAt current_costs_2 bit_pre 0 + ones)
        (Znth bit_pre current_costs_2 nil)) current_costs_2 bit_pre 30) by lia.
    rewrite !Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    unfold CostAt.
    rewrite (Znth_default_irrelevant__solve_counting
      (list Z) current_costs_2 bit_pre __default__List_Z nil) by lia.
    cancel (IntArray.full a_p n_total before).
    cancel (IntArray.mixed_full tmp_p n_total scratch).
    cancel (Int64Array2.full ( &( "cost" ) ) bit_pre 2
      (sublist 0 bit_pre current_costs_2)).
    cancel ((( &( "a" ) )) # Ptr |-> a_p).
    cancel ((( &( "tmp" ) )) # Ptr |-> tmp_p).
    LLM_pre_process ltac:(lia || int_auto).
  - split_pures.
    all: unfold updated_costs.
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; exact PreH13).
    all: try (dump_pre_spatial;
      eapply solve_count_prefix_step_zero__solve_counting;
      [lia | lia | lia | exact PreH19 | exact Hnew_zero]).
    all: try (dump_pre_spatial;
      eapply cost_bound_update_cell__solve_counting;
      [lia | lia | exact Hrow_len | lia | | exact PreH20];
      nia).
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = r_pre) by lia. subst i.
  Exists current_costs scratch.
  pose proof PreH19 as Hsolve_shape.
  unfold SolveCountPrefix in Hsolve_shape.
  destruct Hsolve_shape as [_ [_ [_ [Hcurrent_len [Hrows _]]]]].
  pose proof (Hrows bit_pre ltac:(lia)) as [_ Hrow_len].
  split_pure_spatial.
  - cancel (IntArray.full a_p n_total before).
    cancel (IntArray.mixed_full tmp_p n_total scratch).
    cancel ((( &( "a" ) )) # Ptr |-> a_p).
    cancel ((( &( "tmp" ) )) # Ptr |-> tmp_p).
    rewrite (Znth_default_irrelevant__solve_counting
      (list Z) current_costs bit_pre __default__List_Z nil) by lia.
    remember (Znth bit_pre current_costs nil) as row eqn:Hrow.
    rewrite Zlength_correct in Hrow_len.
    change (Z.of_nat (length row) = Z.of_nat 2%nat) in Hrow_len.
    apply Nat2Z.inj in Hrow_len.
    destruct row as [|v0 row]; simpl in Hrow_len; [discriminate |].
    destruct row as [|v1 row]; simpl in Hrow_len; [discriminate |].
    destruct row as [|v2 row]; [| simpl in Hrow_len; discriminate].
    rewrite Znth0_cons, Znth_cons by lia. rewrite Znth0_cons.
    replace (( &( "cost" ) ) + bit_pre * (2 * sizeof (INT64))) with
      (Int64Array2.row_addr ( &( "cost" ) ) 2 bit_pre) by
      (unfold Int64Array2.row_addr; rewrite sizeof_int64; nia).
    sep_apply_l_atomic
      (int64array2_row_cells_merge__solve_counting
        (Int64Array2.row_addr ( &( "cost" ) ) 2 bit_pre)
        (v0 :: v1 :: nil) v0 v1 eq_refl).
    unfold Int64Array2.full, store_array.
    sep_apply_l_atomic
      (int64array2_rec_shift__solve_counting
        (( &( "cost" ) ) + (bit_pre + 1) * (8 * 2))
        2 (-(bit_pre + 1)) 0 (30 - bit_pre - 1)
        (sublist (bit_pre + 1) 30 current_costs)).
    replace (( &( "cost" ) ) + (bit_pre + 1) * (8 * 2) +
      -(bit_pre + 1) * (2 * sizeof (INT64))) with ( &( "cost" ) ) by
      (rewrite sizeof_int64; lia).
    replace (0 - -(bit_pre + 1)) with (bit_pre + 1) by lia.
    replace (30 - bit_pre - 1 - -(bit_pre + 1)) with 30 by lia.
    sep_apply_l_atomic
      (int64array2_pieces_merge__solve_counting
        ( &( "cost" ) ) bit_pre (sublist 0 bit_pre current_costs)
        (v0 :: v1 :: nil) (sublist (bit_pre + 1) 30 current_costs)).
    assert (Hreconstruct :
      sublist 0 bit_pre current_costs ++
        (v0 :: v1 :: nil) :: sublist (bit_pre + 1) 30 current_costs =
      current_costs).
    {
      rewrite Hrow.
      change
        (sublist 0 bit_pre current_costs ++
         (Znth bit_pre current_costs nil :: nil) ++
         sublist (bit_pre + 1) 30 current_costs = current_costs).
      rewrite <- (sublist_single nil bit_pre current_costs) by lia.
      rewrite app_assoc.
      rewrite <- (sublist_split 0 (bit_pre + 1) bit_pre current_costs)
        by lia.
      rewrite <- (sublist_split 0 30 (bit_pre + 1) current_costs) by lia.
      rewrite sublist_self by lia.
      reflexivity.
    }
    rewrite Hreconstruct.
    unfold Int64Array2.full, store_array.
    reflexivity.
  - split_pures.
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; exact PreH13).
    all: try (dump_pre_spatial; exact PreH19).
    all: try (dump_pre_spatial; exact PreH20).
    all: try (dump_pre_spatial;
      unfold StablePartitionPrefix, InitializedSlice;
      left; split; [reflexivity |];
      rewrite !Zsublist_nil by lia;
      reflexivity).
Qed.

Lemma proof_of_solve_entail_wit_4_1_split_goal_1 : solve_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in *.
  destruct PreH19 as [[_ Hinit] | [Hbad _]]; [|lia].
  left. split; [lia|]. unfold InitializedSlice in *.
  rewrite (sublist_replace_Znth_step__stable_partition scratch_current_2 None
    (Some (Znth i before 0)) l_pre p) by lia.
  rewrite Hinit.
  rewrite (sublist_split l_pre (i + 1) i before) by lia.
  rewrite (@sublist_single Z 0 i before) by lia.
  rewrite filter_app. simpl. unfold BitIs, BitAt. rewrite PreH1. simpl.
  rewrite map_app. reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_4_1_split_goal_2 : solve_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. exact PreH15.
Qed.

Lemma proof_of_solve_entail_wit_4_1 : solve_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_4_1_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_4_2_split_goal_1 : solve_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in *.
  destruct PreH19 as [[_ Hinit] | [Hbad _]]; [|lia].
  left. split; [lia|]. unfold InitializedSlice in *.
  rewrite (sublist_split l_pre (i + 1) i before) by lia.
  rewrite (@sublist_single Z 0 i before) by lia.
  rewrite filter_app. simpl. unfold BitIs, BitAt.
  destruct (Z.eqb_spec (Z.land (Z.shiftr (Znth i before 0) bit_pre) 1) 0);
    [contradiction|]. simpl. fold (BitIs bit_pre 0).
  rewrite app_nil_r. exact Hinit.
Qed.

Lemma proof_of_solve_entail_wit_4_2 : solve_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_5_split_goal_1 : solve_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in *.
  destruct PreH18 as [[_ Hinit] | [Hbad _]]; [|lia].
  right. split; [lia|]. unfold InitializedSlice in *.
  replace (sublist l_pre l_pre before) with (@nil Z).
  - simpl. rewrite app_nil_r. replace i with r_pre in Hinit by lia. exact Hinit.
  - symmetry. unfold sublist. apply sublist_nil. lia.
Qed.

Lemma proof_of_solve_entail_wit_5_split_goal_2 : solve_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in PreH18.
  destruct PreH18 as [[_ Hinit] | [Hbad _]]; [|lia].
  unfold InitializedSlice in Hinit.
  assert (Hlen := f_equal (@Zlength (option Z)) Hinit).
  rewrite Zlength_sublist in Hlen by lia.
  rewrite Zlength_correct, length_map, <- Zlength_correct in Hlen.
  unfold SolveCountPrefix in PreH16. destruct PreH16 as [Hzero _].
  rewrite (set_card_bit_slice_filter__stable_partition
    before l_pre r_pre bit_pre 0) in Hzero by lia.
  replace i with r_pre in Hlen by lia. lia.
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_1 : solve_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in PreH36.
  destruct PreH36 as [[Hbad _] | [_ Hinit]]; [lia|].
  unfold InitializedSlice in Hinit.
  assert (Hwrite := f_equal (@Zlength (option Z)) Hinit).
  rewrite Zlength_sublist in Hwrite by lia.
  rewrite Zlength_correct, length_map, <- Zlength_correct, Zlength_app in Hwrite.
  unfold SolveCountPrefix in PreH34. destruct PreH34 as [Hzero [Hone _]].
  rewrite (set_card_bit_slice_filter__stable_partition
    before l_pre r_pre bit_pre 0) in Hzero by lia.
  rewrite (set_card_bit_slice_filter__stable_partition
    before l_pre r_pre bit_pre 1) in Hone by lia.
  assert (Hbit : BitAt (Znth i before 0) bit_pre = 1).
  { destruct (bit_at_binary__stable_partition (Znth i before 0) bit_pre);
      [contradiction|assumption]. }
  assert (Hstep :
    Zlength (filter (BitIs bit_pre 1) (sublist l_pre (i + 1) before)) =
    Zlength (filter (BitIs bit_pre 1) (sublist l_pre i before)) + 1).
  { rewrite (sublist_split l_pre (i + 1) i before) by lia.
    rewrite (@sublist_single Z 0 i before) by lia.
    rewrite filter_app, Zlength_app. simpl.
    assert (HB : BitIs bit_pre 1 (Znth i before 0) = true).
    { unfold BitIs. apply Z.eqb_eq. exact Hbit. }
    rewrite HB. simpl. rewrite Zlength_cons, Zlength_nil. lia. }
  assert (Hmono :
    Zlength (filter (BitIs bit_pre 1) (sublist l_pre (i + 1) before)) <=
    Zlength (filter (BitIs bit_pre 1) (sublist l_pre r_pre before))).
  { rewrite (sublist_split l_pre r_pre (i + 1) before) by lia.
    rewrite filter_app, Zlength_app.
    pose proof (Zlength_nonneg (filter (BitIs bit_pre 1)
      (sublist (i + 1) r_pre before))). lia. }
  pose proof (filter_bit_lengths__stable_partition
    (sublist l_pre r_pre before) bit_pre) as Hparts.
  rewrite Zlength_sublist in Hparts by lia. lia.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_1 : solve_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in *.
  destruct PreH33 as [[Hbad _] | [_ Hinit]]; [lia|].
  right. split; [lia|]. unfold InitializedSlice in *.
  rewrite (sublist_replace_Znth_step__stable_partition scratch_current_2 None
    (Some (Znth i before 0)) l_pre p) by lia.
  rewrite Hinit.
  rewrite (sublist_split l_pre (i + 1) i before) by lia.
  rewrite (@sublist_single Z 0 i before) by lia.
  rewrite filter_app. simpl.
  assert (Hbit : BitAt (Znth i before 0) bit_pre = 1).
  { destruct (bit_at_binary__stable_partition (Znth i before 0) bit_pre);
      [unfold BitAt in H; contradiction|assumption]. }
  assert (HB : BitIs bit_pre 1 (Znth i before 0) = true).
  { unfold BitIs. apply Z.eqb_eq. exact Hbit. }
  rewrite HB. simpl. rewrite !map_app. simpl. rewrite app_assoc. reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_2 : solve_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. exact PreH29.
Qed.

Lemma proof_of_solve_entail_wit_7_1 : solve_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_1 : solve_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StablePartitionPrefix in *.
  destruct PreH20 as [[Hbad _] | [_ Hinit]]; [lia|].
  right. split; [lia|]. unfold InitializedSlice in *.
  rewrite (sublist_split l_pre (i + 1) i before) by lia.
  rewrite (@sublist_single Z 0 i before) by lia.
  rewrite filter_app. simpl. unfold BitIs, BitAt. rewrite PreH21. simpl.
  fold (BitIs bit_pre 0). fold (BitIs bit_pre 1).
  rewrite app_nil_r. exact Hinit.
Qed.

Lemma proof_of_solve_entail_wit_7_2 : solve_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = r_pre) by lia. subst i.
  assert (Hp : p = r_pre).
  { eapply stable_partition_complete_write_end__solve_base_exits; eauto;
      rewrite ?PreH15, ?PreH16; lia. }
  subst p.
  set (partitioned :=
    filter (BitIs bit_pre 0) (sublist l_pre r_pre before) ++
    filter (BitIs bit_pre 1) (sublist l_pre r_pre before)).
  pose proof
    (partition_copy_back_init__solve_base_exits before scratch_current_2
      l_pre r_pre bit_pre r_pre __default__App_option_Z
      ltac:(lia) ltac:(rewrite PreH15; lia)
      ltac:(rewrite PreH15, PreH16; reflexivity)
      eq_refl PreH20) as [Hpartlen [Hscratch Hcopy]].
  fold partitioned in Hpartlen, Hscratch, Hcopy.
  assert (Hpart_bounds : forall k,
    0 <= k < Zlength partitioned ->
    0 <= Znth k partitioned 0 <= 1000000000).
  { subst partitioned.
    apply (partition_values_bound__solve_base_exits
      before l_pre r_pre bit_pre
      (filter (BitIs bit_pre 0) (sublist l_pre r_pre before) ++
       filter (BitIs bit_pre 1) (sublist l_pre r_pre before))).
    - lia.
    - rewrite PreH15. lia.
    - reflexivity.
    - intros k Hk. apply PreH17. rewrite <- PreH15. exact Hk. }
  pose proof PreH18 as Hcount.
  unfold SolveCountPrefix in Hcount.
  destruct Hcount as
    [Hzeros [Hones [Hcost_before_len [Hcounted_len [Hcount_rows Hdelta]]]]].
  assert (Hcount_nonnegative : forall b, 0 <= b < 30 ->
    (Zlength (Znth b counted_costs_2 __default__List_Z) = 2 /\
     0 <= Znth 0 (Znth b counted_costs_2 __default__List_Z) 0) /\
    0 <= Znth 1 (Znth b counted_costs_2 __default__List_Z) 0).
  { eapply cost_bound_row_shape_nonnegative__solve_base_exits
      with (limit := capacity + (r_pre - l_pre) * (r_pre - l_pre));
      eauto.
    intros b Hb. specialize (Hcount_rows b Hb). tauto. }
  Exists counted_costs_2 partitioned scratch_current_2 before.
  split_pure_spatial.
  - rewrite PreH15. repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try solve [apply Hcount_nonnegative; lia];
      try solve [apply PreH17; lia];
      try solve [
        intros k Hk; apply PreH17; rewrite <- PreH15; exact Hk];
      try solve [apply Hpart_bounds; lia];
      try solve [apply Hscratch; lia];
      try solve [
        intros Hlt; repeat split;
        [apply Hscratch; lia | apply Hpart_bounds; lia |
         apply Hpart_bounds; lia]].
Qed.

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists counted_costs_2 partitioned_2 scratch_current_2 current_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_missing_i
        tmp_p i (Zlength current_2) scratch_current_2
        __default__App_option_Z ltac:(lia)).
    rewrite (PreH28 i ltac:(lia)).
    unfold IntArray.mixedstoreA. simpl.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try solve [apply PreH28; lia];
      try solve [specialize (PreH29 ltac:(lia)); tauto].
Qed.

Lemma proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists counted_costs_2 partitioned scratch_current_2 current_2.
  split_pure_spatial.
  - fold (IntArray.mixedstoreA tmp_p i
      (Some (Znth (i - l_pre) partitioned 0))).
    sep_apply_l_atomic
      (IntArray.mixed_missing_i_merge_to_mixed_full
        tmp_p i (Zlength current_2)
        (Some (Znth (i - l_pre) partitioned 0)) scratch_current_2
        ltac:(lia)).
    rewrite <- PreH28, replace_Znth_Znth by lia.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try solve [apply PreH27; lia].
Qed.

Lemma proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists counted_costs_2 partitioned_2 scratch_current_2
    (replace_Znth i value current_2).
  split_pure_spatial.
  - rewrite Zlength_replace_Znth. repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try solve [rewrite Zlength_replace_Znth; lia];
      try solve [apply PreH27; lia];
      try solve [
        eapply replace_Znth_value_bounds__solve_base_exits
          with (n := n_total); eauto; lia];
      try solve [
        intros k Hk;
        destruct (Z.eq_dec k i) as [-> | Hne];
        [rewrite Znth_replace_Znth_Same by (rewrite PreH17; lia); lia |
         rewrite Znth_replace_Znth_Diff by (rewrite PreH17; lia);
         apply PreH24; lia]];
      try solve [
        intros k Hk; rewrite Zlength_replace_Znth in Hk;
        destruct (Z.eq_dec k i) as [-> | Hne];
        [rewrite Znth_replace_Znth_Same by lia; lia |
         rewrite Znth_replace_Znth_Diff by lia; apply PreH25; lia]];
      try solve [
        intros Hnext; repeat split;
        [apply PreH27; lia | apply PreH26; lia | apply PreH26; lia]];
      try solve [
        eapply partition_copy_back_extend__solve_base_exits; eauto; lia].
Qed.

Lemma proof_of_solve_entail_wit_12 : solve_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = r_pre) by lia. subst i.
  pose proof PreH1 as Heffect.
  unfold SolveEffect in Heffect.
  destruct Heffect as
    [Hafter_len [Hbefore_prefix [Hbefore_suffix [Hpermutation
    [Hcounted_len [Hcost_after_len [Hcost_rows [Hcost_delta Htable]]]]]]]].
  pose proof PreH2 as Hbound.
  unfold CostBound in Hbound.
  destruct Hbound as [Hlimit_nonneg [Hbound_len Hbound_cells]].
  prop_apply
    (IntArray.mixed_full_Zlength tmp_p (Zlength current) scratch_after).
  Intros.
  Exists counted_costs_2 cost_after scratch_after after scratch_current
    partitioned_2 current.
  split_pure_spatial.
  - rewrite Hafter_len. repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try solve [
        intros k Hk; apply PreH3; rewrite PreH21; exact Hk];
      try solve [apply PreH3; lia];
      try solve [apply PreH31; lia];
      try solve [
        eapply cost_bound_row_shape_nonnegative__solve_base_exits
          with (limit :=
            (capacity + (r_pre - l_pre) * (r_pre - l_pre)) +
            (bit_pre - 1 + 1) * (mid - l_pre) * (mid - l_pre));
        [exact Hcost_after_len |
         intros b Hb; specialize (Hcost_rows b Hb); tauto |
         exact PreH2]];
      try solve [
        replace
          ((capacity + (r_pre - l_pre) * (r_pre - l_pre)) +
             bit_pre * (mid - l_pre) * (mid - l_pre))
          with
          ((capacity + (r_pre - l_pre) * (r_pre - l_pre)) +
             (bit_pre - 1 + 1) * (mid - l_pre) * (mid - l_pre))
          by ring; exact PreH2].
Qed.

Lemma proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (bit_pre = -1) by lia. subst bit_pre. cbn.
  replace (capacity + 0) with capacity by lia.
  exact PreH13.
Qed.

Lemma proof_of_solve_return_wit_1_split_goal_2 : solve_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply solve_effect_negative__solve_base_exits
    with (d := __default__List_Z); eauto; try lia.
  intros b Hb. specialize (PreH14 b Hb). tauto.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solve_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_solve_return_wit_2_split_goal_1 : solve_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply cost_bound_monotone__solve_base_exits; [exact PreH14 |].
  assert (Hprod : 0 <= (bit_pre + 1) * (r_pre - l_pre)).
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (Hprod2 :
    0 <= ((bit_pre + 1) * (r_pre - l_pre)) * (r_pre - l_pre)).
  { apply Z.mul_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solve_return_wit_2_split_goal_2 : solve_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply solve_effect_short__solve_base_exits
    with (d := __default__List_Z); eauto; try lia.
  intros b Hb. specialize (PreH15 b Hb). tauto.
Qed.

Lemma proof_of_solve_return_wit_2 : solve_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_return_wit_2_split_goal_1.
  - Goal_apply proof_of_solve_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_solve_return_wit_3 : solve_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists scratch_after_2 after_2 cost_after_2.
  rewrite <- PreH20.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial.
      pose proof PreH28 as Hcopy.
      unfold PartitionCopyBack in Hcopy.
      destruct Hcopy as [Hcopylen _].
      apply (solve_effect_compose_partition__solve_recursive
        before partition_before partitioned partition_scratch
        first_after after_2 cost_before counted_costs first_cost cost_after_2
        l_pre mid r_pre bit_pre zeros ones p __default__App_option_Z);
        try eassumption; lia.
    + dump_pre_spatial.
      eapply cost_bound_monotone__solve_counting.
      * exact PreH2.
      * replace (bit_pre - 1 + 1) with bit_pre by lia.
        apply square_partition_budget__solve_recursive; lia.
    + dump_pre_spatial.
      exact PreH3.
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure_split_goal_1 : solve_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure_split_goal_2 : solve_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (square_partition_budget__solve_recursive
    capacity bit_pre l_pre mid r_pre ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- PreH23.
  eapply Z.le_trans.
  2: exact PreH28.
  eapply Z.le_trans.
  2: exact H.
  assert (Hsq : 0 <= (r_pre - mid) * (r_pre - mid)) by nia.
  assert (Hnonneg : 0 <= bit_pre * ((r_pre - mid) * (r_pre - mid))).
  { apply Z.mul_nonneg_nonneg; assumption. }
  replace (bit_pre * (r_pre - mid) * (r_pre - mid))
    with (bit_pre * ((r_pre - mid) * (r_pre - mid))) by ring.
  lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure_split_goal_3 : solve_partial_solve_wit_9_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure_split_goal_4 : solve_partial_solve_wit_9_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure_split_goal_5 : solve_partial_solve_wit_9_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (square_partition_budget__solve_recursive
    capacity bit_pre l_pre mid r_pre ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- PreH23.
  eapply Z.le_trans.
  2: exact PreH28.
  eapply Z.le_trans.
  2: exact H.
  assert (Hsq : 0 <= (r_pre - mid) * (r_pre - mid)) by nia.
  assert (Hnonneg : 0 <= bit_pre * ((r_pre - mid) * (r_pre - mid))).
  { apply Z.mul_nonneg_nonneg; assumption. }
  replace (bit_pre * (r_pre - mid) * (r_pre - mid))
    with (bit_pre * ((r_pre - mid) * (r_pre - mid))) by ring.
  lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure : solve_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_solve_partial_solve_wit_9_pure_split_goal_2.
  - Goal_apply proof_of_solve_partial_solve_wit_9_pure_split_goal_3.
  - Goal_apply proof_of_solve_partial_solve_wit_9_pure_split_goal_4.
  - Goal_apply proof_of_solve_partial_solve_wit_9_pure_split_goal_5.
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure_split_goal_1 : solve_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure_split_goal_2 : solve_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH20.
  pose proof (square_partition_budget__solve_recursive
    capacity bit_pre l_pre mid r_pre ltac:(lia) ltac:(lia) ltac:(lia)).
  replace (bit_pre - 1 + 1) with bit_pre by lia.
  eapply Z.le_trans; [exact H | exact PreH25].
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure_split_goal_3 : solve_partial_solve_wit_10_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros i Hi.
  apply PreH35.
  rewrite <- PreH31.
  exact Hi.
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure_split_goal_4 : solve_partial_solve_wit_10_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure_split_goal_5 : solve_partial_solve_wit_10_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH20.
  pose proof (square_partition_budget__solve_recursive
    capacity bit_pre l_pre mid r_pre ltac:(lia) ltac:(lia) ltac:(lia)).
  replace (bit_pre - 1 + 1) with bit_pre by lia.
  eapply Z.le_trans; [exact H | exact PreH25].
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure_split_goal_6 : solve_partial_solve_wit_10_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solve_partial_solve_wit_10_pure : solve_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_solve_partial_solve_wit_10_pure_split_goal_2.
  - Goal_apply proof_of_solve_partial_solve_wit_10_pure_split_goal_3.
  - Goal_apply proof_of_solve_partial_solve_wit_10_pure_split_goal_4.
  - Goal_apply proof_of_solve_partial_solve_wit_10_pure_split_goal_5.
  - Goal_apply proof_of_solve_partial_solve_wit_10_pure_split_goal_6.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH15 as [Htable _].
  destruct Htable as [Hlen [_ Hcost]].
  specialize (Hcost b 1 ltac:(lia) ltac:(lia)) as Hcontrib.
  pose proof (bit_contribution_pair_bound__solver_choice_loop
    input_values 29 b 1 (CostAt costs b 1) Hcontrib) as Hbound.
  assert (Hrow : Znth b costs __default__List_Z = Znth b costs nil).
  { apply Znth_indep. lia. }
  rewrite Hrow.
  unfold CostAt in Hbound.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH15 as [Htable _].
  destruct Htable as [Hlen [_ Hcost]].
  specialize (Hcost b 1 ltac:(lia) ltac:(lia)) as Hcontrib.
  pose proof (bit_contribution_pair_bound__solver_choice_loop
    input_values 29 b 1 (CostAt costs b 1) Hcontrib) as Hbound.
  assert (Hrow : Znth b costs __default__List_Z = Znth b costs nil).
  { apply Znth_indep. lia. }
  rewrite Hrow.
  unfold CostAt in Hbound.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hshift : 1 * 2 ^ b = Z.shiftl 1 b).
  { rewrite Z.shiftl_mul_pow2 by lia. ring. }
  rewrite Hshift.
  pose proof (bit_mask_singleton_bounds__solver_choice_loop 0 b
    ltac:(lia) ltac:(split; [lia |]; apply Z.pow_pos_nonneg; lia))
    as [Hs _].
  rewrite Hs.
  assert (Hpow : 2 ^ b <= 2 ^ 29) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 29) with 536870912 in Hpow.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hshift : 1 * 2 ^ b = Z.shiftl 1 b).
  { rewrite Z.shiftl_mul_pow2 by lia. ring. }
  rewrite Hshift.
  pose proof (bit_mask_singleton_bounds__solver_choice_loop 0 b
    ltac:(lia) ltac:(split; [lia |]; apply Z.pow_pos_nonneg; lia))
    as [Hs _].
  rewrite Hs.
  pose proof (Z.pow_nonneg 2 b ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_3 : solver_safety_wit_22_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_4 : solver_safety_wit_22_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH15 as [Htable _].
  destruct Htable as [Hlen [_ Hcost]].
  specialize (Hcost b 0 ltac:(lia) ltac:(lia)) as Hcontrib.
  pose proof (bit_contribution_pair_bound__solver_choice_loop
    input_values 29 b 0 (CostAt costs b 0) Hcontrib) as Hbound.
  assert (Hrow : Znth b costs __default__List_Z = Znth b costs nil).
  { apply Znth_indep. lia. }
  rewrite Hrow.
  unfold CostAt in Hbound.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct PreH15 as [Htable _].
  destruct Htable as [Hlen [_ Hcost]].
  specialize (Hcost b 0 ltac:(lia) ltac:(lia)) as Hcontrib.
  pose proof (bit_contribution_pair_bound__solver_choice_loop
    input_values 29 b 0 (CostAt costs b 0) Hcontrib) as Hbound.
  assert (Hrow : Znth b costs __default__List_Z = Znth b costs nil).
  { apply Znth_indep. lia. }
  rewrite Hrow.
  unfold CostAt in Hbound.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply input_copy_prefix_extend__solver_copy_init; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH8.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hacells : a_cells = map (@Some Z) input_values).
  {
    apply input_copy_prefix_complete__solver_copy_init.
    - lia.
    - rewrite <- PreH2.
      exact PreH10.
  }
  subst a_cells.
  assert (Hzero : ZeroCostPrefix
    (repeat (None :: None :: nil) 30) 0).
  {
    unfold ZeroCostPrefix.
    split.
    - rewrite Zlength_correct, repeat_length. reflexivity.
    - split.
      + intros row Hrow.
        rewrite Znth_repeat_lt by lia.
        reflexivity.
      + intros row choice Hrow Hchoice. lia.
  }
  Exists tmp_p_2 a_p_2 (repeat (None :: None :: nil) 30)
    nil tmp_cells_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.mixed_full_to_full
      a_p_2 n_pre input_values).
    cbn [Int64Array2.full store_array store_array_rec].
    replace (&( "cost" ) + 0 * (sizeof(INT64) * 2)) with (&( "cost" )) by lia.
    replace (30 - 0) with 30 by lia.
    repeat cancel.
    + rewrite Z.mul_0_l, Z.add_0_r.
      cancel.
      entailer!.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (undef_cost_table_unfold__solver_zero_cost
    ((&( "cost" )) + b * (sizeof(INT64) * 2)) (30 - b)).
  - dump_pre_spatial. lia.
  - Exists tmp_p_2 a_p_2 cost_cells_2 zero_rows_2 tmp_cells_2.
    replace ((&( "cost" )) + b * (sizeof(INT64) * 2) + sizeof(INT64) * 2)
      with ((&( "cost" )) + (b + 1) * (sizeof(INT64) * 2)) by nia.
    replace (30 - b - 1) with (30 - (b + 1)) by lia.
    split_pure_spatial.
    + cancel (IntArray.full input_pre n_pre input_values).
      cancel (IntArray.full a_p_2 n_pre input_values).
      cancel (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2).
      cancel (Int64Array2.full (&( "cost" )) b 2 zero_rows_2).
      cancel (((&( "cost" )) + b * (sizeof(INT64) * 2) + 0 * sizeof(INT64)) # Int64 |->_).
      cancel (((&( "cost" )) + b * (sizeof(INT64) * 2) + 1 * sizeof(INT64)) # Int64 |->_).
      cancel (Int64Array2.undef_full
        ((&( "cost" )) + (b + 1) * (sizeof(INT64) * 2))
        (30 - (b + 1)) 2).
      cancel (((&( "a" )) # Ptr |-> a_p_2)).
      cancel (((&( "tmp" )) # Ptr |-> tmp_p_2)).
      cancel (out_inv_pre # Int64 |->_).
      cancel (out_x_pre # Int |->_).
    + split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (int64_zero_row_full__solver_zero_cost
    ((&( "cost" )) + b * (2 * sizeof(INT64)))).
  sep_apply_l_atomic (full_cost_rows_snoc__solver_zero_cost
    (&( "cost" )) b zero_rows_2 (0 :: 0 :: nil)).
  - dump_pre_spatial. exact PreH8.
  - Exists tmp_p_2 a_p_2
      (replace_Znth b (Some 0 :: Some 0 :: nil) cost_cells_2)
      (zero_rows_2 ++ (0 :: 0 :: nil) :: nil) tmp_cells_2.
    replace (30 - b - 1) with (30 - (b + 1)) by lia.
    assert (Hzprefix : ZeroCostPrefix
      (replace_Znth b (Some 0 :: Some 0 :: nil) cost_cells_2) (b + 1)).
    { apply zero_cost_prefix_extend__solver_zero_cost; auto. }
    pose proof (zero_rows_extend__solver_zero_cost
      zero_rows_2 __default__List_Z b PreH8 PreH9) as [Hzlen Hzrows].
    split_pure_spatial.
    + cancel (IntArray.full input_pre n_pre input_values).
      cancel (IntArray.full a_p_2 n_pre input_values).
      cancel (IntArray.mixed_full tmp_p_2 n_pre tmp_cells_2).
      cancel (Int64Array2.full (&( "cost" )) (b + 1) 2
        (zero_rows_2 ++ (0 :: 0 :: nil) :: nil)).
      cancel (Int64Array2.undef_full
        ((&( "cost" )) + (b + 1) * (2 * sizeof(INT64)))
        (30 - (b + 1)) 2).
      cancel (((&( "a" )) # Ptr |-> a_p_2)).
      cancel (((&( "tmp" )) # Ptr |-> tmp_p_2)).
      cancel (out_inv_pre # Int64 |->_).
      cancel (out_x_pre # Int |->_).
    + split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb30 : b_2 = 30) by lia.
  rewrite Hb30 in *.
  rewrite PreH2 in *.
  assert (Hcost : CostBound zero_rows 0).
  { apply (zero_cost_prefix_complete__solver_zero_cost
      zero_rows __default__List_Z).
    - lia.
    - intros bit Hbit. apply PreH10. lia. }
  unfold Int64Array2.undef_full, store_undef_array.
  replace (Z.to_nat (30 - 30)) with 0%nat by lia.
  cbn [store_undef_array_rec].
  Intros_p Hempty.
  Exists tmp_p_2 a_p_2 zero_rows tmp_cells_2.
  split_pure_spatial.
  - cancel (IntArray.full input_pre (Zlength input_values) input_values).
    cancel (IntArray.full a_p_2 (Zlength input_values) input_values).
    cancel (IntArray.mixed_full tmp_p_2 (Zlength input_values) tmp_cells_2).
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia; try nia; try int_auto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH1 as Heffect_shape.
  unfold SolveEffect in Heffect_shape.
  destruct Heffect_shape as [Hafterlen _].
  pose proof PreH10 as Hzero_bound.
  unfold CostBound in Hzero_bound.
  destruct Hzero_bound as [_ [_ Hzero]].
  assert (Htable : CostTable input_values cost_after).
  {
    eapply solve_effect_full_range_cost_table__solver_solve_transition.
    - exact PreH1.
    - exact PreH4.
    - intros bit choice Hbit Hchoice.
      specialize (Hzero bit choice Hbit Hchoice).
      lia.
  }
  pose proof (xor_choice_prefix_zero__solver_solve_transition
    input_values cost_after Htable) as Hprefix.
  prop_apply_p (IntArray.mixed_full_Zlength tmp_p_2
    (Zlength input_values) scratch_after).
  Intros_p Hscratchlen.
  Exists tmp_p_2 a_p_2 cost_after scratch_after after.
  rewrite PreH4.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH15 as HP.
  destruct HP as [Htable _].
  destruct Htable as [Hlen [Hrowlens _]].
  Exists tmp_p_2 a_p_2 costs_2 tmp_cells_2 current_2.
  split_pure_spatial.
  - assert (Hroweq : Znth b costs_2 __default__List_Z = Znth b costs_2 nil).
    { apply Znth_indep. lia. }
    rewrite Hroweq.
    sep_apply_l_atomic
      (int64_cost_table_expose__solver_choice_loop
        &( "cost") costs_2 b nil Hlen ltac:(lia)
        (Hrowlens b ltac:(lia))).
    cancel.
    change (sizeof ( INT64 )) with 8.
    replace (2 * 8) with 16 by ring.
    replace (1 * 8) with 8 by ring.
    replace (0 * 8) with 0 by ring.
    cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists tmp_p_2 a_p_2 costs_2 tmp_cells_2 current_2.
  pose proof PreH15 as Hprefix.
  unfold XorChoicePrefix in Hprefix.
  destruct Hprefix as [Htable [Hinvsum Hxsum]].
  unfold CostTable in Htable.
  destruct Htable as [Hcostlen [Hrowlens Hcontrib]].
  assert (Hrowb : Zlength (Znth b costs_2 nil) = 2)
    by (apply Hrowlens; lia).
  assert (Hroweq : Znth b costs_2 __default__List_Z = Znth b costs_2 nil).
  { apply Znth_indep. rewrite Hcostlen. lia. }
  assert (Hrowbd : Zlength (Znth b costs_2 __default__List_Z) = 2).
  { rewrite Hroweq. exact Hrowb. }
  assert (Hcost1 : CostAt costs_2 b 1 =
      Znth 1 (Znth b costs_2 __default__List_Z) 0).
  { unfold CostAt. rewrite Hroweq. reflexivity. }
  assert (Hcost0 : CostAt costs_2 b 0 =
      Znth 0 (Znth b costs_2 __default__List_Z) 0).
  { unfold CostAt. rewrite Hroweq. reflexivity. }
  assert (Hprefix0 : XorChoicePrefix input_values costs_2 b inv x).
  { unfold XorChoicePrefix. repeat split; assumption. }
  pose proof (xor_choice_prefix_bounds__solver_choice_loop
    input_values costs_2 b inv x Hprefix0 ltac:(lia)) as [Hinvb Hxb].
  pose proof (bit_mask_singleton_bounds__solver_choice_loop
    x b ltac:(lia) Hxb) as [Hmask [Hlor Hlorbounds]].
  pose proof (xor_choice_prefix_step_one__solver_choice_loop
    input_values costs_2 b inv x Hprefix0 ltac:(lia) ltac:(
      rewrite Hcost1, Hcost0; exact PreH1)) as Hprefix1.
  rewrite Hcost1 in Hprefix1.
  rewrite <- Hlor in Hprefix1.
  pose proof (xor_choice_prefix_bounds__solver_choice_loop
    input_values costs_2 (b + 1)
      (inv + Znth 1 (Znth b costs_2 __default__List_Z) 0)
      (Z.lor x (signed_last_nbits (Z.shiftl 1 b) 32))
      Hprefix1 ltac:(lia)) as [Hinvnext Hxnext].
  split_pure_spatial.
  - change (sizeof ( INT64 )) with 8.
    replace (2 * 8) with 16 by ring.
    replace (0 * 8) with 0 by ring.
    replace (1 * 8) with 8 by ring.
    sep_apply_left (int64_cost_table_merge__solver_choice_loop
      &( "cost") costs_2 b __default__List_Z Hcostlen ltac:(lia) Hrowbd).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists tmp_p_2 a_p_2 costs_2 tmp_cells_2 current_2.
  pose proof PreH15 as Hprefix.
  unfold XorChoicePrefix in Hprefix.
  destruct Hprefix as [Htable [Hinvsum Hxsum]].
  unfold CostTable in Htable.
  destruct Htable as [Hcostlen [Hrowlens Hcontrib]].
  assert (Hrowb : Zlength (Znth b costs_2 nil) = 2)
    by (apply Hrowlens; lia).
  assert (Hroweq : Znth b costs_2 __default__List_Z = Znth b costs_2 nil).
  { apply Znth_indep. rewrite Hcostlen. lia. }
  assert (Hrowbd : Zlength (Znth b costs_2 __default__List_Z) = 2).
  { rewrite Hroweq. exact Hrowb. }
  assert (Hcost1 : CostAt costs_2 b 1 =
      Znth 1 (Znth b costs_2 __default__List_Z) 0).
  { unfold CostAt. rewrite Hroweq. reflexivity. }
  assert (Hcost0 : CostAt costs_2 b 0 =
      Znth 0 (Znth b costs_2 __default__List_Z) 0).
  { unfold CostAt. rewrite Hroweq. reflexivity. }
  assert (Hprefix0 : XorChoicePrefix input_values costs_2 b inv x).
  { unfold XorChoicePrefix. repeat split; assumption. }
  pose proof (xor_choice_prefix_step_zero__solver_choice_loop
    input_values costs_2 b inv x Hprefix0 ltac:(lia) ltac:(
      rewrite Hcost1, Hcost0; lia)) as Hprefix1.
  rewrite Hcost0 in Hprefix1.
  pose proof (xor_choice_prefix_bounds__solver_choice_loop
    input_values costs_2 (b + 1)
      (inv + Znth 0 (Znth b costs_2 __default__List_Z) 0) x
      Hprefix1 ltac:(lia)) as [Hinvnext Hxnext].
  split_pure_spatial.
  - change (sizeof ( INT64 )) with 8.
    replace (&( "cost") + b * (8 * 2) + 0 * 8)
      with (&( "cost") + b * 16 + 0) by ring.
    replace (&( "cost") + b * (8 * 2) + 1 * 8)
      with (&( "cost") + b * 16 + 8) by ring.
    replace (&( "cost") + (b + 1) * (8 * 2))
      with (&( "cost") + (b + 1) * 16) by ring.
    replace (2 * 8) with 16 by ring.
    replace (0 * 8) with 0 by ring.
    replace (1 * 8) with 8 by ring.
    sep_apply_left (int64_cost_table_merge__solver_choice_loop
      &( "cost") costs_2 b __default__List_Z Hcostlen ltac:(lia) Hrowbd).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists costs_2 tmp_p_2 a_p_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_to_undef_full a_p_2 n_pre current).
    sep_apply_l_atomic
      (IntArray.mixed_full_to_undef_full tmp_p_2 n_pre tmp_cells).
    cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      assert (Hb : b = 30) by lia.
      rewrite Hb in PreH15.
      apply (xor_choice_prefix_complete_spec__solver_final
        input_values costs_2 inv x).
      * intros i Hi. apply PreH13. lia.
      * exact PreH15.
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure_split_goal_1 : solver_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros b Hb.
  destruct (PreH8 b Hb) as [[Hlen Hzero] Hone].
  repeat split; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure_split_goal_2 : solver_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_5_pure_split_goal_2.
Qed.
