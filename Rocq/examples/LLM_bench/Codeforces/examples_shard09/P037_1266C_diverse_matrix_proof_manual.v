From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P037_1266C_diverse_matrix_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P037_1266C_diverse_matrix_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P037_1266C_diverse_matrix_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists rows_2.
  subst r_pre.
  unfold ConstructionPrefix, StagedConstruction, ConstructionIndices in PreH2.
  simpl in PreH2.
  subst rows_2.
  simpl.
  split_pure_spatial.
  - unfold IntArray2.mixed_full, IntArray2.mixed_row_store,
      IntArray2.row_addr, store_array.
    simpl.
    rewrite Znth0_cons.
    replace (m_pre + 0) with m_pre by lia.
    unfold IntArray2.ElemArray.mixed_full, IntArray.mixed_full.
    unfold IntArray2.ElemArray.mixedstoreA, IntArray.mixedstoreA.
    normalize.
    Intros_p Hone.
    Intros_p Hnil.
    cancel.
  - split_pures; dump_pre_spatial.
    all: try lia.
    unfold ConstructionPrefix, StagedConstruction, ConstructionIndices.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists rows_2.
  replace (1 - 1) with 0 by lia.
  split_pure_spatial.
  - cancel (IntArray.mixed_full m_pre c_pre
      (Znth 0 rows_2 __default__List__App_option_Z)).
  - split_pures; dump_pre_spatial.
    all: try lia.
    exact PreH4.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists ((replace_Znth (j - 1) (Some (j + 1))
    (Znth 0 rows_2 __default__List__App_option_Z)) :: nil).
  subst r_pre.
  replace ((j + 1) - 1) with j by lia.
  simpl.
  split_pure_spatial.
  - rewrite Znth0_cons.
    cancel (IntArray.mixed_full m_pre c_pre
      (replace_Znth (j - 1) (Some (j + 1))
        (Znth 0 rows_2 __default__List__App_option_Z))).
  - split_pures; dump_pre_spatial.
    all: try lia.
    eapply construction_prefix_single_row_step__initial_single_row;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i - 1) * c_pre + (1 - 1)) with ((i - 1) * c_pre) by ring.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = c_pre + 1) by lia. subst j.
  replace ((i + 1 - 1) * c_pre)
    with ((i - 1) * c_pre + (c_pre + 1 - 1)) by ring.
  exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth (i - 1)
    (replace_Znth (j - 1) (Some ((c_pre + i) * j))
      (Znth (i - 1) rows_2 __default__List__App_option_Z)) rows_2).
  split_pure_spatial.
  - replace (m_pre + ((i - 1) * c_pre + (j - 1)) * sizeof(INT))
      with (m_pre + (i - 1) * c_pre * sizeof(INT) +
        (j - 1) * sizeof(INT)) by ring.
    fold (IntArray.mixedstoreA
      (m_pre + (i - 1) * c_pre * sizeof(INT)) (j - 1)
      (Some ((c_pre + i) * j))).
    sep_apply_l_atomic (IntArray.mixed_missing_i_merge_to_mixed_full
      (m_pre + (i - 1) * c_pre * sizeof(INT)) (j - 1) c_pre
      (Some ((c_pre + i) * j))
      (Znth (i - 1) rows_2 __default__List__App_option_Z) ltac:(lia)).
    assert (Hrow_addr :
      m_pre + (i - 1) * c_pre * sizeof(INT) =
      IntArray2.row_addr m_pre c_pre (i - 1)) by
        (unfold IntArray2.row_addr; ring).
    rewrite Hrow_addr.
    unfold IntArray.mixed_full, IntArray.mixedstoreA.
    fold (IntArray2.ElemArray.mixed_full
      (IntArray2.row_addr m_pre c_pre (i - 1)) c_pre
      (replace_Znth (j - 1) (Some ((c_pre + i) * j))
        (Znth (i - 1) rows_2 __default__List__App_option_Z))).
    pose proof (IntArray2.mixed_missing_i_merge_to_mixed_full
      m_pre (i - 1) r_pre c_pre rows_2
      (replace_Znth (j - 1) (Some ((c_pre + i) * j))
        (Znth (i - 1) rows_2 __default__List__App_option_Z)) ltac:(lia))
      as Hmerge_outer.
    unfold IntArray2.ElemArray.mixed_full,
      IntArray2.ElemArray.mixedstoreA in Hmerge_outer.
    sep_apply_l_atomic Hmerge_outer.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
    replace ((i - 1) * c_pre + (j + 1 - 1))
      with ((i - 1) * c_pre + j) by ring.
    assert (Hrowslen : Zlength rows_2 = r_pre).
    { unfold ConstructionPrefix in PreH15.
      rewrite PreH15. unfold StagedConstruction.
      rewrite Zlength_map__final_results.
      pose proof
        (construction_indices_characterization__final_results r_pre ltac:(lia))
        as [Hlen _]. exact Hlen. }
    rewrite (Znth_indep rows_2 (i - 1)
      __default__List__App_option_Z (@nil (option Z))) by lia.
    eapply construction_prefix_multirow_step__multirow_transitions; eauto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = r_pre + 1) by lia. subst i.
  assert (Hrows : rows = Array2.some_rows (ConstructionMatrix r_pre c_pre)).
  { unfold Array2.some_rows.
    apply construction_prefix_completion__final_results; try lia.
    replace ((r_pre + 1 - 1) * c_pre) with (r_pre * c_pre) in PreH11 by ring.
    exact PreH11. }
  rewrite Hrows.
  Exists (ConstructionMatrix r_pre c_pre)
    (Some (ConstructionMatrix r_pre c_pre)).
  sep_apply_l_atomic
    (Array2Convert.int_mixed_full_to_full m_pre r_pre c_pre
      (ConstructionMatrix r_pre c_pre)).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    apply construction_matrix_optimal_spec__final_results; try lia.
    intro Hpair. inversion Hpair. lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = c_pre + 1) by lia. subst j.
  subst r_pre.
  assert (Hrows : rows = Array2.some_rows (ConstructionMatrix 1 c_pre)).
  { unfold Array2.some_rows.
    apply construction_prefix_completion__final_results; try lia.
    replace (c_pre + 1 - 1) with (1 * c_pre) in PreH9 by ring.
    exact PreH9. }
  rewrite Hrows.
  Exists (ConstructionMatrix 1 c_pre)
    (Some (ConstructionMatrix 1 c_pre)).
  assert (Hmatrix : ConstructionMatrix 1 c_pre =
      (map (fun j => ConstructionCell 1 c_pre 0 j)
        (ConstructionIndices c_pre) :: nil)).
  { unfold ConstructionMatrix. change (ConstructionIndices 1) with (0 :: nil).
    reflexivity. }
  rewrite Hmatrix in *.
  unfold Array2.some_rows in *; simpl in *.
  rewrite Znth0_cons.
  sep_apply_l_atomic
    (IntArray.mixed_full_to_full m_pre c_pre
      (map (fun j => ConstructionCell 1 c_pre 0 j)
        (ConstructionIndices c_pre))).
  split_pure_spatial.
  - unfold IntArray2.full, store_array, IntArray2.row_store,
      IntArray2.row_addr; simpl.
    replace (m_pre + 0 * c_pre * sizeof(INT)) with m_pre by ring.
    split_pure_spatial.
    + replace (m_pre + 0) with m_pre by lia.
      change (IntArray.full m_pre c_pre
        (map (fun j => ConstructionCell 1 c_pre 0 j)
          (ConstructionIndices c_pre)) |--
        IntArray.full m_pre c_pre
          (map (fun j => ConstructionCell 1 c_pre 0 j)
            (ConstructionIndices c_pre))).
      cancel.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures; dump_pre_spatial; try reflexivity.
    rewrite <- Hmatrix.
    apply construction_matrix_optimal_spec__final_results; try lia.
    intro Hpair. inversion Hpair. lia.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact no_diverse_one_by_one__degenerate_result.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (StagedConstruction r_pre c_pre 0).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Array2Convert.int_undef_full_to_mixed_full m_pre r_pre c_pre).
    unfold Array2Convert.undef_rows.
    rewrite staged_construction_zero__initial_single_row.
    cancel (IntArray2.mixed_full m_pre r_pre c_pre
      (repeat (repeat None (Z.to_nat c_pre)) (Z.to_nat r_pre))).
  - dump_pre_spatial.
    unfold ConstructionPrefix.
    reflexivity.
Qed.
