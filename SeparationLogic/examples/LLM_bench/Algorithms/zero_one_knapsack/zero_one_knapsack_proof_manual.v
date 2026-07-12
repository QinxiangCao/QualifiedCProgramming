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
From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib.
Local Open Scope sac.

Lemma proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2.
Proof.
  pre_process.
  Exists nil.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    replace (0 * width) with 0 by lia.
    sep_apply (IntArray.undef_full_split_to_undef_seg dp_pre 0 ((n_pre + 1) * (capacity_pre + 1))).
    + cancel (IntArray.undef_seg dp_pre 0 ((n_pre + 1) * (capacity_pre + 1))).
      rewrite <- (IntArray.seg_empty dp_pre 0 0).
      cancel (IntArray.seg dp_pre 0 0 nil).
    + lia.
  - entailer!.
    + intros k Hk. rewrite Zlength_nil in Hk. lia.
    + unfold KnapsackRowsDone, KnapsackTablePrefix.
      repeat split; try rewrite Zlength_nil; try lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3.
Proof.
  pre_process.
  Exists dp_l_2.
  replace (i * width + 0) with (i * width) by lia.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (i * width) dp_l_2).
    cancel (IntArray.undef_seg dp_pre (i * width) ((n_pre + 1) * (capacity_pre + 1))).
  - entailer!.
    eapply KnapsackRowsDone_to_RowProgress0; eauto.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_4 : zeroOneKnapsack_entail_wit_4.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (i * width + j) dp_l_2).
    cancel (IntArray.undef_seg dp_pre (i * width + j) ((n_pre + 1) * (capacity_pre + 1))).
  - entailer!.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5.
Proof.
  pre_process.
  subst i.
  Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - cancel.
    cancel.
  - repeat split_pures; try solve [dump_pre_spatial; auto; try lia].
    + dump_pre_spatial.
      apply KnapsackCellCorrect_row0_zero; lia.
    + prop_apply IntArray.seg_Zlength.
      Intros.
      dump_pre_spatial.
      eapply KnapsackRowProgress_append_cell;
        [ rewrite Zlength_app_cons in H; unfold KnapsackCellIndex; lia
        | exact PreH21
        | lia
        | apply KnapsackCellCorrect_row0_zero; lia ].
    + dump_pre_spatial.
      intros k Hk.
      apply append_zero_range; auto.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6.
Proof.
  pre_process.
  subst j.
  Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - cancel.
    cancel.
  - repeat split_pures; try solve [dump_pre_spatial; auto; try lia].
    + dump_pre_spatial.
      apply KnapsackCellCorrect_col0_zero.
      * rewrite PreH10; lia.
      * lia.
      * intros k Hk.
        specialize (PreH24 k ltac:(lia)).
        lia.
    + prop_apply IntArray.seg_Zlength.
      Intros.
      dump_pre_spatial.
      eapply KnapsackRowProgress_append_cell;
        [ rewrite Zlength_app_cons in H; unfold KnapsackCellIndex; lia
        | exact PreH22
        | lia
        | apply KnapsackCellCorrect_col0_zero;
          [ rewrite PreH10; lia
          | lia
          | intros k Hk;
            specialize (PreH24 k ltac:(lia));
            lia ] ].
    + dump_pre_spatial.
      intros k Hk.
      apply append_zero_range; auto.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_7 : zeroOneKnapsack_entail_wit_7.
Proof.
  pre_process.
  assert (Hitem_bounds : 0 <= i - 1 < n_pre) by lia.
  pose proof (PreH24 (i - 1) Hitem_bounds) as Hweight_bounds.
  pose proof (PreH25 (i - 1) Hitem_bounds) as Hvalue_bounds.
  assert (Hprev_nonneg : 0 <= (i - 1) * width + j) by nia.
  assert (Hprev_lt_idx : (i - 1) * width + j < idx) by nia.
  assert (Hprev_lt_total : (i - 1) * width + j < (n_pre + 1) * (capacity_pre + 1)) by lia.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 idx dp_l_2).
    cancel (IntArray.undef_seg dp_pre idx ((n_pre + 1) * (capacity_pre + 1))).
  - split_pures; dump_pre_spatial; try lia; auto.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8.
Proof.
  pre_process.
  Exists dp_l.
  split_pure_spatial.
  - cancel.
    cancel (IntArray.seg dp_pre 0 idx dp_l).
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
  - assert (Hidx_in : 0 <= (i - 1) * width + j < Zlength dp_l).
    {
      eapply (KnapsackRowProgress_index_bound weights_l values_l capacity_pre dp_l i j); eauto.
      rewrite <- PreH1; rewrite <- PreH23; lia.
    }
    match goal with
    | Hbound : forall k : Z, 0 <= k < Zlength dp_l ->
        0 <= Znth k dp_l 0 <= 4000000 |- _ =>
        pose proof (Hbound ((i - 1) * width + j) Hidx_in) as Hidx_value_bound
    end.
    assert (Hidx_cell :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((i - 1) * width + j) dp_l 0)).
    {
      replace ((i - 1) * width + j)
        with (KnapsackCellIndex capacity_pre (i - 1) j)
        by (unfold KnapsackCellIndex; rewrite PreH1; lia).
      eapply KnapsackRowProgress_lookup_cell; eauto; try lia.
      unfold KnapsackCellIndex; rewrite <- PreH1; rewrite <- PreH23; lia.
    }
    split_pures; dump_pre_spatial;
      repeat match goal with
      | |- context [?x - 0] => replace (x - 0) with x by lia
      end;
      auto; try lia.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9.
Proof.
  pre_process.
  assert (Htake_nonneg : 0 <= j - w) by lia.
  assert (Htake_cap : j - w <= capacity_pre) by lia.
  assert (Htake_idx_nonneg : 0 <= (i - 1) * width + (j - w)) by nia.
  assert (Htake_idx_lt_idx : (i - 1) * width + (j - w) < idx) by nia.
  assert (Htake_idx_lt_total : (i - 1) * width + (j - w) < (n_pre + 1) * (capacity_pre + 1)) by lia.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 idx dp_l_2).
    cancel (IntArray.undef_seg dp_pre idx ((n_pre + 1) * (capacity_pre + 1))).
  - split_pures; dump_pre_spatial; try lia; auto.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10.
Proof.
  pre_process.
  Exists dp_l.
  split_pure_spatial.
  - cancel.
    cancel (IntArray.seg dp_pre 0 idx dp_l).
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
  - assert (Htake_idx_in :
      0 <= (i - 1) * width + (j - w) < Zlength dp_l).
    {
      eapply (KnapsackRowProgress_index_bound weights_l values_l capacity_pre dp_l i j); eauto.
      rewrite <- PreH1; rewrite <- PreH23; lia.
    }
    match goal with
    | Hbound : forall k : Z, 0 <= k < Zlength dp_l ->
        0 <= Znth k dp_l 0 <= 4000000 |- _ =>
        pose proof (Hbound ((i - 1) * width + (j - w)) Htake_idx_in)
          as Htake_value_bound
    end.
    assert (Htake_cell :
      KnapsackCellCorrect weights_l values_l (i - 1) (j - w)
        (Znth ((i - 1) * width + (j - w)) dp_l 0)).
    {
      replace ((i - 1) * width + (j - w))
        with (KnapsackCellIndex capacity_pre (i - 1) (j - w))
        by (unfold KnapsackCellIndex; rewrite PreH1; lia).
      eapply KnapsackRowProgress_lookup_cell; eauto; try lia.
      unfold KnapsackCellIndex; rewrite <- PreH1; rewrite <- PreH23; lia.
    }
    split_pures; dump_pre_spatial;
      repeat match goal with
      | |- context [?x - 0] => replace (x - 0) with x by lia
      end;
      auto; try lia.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_11 : zeroOneKnapsack_entail_wit_11.
Proof.
  pre_process.
  Exists (dp_l_2 ++ (prev + v) :: nil).
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (idx + 1) (dp_l_2 ++ (prev + v) :: nil)).
    cancel (IntArray.undef_seg dp_pre (idx + 1) ((n_pre + 1) * (capacity_pre + 1))).
  - prop_apply_p (IntArray.seg_Zlength dp_pre 0 (idx + 1) (dp_l_2 ++ (prev + v) :: nil)).
    Intros.
    match goal with
    | Hlen_seg : Zlength (dp_l_2 ++ (prev + v) :: nil) = _ |- _ =>
        rewrite Zlength_app_cons in Hlen_seg;
        assert (Hdp_len : Zlength dp_l_2 = idx) by lia
    end.
    assert (Hcell_new : KnapsackCellCorrect weights_l values_l i j (prev + v)).
    {
      replace i with (item + 1) by lia.
      eapply KnapsackCellCorrect_take_better with (without := without) (w := w) (v := v).
      - rewrite PreH9. lia.
      - lia.
      - exact PreH18.
      - exact PreH19.
      - lia.
      - intros k Hk. specialize (PreH40 k). lia.
      - replace item with (i - 1) by lia. exact PreH36.
      - replace item with (i - 1) by lia. exact PreH37.
      - lia.
    }
    pose proof (KnapsackCellCorrect_value_bound weights_l values_l i j (prev + v) n_pre PreH10 (conj PreH3 PreH4) PreH41 Hcell_new) as Hcell_bound.
    assert (Hrow_new : KnapsackRowProgress weights_l values_l capacity_pre (dp_l_2 ++ (prev + v) :: nil) i (j + 1)).
    {
      eapply KnapsackRowProgress_append_cell_recurrence; eauto; try lia.
    }
    split_pures; dump_pre_spatial; auto; try lia.
    + rewrite app_Znth1; [exact PreH28 |]. rewrite Hdp_len. lia.
    + rewrite app_Znth1; [exact PreH29 |]. rewrite Hdp_len. lia.
    + intros k Hk.
      rewrite Zlength_app_cons in Hk.
      destruct (Z_lt_dec k (Zlength dp_l_2)) as [Hklt | Hknlt].
      * rewrite app_Znth1 by lia. apply PreH39. lia.
      * assert (k = Zlength dp_l_2) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        replace (Zlength dp_l_2 - Zlength dp_l_2) with 0 by lia.
        rewrite Znth0_cons.
        lia.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_12 : zeroOneKnapsack_entail_wit_12.
Proof.
  pre_process.
  Exists (dp_l_2 ++ without :: nil).
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (idx + 1) (dp_l_2 ++ without :: nil)).
    cancel (IntArray.undef_seg dp_pre (idx + 1) ((n_pre + 1) * (capacity_pre + 1))).
  - prop_apply_p (IntArray.seg_Zlength dp_pre 0 (idx + 1) (dp_l_2 ++ without :: nil)).
    Intros.
    match goal with
    | Hlen_seg : Zlength (dp_l_2 ++ without :: nil) = _ |- _ =>
        rewrite Zlength_app_cons in Hlen_seg;
        assert (Hdp_len : Zlength dp_l_2 = idx) by lia
    end.
    assert (Hcell_new : KnapsackCellCorrect weights_l values_l i j without).
    {
      replace i with (item + 1) by lia.
      eapply KnapsackCellCorrect_keep_without_when_better_or_equal with (w := w) (v := v) (prev := prev).
      - rewrite PreH9. lia.
      - lia.
      - exact PreH18.
      - exact PreH19.
      - lia.
      - intros k Hk. specialize (PreH40 k). lia.
      - replace item with (i - 1) by lia. exact PreH36.
      - replace item with (i - 1) by lia. exact PreH37.
      - lia.
    }
    assert (Hrow_new : KnapsackRowProgress weights_l values_l capacity_pre (dp_l_2 ++ without :: nil) i (j + 1)).
    {
      eapply KnapsackRowProgress_append_cell_recurrence; eauto; try lia.
    }
    split_pures; dump_pre_spatial; auto; try lia.
    + rewrite app_Znth1; [exact PreH28 |]. rewrite Hdp_len. lia.
    + rewrite app_Znth1; [exact PreH29 |]. rewrite Hdp_len. lia.
    + intros k Hk.
      rewrite Zlength_app_cons in Hk.
      destruct (Z_lt_dec k (Zlength dp_l_2)) as [Hklt | Hknlt].
      * rewrite app_Znth1 by lia. apply PreH39. lia.
      * assert (k = Zlength dp_l_2) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        replace (Zlength dp_l_2 - Zlength dp_l_2) with 0 by lia.
        rewrite Znth0_cons.
        lia.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_13 : zeroOneKnapsack_entail_wit_13.
Proof.
  pre_process.
  Exists (dp_l_2 ++ without :: nil).
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (idx + 1) (dp_l_2 ++ without :: nil)).
    cancel (IntArray.undef_seg dp_pre (idx + 1) ((n_pre + 1) * (capacity_pre + 1))).
  - prop_apply_p (IntArray.seg_Zlength dp_pre 0 (idx + 1) (dp_l_2 ++ without :: nil)).
    Intros.
    match goal with
    | Hlen_seg : Zlength (dp_l_2 ++ without :: nil) = _ |- _ =>
        rewrite Zlength_app_cons in Hlen_seg;
        assert (Hdp_len : Zlength dp_l_2 = idx) by lia
    end.
    assert (Hcell_new : KnapsackCellCorrect weights_l values_l i j without).
    {
      replace i with (item + 1) by lia.
      eapply KnapsackCellCorrect_too_heavy with (w := w) (v := v).
      - rewrite PreH9. lia.
      - lia.
      - exact PreH18.
      - exact PreH19.
      - lia.
      - intros k Hk. specialize (PreH34 k). lia.
      - replace item with (i - 1) by lia. exact PreH31.
    }
    assert (Hrow_new : KnapsackRowProgress weights_l values_l capacity_pre (dp_l_2 ++ without :: nil) i (j + 1)).
    {
      eapply KnapsackRowProgress_append_cell_recurrence; eauto; try lia.
    }
    split_pures; dump_pre_spatial; auto; try lia.
    + rewrite app_Znth1; [exact PreH28 |]. rewrite Hdp_len. lia.
    + intros k Hk.
      rewrite Zlength_app_cons in Hk.
      destruct (Z_lt_dec k (Zlength dp_l_2)) as [Hklt | Hknlt].
      * rewrite app_Znth1 by lia. apply PreH33. lia.
      * assert (k = Zlength dp_l_2) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        replace (Zlength dp_l_2 - Zlength dp_l_2) with 0 by lia.
        rewrite Znth0_cons.
        lia.
Qed. 

Lemma proof_of_zeroOneKnapsack_entail_wit_15 : zeroOneKnapsack_entail_wit_15.
Proof.
  pre_process.
  Exists dp_l_2.
  replace (i * width + (j + 1)) with (idx + 1) by lia.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (idx + 1) dp_l_2).
    cancel (IntArray.undef_seg dp_pre (idx + 1) ((n_pre + 1) * (capacity_pre + 1))).
  - entailer!.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_16 : zeroOneKnapsack_entail_wit_16.
Proof.
  pre_process.
  assert (Hj_end : j = capacity_pre + 1) by lia.
  Exists dp_l_2.
  replace ((i + 1) * width) with (i * width + j) by nia.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (i * width + j) dp_l_2).
    cancel (IntArray.undef_seg dp_pre (i * width + j) ((n_pre + 1) * (capacity_pre + 1))).
  - entailer!.
    eapply KnapsackRowProgress_end_to_RowsDone with (col := j); eauto.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_17 : zeroOneKnapsack_entail_wit_17.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 ((i + 1) * width) dp_l_2).
    cancel (IntArray.undef_seg dp_pre ((i + 1) * width) ((n_pre + 1) * (capacity_pre + 1))).
  - entailer!.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_18 : zeroOneKnapsack_entail_wit_18.
Proof.
  pre_process.
  assert (Hi_done : i = n_pre + 1) by lia.
  subst i.
  Exists dp_l_2.
  split_pure_spatial.
  - rewrite PreH2.
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full
      dp_pre 0 ((n_pre + 1) * (capacity_pre + 1)) dp_l_2).
    replace (dp_pre + 0 * sizeof ( INT )) with dp_pre by lia.
    replace ((n_pre + 1) * (capacity_pre + 1) - 0)
      with ((n_pre + 1) * (capacity_pre + 1)) by lia.
    cancel (IntArray.full dp_pre ((n_pre + 1) * (capacity_pre + 1)) dp_l_2).
  - assert (Hres_idx_in :
      0 <= n_pre * width + capacity_pre < Zlength dp_l_2).
    {
      eapply (KnapsackRowsDone_index_bound
        weights_l values_l capacity_pre dp_l_2 (n_pre + 1)); eauto.
      rewrite PreH2; nia.
    }
    match goal with
    | Hbound : forall k : Z, 0 <= k < Zlength dp_l_2 ->
        0 <= Znth k dp_l_2 0 <= 4000000 |- _ =>
        pose proof (Hbound (n_pre * width + capacity_pre) Hres_idx_in)
          as Hres_value_bound
    end.
    assert (Hres_cell :
      KnapsackMaxValue weights_l values_l n_pre capacity_pre
        (Znth (n_pre * width + capacity_pre) dp_l_2 0)).
    {
      change (KnapsackCellCorrect weights_l values_l n_pre capacity_pre
        (Znth (n_pre * width + capacity_pre) dp_l_2 0)).
      replace (n_pre * width + capacity_pre)
        with (KnapsackCellIndex capacity_pre n_pre capacity_pre)
        by (unfold KnapsackCellIndex; rewrite PreH2; nia).
      eapply KnapsackRowsDone_lookup_cell; eauto; try lia.
      unfold KnapsackCellIndex; nia.
    }
    split_pures; dump_pre_spatial; auto; try lia; try nia.
Qed. 
