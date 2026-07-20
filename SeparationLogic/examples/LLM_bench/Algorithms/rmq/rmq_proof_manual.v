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
From SimpleC.EE.LLM_bench.Algorithms.rmq Require Import rmq_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib.
Local Open Scope sac.

Lemma proof_of_build_entail_wit_7 : build_entail_wit_7.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_build_safety_wit_12 : build_safety_wit_12.
Proof.
  pre_process.
  entailer!; subst len.
  - pose proof (worker_Power2_nonneg j).
    lia.
  - eapply worker_Power2_plus_n_int_bound_30; eauto.
Qed.

Lemma proof_of_build_safety_wit_26 : build_safety_wit_26.
Proof.
  pre_process.
  split_pures.
  - assert (0 < len) by (subst len; unfold Power2; apply Z.pow_pos_nonneg; lia).
    dump_pre_spatial; lia.
  - dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_safety_wit_27 : build_safety_wit_27.
Proof.
  pre_process.
  entailer!; subst len.
  - pose proof (worker_Power2_nonneg j).
    lia.
  - eapply worker_Power2_double_int_bound_30; eauto.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  pre_process.
  Exists st0.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st0).
  - split_pures.
    all: dump_pre_spatial; try lia; try nia; try assumption;
      try (unfold STZeroPrefix; repeat split; try nia; intros; lia).
Qed.

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  pre_process.
  Exists (replace_Znth idx 0 st_l_2).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) (replace_Znth idx 0 st_l_2)).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption;
      try (rewrite Zlength_replace_Znth; lia);
      try (eapply STZeroPrefix_replace_zero_step; [eassumption | rewrite PreH9; lia]).
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption;
      try (replace (n_pre * K_pre) with idx by lia; assumption).
Qed.

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption;
      try (unfold STBasePrefix; repeat split; try lia; intros; lia).
Qed.

Lemma proof_of_build_entail_wit_5 : build_entail_wit_5.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; eauto; try lia.
    nia.
Qed.

Lemma proof_of_build_entail_wit_6 : build_entail_wit_6.
Proof.
  pre_process.
  Exists (replace_Znth (i * K_pre) (Znth i l 0) st_l_2).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre)
              (replace_Znth (i * K_pre) (Znth i l 0) st_l_2)).
  - split_pures.
    all: dump_pre_spatial; eauto;
      try rewrite Zlength_replace_Znth; eauto; try lia; try nia.
    eapply worker_STBasePrefix_write_base_step; eauto; try lia; try nia.
Qed.

Lemma proof_of_build_entail_wit_8 : build_entail_wit_8.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; eauto; try lia.
    eapply worker_STBasePrefix_complete_level1; eauto; try lia.
Qed.

Lemma proof_of_build_entail_wit_9 : build_entail_wit_9.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; try solve [auto | lia | unfold Power2; simpl; lia].
Qed. 

Lemma proof_of_build_entail_wit_10 : build_entail_wit_10.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; try solve [auto | lia].
    unfold STLevelPrefix; repeat split; auto; try lia.
Qed. 

Lemma proof_of_build_entail_wit_11 : build_entail_wit_11.
Proof.
  pre_process.
  Exists st_l_2.
  assert (Hhalf_pos : 0 < half) by
    (rewrite PreH12; unfold Power2; apply Z.pow_pos_nonneg; lia).
  assert (Hlen_half : len = 2 * half) by
    (rewrite PreH13, PreH12; unfold Power2;
     replace j with (Z.succ (j - 1)) by lia;
     replace (Z.succ (j - 1) - 1) with (j - 1) by lia;
     rewrite Z.pow_succ_r by lia; ring).
  assert (Hcell_left : STCellRangeMax l st_l_2 K_pre i (j - 1)).
  {
    unfold STBuiltBeforeLevel in PreH16.
    destruct PreH16 as (_ & _ & _ & _ & _ & Hbuilt).
    apply Hbuilt; repeat split; try lia.
  }
  assert (Hcell_right : STCellRangeMax l st_l_2 K_pre (i + half) (j - 1)).
  {
    unfold STBuiltBeforeLevel in PreH16.
    destruct PreH16 as (_ & _ & _ & _ & _ & Hbuilt).
    apply Hbuilt; repeat split; try lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures.
    all: dump_pre_spatial; try solve [auto | lia | nia].
Qed. 

Lemma proof_of_build_entail_wit_12 : build_entail_wit_12.
Proof.
  pre_process.
  Exists st_l.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l).
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_build_entail_wit_13_2 : build_entail_wit_13_2.
Proof.
  pre_process.
  Exists (replace_Znth (i * K_pre + j) b st_l_2).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre)
      (replace_Znth (i * K_pre + j) b st_l_2)).
  - assert (Hidx_half_diff :
        i * K_pre + j <> (i + half) * K_pre + j - 1).
    {
      replace ((i + half) * K_pre + j - 1)
        with ((i + half) * K_pre + (j - 1)) by lia.
      apply cell_index_diff_col_neq with (K := K_pre); lia.
    }
    assert (Ha_prev : a = Znth (i * K_pre + (j - 1)) st_l_2 0).
    {
      replace (i * K_pre + (j - 1)) with (i * K_pre + j - 1) by lia.
      exact PreH22.
    }
    assert (Hb_prev : b = Znth ((i + half) * K_pre + (j - 1)) st_l_2 0).
    {
      replace ((i + half) * K_pre + (j - 1))
        with ((i + half) * K_pre + j - 1) by lia.
      exact PreH23.
    }
    split_pures; dump_pre_spatial; auto; try lia.
    + rewrite Zlength_replace_Znth; auto.
    + rewrite Znth_replace_Znth_Diff by lia.
      exact PreH22.
    + rewrite Znth_replace_Znth_Diff by lia.
      exact PreH23.
    + eapply STBuiltBeforeLevel_replace_level_cell; eauto; lia.
    + eapply STLevelPrefix_extend_by_right_max; eauto; lia.
Qed. 

Lemma proof_of_build_entail_wit_13_1 : build_entail_wit_13_1.
Proof.
  pre_process.
  Exists (replace_Znth (i * K_pre + j) a st_l_2).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre)
      (replace_Znth (i * K_pre + j) a st_l_2)).
  - assert (Hidx_half_diff :
        i * K_pre + j <> (i + half) * K_pre + j - 1).
    {
      replace ((i + half) * K_pre + j - 1)
        with ((i + half) * K_pre + (j - 1)) by lia.
      apply cell_index_diff_col_neq with (K := K_pre); lia.
    }
    assert (Ha_prev : a = Znth (i * K_pre + (j - 1)) st_l_2 0).
    {
      replace (i * K_pre + (j - 1)) with (i * K_pre + j - 1) by lia.
      exact PreH22.
    }
    assert (Hb_prev : b = Znth ((i + half) * K_pre + (j - 1)) st_l_2 0).
    {
      replace ((i + half) * K_pre + (j - 1))
        with ((i + half) * K_pre + j - 1) by lia.
      exact PreH23.
    }
    split_pures; dump_pre_spatial; auto; try lia.
    + rewrite Zlength_replace_Znth; auto.
    + rewrite Znth_replace_Znth_Diff by lia.
      exact PreH22.
    + rewrite Znth_replace_Znth_Diff by lia.
      exact PreH23.
    + eapply STBuiltBeforeLevel_replace_level_cell; eauto; lia.
    + eapply STLevelPrefix_extend_by_left_max; eauto; lia.
Qed. 

Lemma proof_of_build_entail_wit_14 : build_entail_wit_14.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
    cancel (IntArray.full st_pre (n_pre * K_pre) st_l_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    pose proof (Power2_pos j ltac:(lia)).
    subst len; lia.
Qed. 

Lemma proof_of_build_entail_wit_15 : build_entail_wit_15.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    eapply STLevelPrefix_exit_to_built_step; eauto.
Qed.

Lemma proof_of_build_entail_wit_16 : build_entail_wit_16.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    + rewrite PreH12.
      apply Power2_step; lia.
    + rewrite PreH12.
      f_equal; lia.
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  pre_process.
  Exists st_l_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold STBuilt.
    assert (j = K_pre) by lia.
    subst j.
    exact PreH14.
Qed.

Lemma proof_of_query_safety_wit_6 : query_safety_wit_6.
Proof.
  pre_process.
  apply _derivable1_andp_intros.
  all: apply derivable1s_coq_prop_r.
  all:
    match goal with
    | Hloop : QueryLogLoopState _ _ _ _ _ |- _ =>
        unfold QueryLogLoopState in Hloop;
        destruct Hloop as
          (Hlen_pos & Hlen_le & HK_pos & Hn_pow &
           Hk_nonneg & Hk_lt & Hpow & Hpow_len);
        subst pow;
        unfold Power2 in *;
        pose proof (Z.pow_nonneg 2 k ltac:(lia));
        lia
    end.
Qed.

Lemma proof_of_query_safety_wit_8 : query_safety_wit_8.
Proof.
  pre_process.
  apply _derivable1_andp_intros.
  all: apply derivable1s_coq_prop_r.
  all:
    match goal with
    | Hloop : QueryLogLoopState _ _ _ _ _ |- _ =>
        unfold QueryLogLoopState in Hloop;
        destruct Hloop as
          (Hlen_pos & Hlen_le & HK_pos & Hn_pow &
           Hk_nonneg & Hk_lt & Hpow & Hpow_len);
        subst pow;
        unfold Power2 in *;
        pose proof (Z.pow_nonneg 2 k ltac:(lia));
        lia
    end.
Qed.

Lemma proof_of_query_safety_wit_10 : query_safety_wit_10.
Proof.
  pre_process.
  apply _derivable1_andp_intros.
  all: apply derivable1s_coq_prop_r.
  all:
    match goal with
    | Hloop : QueryLogLoopState _ _ _ _ _ |- _ =>
        unfold QueryLogLoopState in Hloop;
        destruct Hloop as
          (Hlen_pos & Hlen_le & HK_pos & Hn_pow &
           Hk_nonneg & Hk_lt & Hpow & Hpow_len);
        lia
    end.
Qed.

Lemma proof_of_query_entail_wit_1 : query_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; (dump_pre_spatial; try lia; eauto using QueryLogLoopState_init).
Qed.

Lemma proof_of_query_entail_wit_2 : query_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; (dump_pre_spatial; try lia; eauto using QueryLogLoopState_step).
Qed.

Lemma proof_of_query_entail_wit_3 : query_entail_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full st_pre (n_pre * K_pre) st_l).
  - split_pures.
    all: dump_pre_spatial; try solve [auto | lia].
    all: try solve
      [ unfold QueryLogFinalState; split; [exact PreH15|];
        unfold QueryLogLoopState in PreH15;
        destruct PreH15 as (_ & _ & _ & _ & Hk_nonneg & _ & Hpow & _);
        unfold Power2 in *;
        replace (k + 1) with (Z.succ k) by lia;
        rewrite Z.pow_succ_r by lia;
        rewrite <- Hpow; lia
      | unfold QueryLogLoopState in PreH15; intuition nia
      | unfold STBuilt, STBuiltBeforeLevel in PreH14;
        destruct PreH14 as (_ & _ & _ & _ & _ & Hbuilt);
        apply Hbuilt;
        unfold QueryLogLoopState in PreH15; intuition nia ].
Qed. 

Lemma proof_of_query_entail_wit_5 : query_entail_wit_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full st_pre (n_pre * K_pre) st_l).
  - split_pures; dump_pre_spatial; eauto using RangeMaxValue_sparse_query_left.
Qed.

Lemma proof_of_query_entail_wit_6 : query_entail_wit_6.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full st_pre (n_pre * K_pre) st_l).
  - split_pures; dump_pre_spatial; eauto using RangeMaxValue_sparse_query_right.
Qed.
