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
From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_goal.
From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib.
Local Open Scope sac.

Lemma proof_of_initCounts_entail_wit_1_split_goal_1 : initCounts_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_1_split_goal_2 : initCounts_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) (@nil Z).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg seen_pre k_pre).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg good_pre k_pre).
  rewrite (IntArray.seg_empty seen_pre 0 0).
  rewrite (IntArray.seg_empty good_pre 0 0).
  split_pure_spatial.
  - cancel (IntArray.undef_seg seen_pre 0 k_pre).
    cancel (IntArray.undef_seg good_pre 0 k_pre).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. apply CountsZeroPrefix_nil.
    + dump_pre_spatial. apply CountsZeroPrefix_nil.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_initCounts_entail_wit_2_split_goal_1 : initCounts_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_2_split_goal_2 : initCounts_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Proof.
  pre_process.
  Exists (good_l_2 ++ 0 :: nil) (seen_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.seg seen_pre 0 (i + 1) (seen_l_2 ++ 0 :: nil)).
    cancel (IntArray.undef_seg seen_pre (i + 1) k_pre).
    cancel (IntArray.seg good_pre 0 (i + 1) (good_l_2 ++ 0 :: nil)).
    cancel (IntArray.undef_seg good_pre (i + 1) k_pre).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. apply CountsZeroPrefix_snoc_zero; auto.
    + dump_pre_spatial. apply CountsZeroPrefix_snoc_zero; auto.
Qed.

Lemma proof_of_initCounts_return_wit_1 : initCounts_return_wit_1.
Proof.
  pre_process.
  Exists good_l_2 seen_l_2.
  assert (Hi : i = k_pre) by lia.
  subst i.
  repeat rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full seen_pre 0 k_pre seen_l_2).
  replace (seen_pre + 0 * sizeof ( INT )) with seen_pre by lia.
  replace (k_pre - 0) with k_pre by lia.
  sep_apply (IntArray.seg_to_full good_pre 0 k_pre good_l_2).
  replace (good_pre + 0 * sizeof ( INT )) with good_pre by lia.
  replace (k_pre - 0) with k_pre by lia.
  split_pure_spatial.
  - cancel (IntArray.full seen_pre k_pre seen_l_2).
    cancel (IntArray.full good_pre k_pre good_l_2).
  - split_pures; dump_pre_spatial.
    + apply CountsZeroPrefix_to_full. exact PreH6.
    + apply CountsZeroPrefix_to_full. exact PreH7.
Qed.

Lemma proof_of_copyCounts_entail_wit_1_split_goal_1 : copyCounts_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Proof.
  pre_process.
  Exists good_old.
  split_pure_spatial.
  - cancel (IntArray.full seen_pre k_pre seen_l).
    cancel (IntArray.full good_pre k_pre good_old).
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try (apply CopyCountsPrefix_zero; assumption);
      try (intros idx Hidx; apply PreH6; lia).
Qed.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_1 : copyCounts_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_2 : copyCounts_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
Proof.
  pre_process.
  pose proof PreH8 as Hcopy_prefix.
  destruct PreH8 as (_ & _ & _ & Hgood_len & _ & _).
  Exists (replace_Znth i (Znth i seen_l 0) good_cur_2).
  split_pure_spatial.
  - cancel (IntArray.full good_pre k_pre
              (replace_Znth i (Znth i seen_l 0) good_cur_2)).
    cancel (IntArray.full seen_pre k_pre seen_l).
  - split_pures; dump_pre_spatial; try lia; try assumption;
      try (eapply CopyCountsPrefix_step_replace; [exact Hcopy_prefix | lia]);
      try (intros idx Hidx; apply PreH9; lia);
      try (intros idx Hidx;
           eapply replace_Znth_preserves_bounds
             with (xs := good_cur_2) (i := i) (v := Znth i seen_l 0)
                  (k := k_pre) (lo := 0) (hi := 200000);
           [ exact Hgood_len
           | lia
           | apply PreH9; lia
           | intros idx0 Hidx0; apply PreH10; lia
           | exact Hidx ]).
Qed.

Lemma proof_of_copyCounts_return_wit_1_split_goal_1 : copyCounts_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1.
Proof.
  pre_process.
  pose proof (CopyCountsPrefix_full_eq seen_l good_old good_cur i k_pre
                PreH8 PreH1 PreH7) as Hgood.
  subst good_cur.
  split_pure_spatial.
  - cancel (IntArray.full seen_pre k_pre seen_l).
    cancel (IntArray.full good_pre k_pre seen_l).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1.
Proof.
  pre_process.
  Exists good_l_2; Exists seen_l_2; Exists ans_2.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre seen_l_2).
    cancel (IntArray.full good_pre k_pre good_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    eapply CountsZeroFull_to_ChoosingPrefixState_zero; eauto; lia.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2.
Proof.
  pre_process.
  subst answer.
  Exists seen_l_2; Exists good_l_2; Exists ans_2.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre seen_l_2).
    cancel (IntArray.full good_pre k_pre good_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    all: try (intros idx Hidx; eapply CountsZeroFull_bounds_zero; eauto; lia).
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3.
Proof.
  pre_process.
  Exists ans_2; Exists good_l_2; Exists seen_l_2.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre seen_l_2).
    cancel (IntArray.full good_pre k_pre good_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try reflexivity; try assumption.
    all: try (pose proof (PreH16 i ltac:(lia)) as Hcolor_i; lia).
    all: try (pose proof (PreH17 i ltac:(lia)) as Hcost_i; lia).
    all: try (pose proof (PreH16 i ltac:(lia)) as Hcolor_i;
              pose proof (PreH18 (Znth i colors_l 0) ltac:(lia)) as Hseen_i; lia).
    all: try (pose proof (PreH16 i ltac:(lia)) as Hcolor_i;
              pose proof (PreH19 (Znth i colors_l 0) ltac:(lia)) as Hgood_i; lia).
    all: try (intros idx Hidx; apply PreH16; lia).
    all: try (intros idx Hidx; apply PreH17; lia).
    all: try (intros idx Hidx; apply PreH18; lia).
    all: try (intros idx Hidx; apply PreH19; lia).
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4.
Proof.
  pre_process.
  pose proof PreH28 as Hstate.
  unfold ChoosingPrefixState in Hstate.
  destruct Hstate as
    [Hlimit [Hcosts_len [Hseen_len [Hgood_len
      [Hanswer_eq [Hseen_count Hgood_count]]]]]].
  pose (seen_next := replace_Znth c (Znth c seen_l 0 + 1) seen_l).
  assert (Hnext_state :
    ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c seen_l 0) seen_next seen_next).
  {
    subst seen_next.
    eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer) (good := good_l_2) (c := c);
      try exact PreH28; try exact PreH2; try reflexivity; try lia.
  }
  Exists good_l_2; Exists ans_2; Exists seen_l; Exists seen_next.
  subst seen_next.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre
              (replace_Znth c (Znth c seen_l 0 + 1) seen_l)).
    cancel (IntArray.full good_pre k_pre good_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try reflexivity; try assumption.
    + rewrite Zlength_replace_Znth. exact Hseen_len.
    + pose proof
        (ChoosingPrefixState_answer_bound colors_l costs_l (i + 1) k_pre
           p_pre (answer + Znth c seen_l 0)
           (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (replace_Znth c (Znth c seen_l 0 + 1) seen_l) n_pre
           Hnext_state ltac:(lia) PreH5) as Hbound.
      lia.
    + replace (answer + Znth c seen_l 0 - Znth c seen_l 0)
        with answer by lia.
      exact PreH28.
    + intros idx Hidx.
      destruct (Z.eq_dec idx c) as [Heq | Hneq].
      * subst idx.
        rewrite Znth_replace_Znth_Same by (rewrite Hseen_len; lia).
        assert (Hc_idx : 0 <= c < k_pre) by lia.
        destruct (PreH31 c Hc_idx) as [Hc_seen_lo Hc_seen_hi].
        split; lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hseen_len; lia).
        destruct (PreH31 idx Hidx) as [Hseen_idx_lo Hseen_idx_hi].
        split; lia.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5.
Proof.
  pre_process.
  Exists ans_2; Exists seen_next_2.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre seen_next_2).
    cancel (IntArray.full good_pre k_pre seen_next_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try reflexivity; try assumption.
    + eapply ChoosingPrefixState_step_affordable_after_copy
        with (old_answer := answer - Znth c seen_l 0)
             (seen := seen_l) (good := good_l) (c := c);
        try exact PreH23; try exact PreH2; try exact PreH21;
        try reflexivity; try lia.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6.
Proof.
  pre_process.
  pose proof PreH28 as Hstate.
  unfold ChoosingPrefixState in Hstate.
  destruct Hstate as
    [Hlimit [Hcosts_len [Hseen_len [Hgood_len
      [Hanswer_eq [Hseen_count Hgood_count]]]]]].
  pose (seen_next := replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2).
  assert (Hnext_state :
    ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c good_l 0) seen_next good_l).
  {
    subst seen_next.
    eapply ChoosingPrefixState_step_expensive
      with (old_answer := answer) (c := c);
      try exact PreH28; try exact PreH2; try reflexivity; try lia.
  }
  Exists ans_2; Exists seen_l_2; Exists good_l; Exists seen_next.
  subst seen_next.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre
              (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2)).
    cancel (IntArray.full good_pre k_pre good_l).
  - split_pures.
    all: dump_pre_spatial; try lia; try reflexivity; try assumption.
    + rewrite Zlength_replace_Znth. exact Hseen_len.
    + pose proof
        (ChoosingPrefixState_answer_bound colors_l costs_l (i + 1) k_pre
           p_pre (answer + Znth c good_l 0)
           (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2)
           good_l n_pre Hnext_state ltac:(lia) PreH5) as Hbound.
      lia.
    + replace (answer + Znth c good_l 0 - Znth c good_l 0)
        with answer by lia.
      exact PreH28.
    + intros idx Hidx.
      destruct (Z.eq_dec idx c) as [Heq | Hneq].
      * subst idx.
        rewrite Znth_replace_Znth_Same by (rewrite Hseen_len; lia).
        assert (Hc_idx : 0 <= c < k_pre) by lia.
        destruct (PreH31 c Hc_idx) as [Hc_seen_lo Hc_seen_hi].
        split; lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hseen_len; lia).
        destruct (PreH31 idx Hidx) as [Hseen_idx_lo Hseen_idx_hi].
        split; lia.
    + intros idx Hidx.
      destruct (PreH32 idx Hidx) as [Hgood_idx_lo Hgood_idx_hi].
      split; lia.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_8_split_goal_1 : countChoosingInns_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8.
Proof.
  pre_process.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  Exists good_l_2; Exists seen_l_2.
  split_pure_spatial.
  - cancel (IntArray.full colors_pre n_pre colors_l).
    cancel (IntArray.full costs_pre n_pre costs_l).
    cancel (IntArray.full seen_pre k_pre seen_l_2).
    cancel (IntArray.full good_pre k_pre good_l_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    eapply ChoosingPrefixState_to_ChoosingInnsAnswer_full; eauto; lia.
Qed. 

Lemma proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1 : countChoosingInns_partial_solve_wit_7_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure.
Proof.
  pre_process.
  assert (Hgood_len : Zlength good_l = k_pre).
  {
    unfold ChoosingPrefixState in PreH22.
    tauto.
  }
  split_pures.
  all: dump_pre_spatial; try lia; try assumption.
  - intros idx Hidx.
    pose proof (PreH25 idx Hidx) as Hseen_bound.
    lia.
  - intros idx Hidx.
    pose proof (PreH26 idx Hidx) as Hgood_bound.
    lia.
Qed. 
