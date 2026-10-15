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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P049_1946C_tree_cutting_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P049_1946C_tree_cutting_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P049_1946C_tree_cutting_lib.
Local Open Scope sac.

Lemma proof_of_feasible_safety_wit_12_split_goal_1 : feasible_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Pre in PreH13.
  destruct PreH13 as [_ [Hnmax _]].
  pose proof (PreH16 oi ltac:(lia)) as [[[Hvertex_nonneg Hvertex_lt] _] _].
  pose proof (PreH16 (Znth oi order_data 0) ltac:(lia))
    as [[[_ _] Hparent_nonneg] Hparent_lt].
  rewrite Znth_replace_Znth_Same by lia.
  destruct (Z.eq_dec
    (Znth (Znth oi order_data 0) parent_data 0)
    (Znth oi order_data 0)) as [Heq | Hneq].
  - rewrite Heq.
    rewrite Znth_replace_Znth_Same by lia.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    pose proof
      (PreH11 (Znth (Znth oi order_data 0) parent_data 0) ltac:(lia))
      as [_ Hsize_upper].
    lia.
Qed.

Lemma proof_of_feasible_safety_wit_12_split_goal_2 : feasible_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH16 oi ltac:(lia)) as [[[Hvertex_nonneg Hvertex_lt] _] _].
  pose proof (PreH16 (Znth oi order_data 0) ltac:(lia))
    as [[[_ _] Hparent_nonneg] Hparent_lt].
  rewrite Znth_replace_Znth_Same by lia.
  destruct (Z.eq_dec
    (Znth (Znth oi order_data 0) parent_data 0)
    (Znth oi order_data 0)) as [Heq | Hneq].
  - rewrite Heq.
    rewrite Znth_replace_Znth_Same by lia.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    pose proof
      (PreH11 (Znth (Znth oi order_data 0) parent_data 0) ltac:(lia))
      as [Hsize_nonneg _].
    lia.
Qed.

Lemma proof_of_feasible_safety_wit_12 : feasible_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_feasible_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_feasible_safety_wit_18_split_goal_1 : feasible_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Pre in PreH11.
  lia.
Qed.

Lemma proof_of_feasible_safety_wit_18_split_goal_2 : feasible_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Pre in PreH11.
  lia.
Qed.

Lemma proof_of_feasible_safety_wit_18 : feasible_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_feasible_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_1_split_goal_1 : feasible_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros; auto.
Qed.

Lemma proof_of_feasible_entail_wit_1_split_goal_2 : feasible_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SizeInitializationState.
  repeat split; simpl; intros; lia.
Qed.

Lemma proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_2_split_goal_1 : feasible_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  eapply size_initialization_step__feasible_size_init; eauto.
Qed.

Lemma proof_of_feasible_entail_wit_2 : feasible_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_3 : feasible_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (size_initialization_complete__feasible_size_init
      nv i initialized PreH4 PreH1) as Hinitialized.
  destruct Hinitialized as [Hi [Hlength Hones]].
  subst i.
  Exists initialized.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full size_p 0 nv initialized).
    replace (size_p + 0 * sizeof (INT)) with size_p by lia.
    replace (nv - 0) with nv by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Hlength.
    + dump_pre_spatial. intros j Hj. rewrite Hones by lia. lia.
    + dump_pre_spatial.
      intros [Hcursor Hparent].
      assert (Hn : 2 <= nv).
      { unfold Pre in PreH5. intuition lia. }
      pose proof (PreH8 (nv - 1) ltac:(lia)) as Hcursor_bounds.
      destruct Hcursor_bounds as [[[Hvertex_lo Hvertex_hi] _] _].
      pose proof
        (PreH8 (Znth (nv - 1) order_data 0) ltac:(lia))
        as Hvertex_bounds.
      destruct Hvertex_bounds as [[_ _] Hparent_hi].
      rewrite Hones by lia.
      rewrite Hones by lia.
      lia.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial.
      eapply cut_scan_state_initial__feasible_size_init.
      * exact PreH5.
      * exact PreH7.
      * exact PreH8.
      * split; assumption.
      * exact Hlength.
      * exact Hones.
Qed.

Lemma proof_of_feasible_entail_wit_4_1_split_goal_1 : feasible_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17 |- *.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  split; [lia |].
  split; [lia |].
  split; [exact Hparentlen |].
  split; [exact Horderlen |].
  split; [exact Hrooted |].
  split; [exact Hnext_node |].
  exists final_components, final_sizes.
  split; [exact Htail |].
  split; [exact Hfinal_components |].
  split; [exact Hfinal_len |].
  split; [exact Hfinal_bounds |].
  exact Hthreshold.
Qed.

Lemma proof_of_feasible_entail_wit_4_1_split_goal_2 : feasible_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  destruct Hnext_node as [Hnext_len [Hnext_bounds Hnext_addition]].
  pose proof (PreH16 (oi - 1) ltac:(lia)) as Hnext_info.
  destruct Hnext_info as [[Hnext_vertex _] _].
  assert (Hnext_parent_default :
      Znth (Znth (oi - 1) order_data 0) parent_data (-1) =
      Znth (Znth (oi - 1) order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hnext_vertex. }
  rewrite Hnext_parent_default in Hnext_addition.
  apply Hnext_addition; lia.
Qed.

Lemma proof_of_feasible_entail_wit_4_1_split_goal_3 : feasible_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  exact (proj1 Hnext_node).
Qed.

Lemma proof_of_feasible_entail_wit_4_1 : feasible_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_4_2_split_goal_1 : feasible_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17 |- *.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  split; [lia |].
  split; [lia |].
  split; [exact Hparentlen |].
  split; [exact Horderlen |].
  split; [exact Hrooted |].
  split; [exact Hnext_node |].
  exists final_components, final_sizes.
  split; [exact Htail |].
  split; [exact Hfinal_components |].
  split; [exact Hfinal_len |].
  split; [exact Hfinal_bounds |].
  exact Hthreshold.
Qed.

Lemma proof_of_feasible_entail_wit_4_2_split_goal_2 : feasible_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  destruct Hnext_node as [Hnext_len [Hnext_bounds Hnext_addition]].
  pose proof (PreH16 (oi - 1) ltac:(lia)) as Hnext_info.
  destruct Hnext_info as [[Hnext_vertex _] _].
  assert (Hnext_parent_default :
      Znth (Znth (oi - 1) order_data 0) parent_data (-1) =
      Znth (Znth (oi - 1) order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hnext_vertex. }
  rewrite Hnext_parent_default in Hnext_addition.
  apply Hnext_addition; lia.
Qed.

Lemma proof_of_feasible_entail_wit_4_2_split_goal_3 : feasible_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  exact (proj1 Hnext_node).
Qed.

Lemma proof_of_feasible_entail_wit_4_2 : feasible_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_4_3_split_goal_1 : feasible_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17 |- *.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  split; [lia |].
  split; [lia |].
  split; [exact Hparentlen |].
  split; [exact Horderlen |].
  split; [exact Hrooted |].
  split; [exact Hnext_node |].
  exists final_components, final_sizes.
  split; [exact Htail |].
  split; [exact Hfinal_components |].
  split; [exact Hfinal_len |].
  split; [exact Hfinal_bounds |].
  exact Hthreshold.
Qed.

Lemma proof_of_feasible_entail_wit_4_3_split_goal_2 : feasible_entail_wit_4_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  destruct Hnext_node as [Hnext_len [Hnext_bounds Hnext_addition]].
  pose proof (PreH16 (oi - 1) ltac:(lia)) as Hnext_info.
  destruct Hnext_info as [[Hnext_vertex _] _].
  assert (Hnext_parent_default :
      Znth (Znth (oi - 1) order_data 0) parent_data (-1) =
      Znth (Znth (oi - 1) order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hnext_vertex. }
  rewrite Hnext_parent_default in Hnext_addition.
  apply Hnext_addition; lia.
Qed.

Lemma proof_of_feasible_entail_wit_4_3_split_goal_3 : feasible_entail_wit_4_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  exact (proj1 Hnext_node).
Qed.

Lemma proof_of_feasible_entail_wit_4_3 : feasible_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_4_3_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_4_3_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_4_3_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_4_4_split_goal_1 : feasible_entail_wit_4_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17 |- *.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  split; [lia |].
  split; [lia |].
  split; [exact Hparentlen |].
  split; [exact Horderlen |].
  split; [exact Hrooted |].
  split; [exact Hnext_node |].
  exists final_components, final_sizes.
  split; [exact Htail |].
  split; [exact Hfinal_components |].
  split; [exact Hfinal_len |].
  split; [exact Hfinal_bounds |].
  exact Hthreshold.
Qed.

Lemma proof_of_feasible_entail_wit_4_4_split_goal_2 : feasible_entail_wit_4_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CutScanState in PreH17.
  destruct PreH17 as
    [Hcursor [Hcomponents [Hparentlen [Horderlen [Hrooted
     [Hnode Hcontinuation]]]]]].
  destruct Hcontinuation as
    [final_components [final_sizes
     [Hscan [Hfinal_components [Hfinal_len [Hfinal_bounds Hthreshold]]]]]].
  pose proof (PreH16 oi ltac:(lia)) as Hcurrent.
  destruct Hcurrent as [[Hvertex _] _].
  assert (Hparent_default :
      Znth (Znth oi order_data 0) parent_data (-1) =
      Znth (Znth oi order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hvertex. }
  inversion Hscan as
    [components0 sizes0 Hdone
    | cursor0 components0 sizes0 next_components next_sizes
      final_components0 final_sizes0 Hcursor0 Hnode0 Hstep Htail];
    subst; try lia.
  unfold CutScanStep in Hstep.
  rewrite Hparent_default in Hstep.
  destruct Hstep as [cut_sizes [Hcut [Hprop Hnext_node]]].
  destruct Hcut as
    [[Hge [Hnext_components Hcut_sizes]]
    | [Hlt [Hnext_components Hcut_sizes]]]; try lia.
  destruct Hprop as
    [[Hparent Hnext_sizes] | [Hroot Hnext_sizes]]; try lia.
  subst cut_sizes next_components next_sizes.
  unfold CutScanNodeBounds in Hnext_node.
  destruct Hnext_node as [Hnext_len [Hnext_bounds Hnext_addition]].
  pose proof (PreH16 (oi - 1) ltac:(lia)) as Hnext_info.
  destruct Hnext_info as [[Hnext_vertex _] _].
  assert (Hnext_parent_default :
      Znth (Znth (oi - 1) order_data 0) parent_data (-1) =
      Znth (Znth (oi - 1) order_data 0) parent_data 0).
  { apply Znth_indep. rewrite Hparentlen. exact Hnext_vertex. }
  rewrite Hnext_parent_default in Hnext_addition.
  apply Hnext_addition; lia.
Qed.

Lemma proof_of_feasible_entail_wit_4_4 : feasible_entail_wit_4_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_4_4_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_4_4_split_goal_2.
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_1 : feasible_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_2 : feasible_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (cut_scan_terminal_threshold__feasible_returns
      nv kv edges minimum_pre oi components parent_data order_data sizes
      PreH2 PreH16) as Hterminal.
  split.
  - lia.
  - intro Hfeasible.
    apply Hterminal in Hfeasible.
    lia.
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_spatial : feasible_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_to_undef_full size_p nv sizes).
  cancel.
Qed.

Lemma proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_feasible_return_wit_1_split_goal_1.
  - Goal_apply proof_of_feasible_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_feasible_return_wit_2_split_goal_1 : feasible_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_return_wit_2_split_goal_2 : feasible_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (cut_scan_terminal_threshold__feasible_returns
      nv kv edges minimum_pre oi components parent_data order_data sizes
      PreH2 PreH16) as Hterminal.
  split.
  - intros _.
    apply Hterminal.
    exact PreH1.
  - lia.
Qed.

Lemma proof_of_feasible_return_wit_2_split_goal_spatial : feasible_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_to_undef_full size_p nv sizes).
  cancel.
Qed.

Lemma proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_feasible_return_wit_2_split_goal_1.
  - Goal_apply proof_of_feasible_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_32_split_goal_1 : solver_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_32_split_goal_2 : solver_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_32_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_37_split_goal_1 : solver_safety_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH15.
  destruct PreH15 as [_ [Hn _]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_37_split_goal_2 : solver_safety_wit_37_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_37_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_37_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_1 : solver_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH19.
  destruct PreH19 as [_ [Hn _]].
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hmid : (lo + hi) / 2 <= nv) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_39_split_goal_2 : solver_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hmid : 1 <= (lo + hi) / 2) by
    (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_41_split_goal_1 : solver_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH19.
  destruct PreH19 as [_ [Hn _]].
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hmid : (lo + hi) / 2 <= nv) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_41_split_goal_2 : solver_safety_wit_41_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hmid : 1 <= (lo + hi) / 2) by
    (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_41_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros m Hm j Hj.
  pose proof (PreH8 j ltac:(lia)) as [[Hfu1 Hfun] [Hfv1 Hfvn]].
  pose proof (PreH14 j ltac:(lia)) as [Heu Hev].
  repeat split; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof. LLM_pre_process ltac:(lia || nia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof. LLM_pre_process ltac:(lia || nia || int_auto). Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst nn_pre. rewrite <- PreH7. cancel.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval nv).
  cancel.
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
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = nv) by lia. subst i.
  assert (Hbuild : AdjacencyBuildState nv edges 0 head_init (@nil Z) (@nil Z)).
  { apply (adjacency_build_empty__solver_adjacency_build nv edges head_init).
    - lia.
    - exact H.
    - intros u Hu.
      rewrite <- (Znth_indep head_init u 0 (-1)) by lia.
      apply PreH9. lia. }
  assert (Hfresh : CurrentEdgeFresh edges 0).
  { pose proof PreH5 as Hpre. unfold Pre in Hpre.
    destruct Hpre as [_ [_ [_ [_ [_ [_ [Hfresh _]]]]]]].
    exact (Hfresh 0). }
  Exists next_p_2 to_p_2 head_p_2 (@nil Z) (@nil Z) head_init.
  split_pure_spatial.
  - rewrite H.
    rewrite (IntArray.undef_seg_empty head_p_2 nv).
    sep_apply_l_atomic (IntArray.seg_to_full head_p_2 0 nv head_init).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg to_p_2 (2 * nv - 2)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg next_p_2 (2 * nv - 2)).
    rewrite (IntArray.seg_empty to_p_2 0 0).
    rewrite (IntArray.seg_empty next_p_2 0 0).
    replace (head_p_2 + 0 * sizeof(INT)) with head_p_2 by ring.
    replace (nv - 0) with nv by lia.
    asrt_simpl. cancel.
    apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. lia.
    + apply _derivable1_andp_intros.
      * apply derivable1s_coq_prop_r. lia.
      * cancel.
  - split_pures.
    all: dump_pre_spatial; try rewrite Zlength_nil; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH5.
  destruct PreH5 as [_ [_ [_ [_ [_ [_ [Hfresh _]]]]]]].
  apply Hfresh.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH14 i ltac:(lia)).
  destruct PreH14 as [[[[Hu Hev0] Hv] Heu] Hev].
  repeat rewrite <- app_assoc.
  change (AdjacencyBuildState nv edges (i + 1)
    (replace_Znth (Znth i ev_data 0) (2 * i + 1)
      (replace_Znth (Znth i eu_data 0) (2 * i) head_data_2))
    (to_done_2 ++ Znth i ev_data 0 :: Znth i eu_data 0 :: nil)
    (next_done_2 ++ Znth (Znth i eu_data 0) head_data_2 0 ::
      Znth (Znth i ev_data 0)
        (replace_Znth (Znth i eu_data 0) (2 * i) head_data_2) 0 :: nil)).
  rewrite (Znth_indep head_data_2 (Znth i eu_data 0) 0 (-1)) by lia.
  rewrite (Znth_indep
    (replace_Znth (Znth i eu_data 0) (2 * i) head_data_2)
    (Znth i ev_data 0) 0 (-1)) by
    (rewrite Zlength_replace_Znth__solver_adjacency_build; lia).
  pose proof PreH5 as Hpre.
  unfold Pre in Hpre. destruct Hpre as [_ [_ [Hedges _]]].
  assert (Hindex : 0 <= i < Zlength edges) by lia.
  apply (adjacency_build_extend__solver_adjacency_build
    nv edges i head_data_2 to_done_2 next_done_2
    (Znth i eu_data 0) (Znth i ev_data 0) __default__Prod_Z_Z);
    try assumption; try lia.
  destruct (Znth i edges __default__Prod_Z_Z) as [a b] eqn:Hedge.
  simpl in Heu, Hev. f_equal; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
  rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
  rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_replace_Znth__solver_adjacency_build.
  exact PreH9.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = nv - 1) by lia. subst i.
  assert (ec = 2 * nv - 2) by lia. subst ec.
  replace (2 * (nv - 1)) with (2 * nv - 2) in * by ring.
  assert (Hedges : Zlength edges = nv - 1).
  { pose proof PreH5 as Hpre. unfold Pre in Hpre.
    destruct Hpre as [_ [_ [Hedges _]]]. exact Hedges. }
  assert (Hmodel : AdjacencyModel nv edges head_data_2 to_done next_done).
  { apply (adjacency_build_complete__solver_adjacency_build
      nv edges head_data_2 to_done next_done); assumption. }
  Exists next_p_2 to_p_2 head_p_2 head_data_2 to_done next_done.
  split_pure_spatial.
  - rewrite (IntArray.undef_seg_empty to_p_2 (2 * nv - 2)).
    rewrite (IntArray.undef_seg_empty next_p_2 (2 * nv - 2)).
    sep_apply_l_atomic (IntArray.seg_to_full to_p_2 0 (2 * nv - 2) to_done).
    sep_apply_l_atomic (IntArray.seg_to_full next_p_2 0 (2 * nv - 2) next_done).
    replace (to_p_2 + 0 * sizeof(INT)) with to_p_2 by ring.
    replace (next_p_2 + 0 * sizeof(INT)) with next_p_2 by ring.
    replace (2 * nv - 2 - 0) with (2 * nv - 2) by lia.
    asrt_simpl. cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists retval_3 retval_2 retval next_p_2 to_p_2 head_p_2
    (Some (-1) :: repeat None (Z.to_nat (nv - 1)))
    (0 :: nil) next_data_2 to_data_2 head_data_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.undef_seg_to_mixed_seg retval 1 nv).
    sep_apply_l_atomic
      (IntArray.mixed_full_to_undef_full retval_3 nv cells).
    rewrite (IntArray.mixed_full_unfold retval nv
      (repeat None (Z.to_nat (nv - 1))) (Some (-1))).
    rewrite (IntArray.seg_unfold retval_2 0 1 nil 0).
    IntArray.ArraySimplify.
    repeat cancel.
    unfold IntArray.mixedstoreA.
    split_pure_spatial.
    + repeat cancel.
    + split_pures. dump_pre_spatial. lia.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_cons, Zlength_correct, repeat_length. lia.
    + intros q Hq.
      assert (q = 0) by lia. subst q.
      rewrite !Znth0_cons.
      split; [split; lia |].
      exists (-1). repeat split; lia.
    + intros q Hq.
      unfold AdjacencyModel in PreH11.
      destruct PreH11 as
        [_ [_ [_ [_ [_ [Hslots _]]]]]].
      specialize (Hslots q Hq).
      rewrite (Znth_indep next_data_2 q 0 (-1)) by lia.
      destruct Hslots as [Hto [Hminus | Hnext]].
      * repeat split; try tauto; lia.
      * repeat split; try tauto; lia.
    + unfold Pre in PreH10. tauto.
    + exact (root_traversal_entry__solver_traversal_init
        nv kv edges PreH10).
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH12 as Hall_vertices.
  specialize (PreH12 i ltac:(lia)).
  destruct PreH12 as [Hvertex [parent_v [[Hparent Hparent_low] Hparent_high]]].
  assert (Hparent_none :
      Znth (Znth i order_data 0) parent_cells_2 None = Some parent_v).
  { rewrite (Znth_indep parent_cells_2 (Znth i order_data 0)
      None __default__App_option_Z) by lia.
    exact Hparent. }
  Exists size_p_2 order_p_2 parent_p_2 next_p_2 to_p_2 head_p_2
    next_data_2 to_data_2 head_data_2 parent_cells_2 parent_v order_data.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.mixed_full_split_to_mixed_missing_i
        parent_p_2 (Znth i order_data 0) nv parent_cells_2 None
        ltac:(lia)).
    rewrite Hparent_none.
    unfold IntArray.mixedstoreA.
    replace (i - 0) with i by lia.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    all: replace (i - 0) with i by lia.
    all: try tauto; try exact Hparent.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hparent_none :
      Znth v parent_cells_2 None = Some parent_v).
  { rewrite (Znth_indep parent_cells_2 v None __default__App_option_Z)
      by lia.
    exact PreH11. }
  pose proof
    (traversal_adj_enter__solver_traversal_init
      nv kv edges i order_data_2 parent_cells_2
      head_data to_data_2 next_data_2 v parent_v
      PreH19 PreH21 PreH22 ltac:(lia) PreH8 Hparent_none) as Hstate.
  unfold TraversalAdjState in Hstate.
  destruct Hstate as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hcurrent _]]]]]]]]].
  rewrite <- (Znth_indep head_data v 0 (-1) ltac:(lia)) in Hcurrent.
  specialize (Hcurrent (proj1 H) (proj2 H)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hparent_none :
      Znth v parent_cells_2 None = Some parent_v).
  { rewrite (Znth_indep parent_cells_2 v None __default__App_option_Z)
      by lia.
    exact PreH11. }
  rewrite (Znth_indep head_data v 0 (-1)) by lia.
  eapply traversal_adj_enter__solver_traversal_init; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH18. exact H.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH17. exact H.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AdjacencyModel in PreH21.
  destruct PreH21 as
    [_ [_ [_ [_ [Hheads _]]]]].
  specialize (Hheads v ltac:(lia)).
  rewrite (Znth_indep head_data v 0 (-1)) by lia.
  destruct Hheads; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_6 : solver_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AdjacencyModel in PreH21.
  destruct PreH21 as
    [_ [_ [_ [_ [Hheads _]]]]].
  specialize (Hheads v ltac:(lia)).
  rewrite (Znth_indep head_data v 0 (-1)) by lia.
  destruct Hheads; lia.
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
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    eapply traversal_finish_entry__solver_traversal_steps;
    [lia | exact PreH11 | subst e; exact PreH25]).
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_2 : solver_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(intros; apply PreH21; assumption).
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_3 : solver_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(intros; apply PreH20; assumption).
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Hdefault : Znth e next_data_2 0 = Znth e next_data_2 (-1)).
  { apply Znth_default_irrelevant__solver_traversal_steps.
    rewrite PreH33. lia. }
  rewrite Hdefault in *.
  pose proof (traversal_adj_append_next_length__solver_traversal_steps
    nv kv edges i order_data_2 parent_cells_2 head_data_2 to_data_2
    next_data_2 v parent_v e PreH38 PreH39 PreH40 ltac:(
      rewrite PreH34; exact PreH20) PreH27 PreH17 PreH16 PreH41
    ltac:(tauto) ltac:(tauto)) as Hlength.
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH34 in Hlength.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_2 : solver_entail_wit_11_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Hdefault : Znth e next_data_2 0 = Znth e next_data_2 (-1)).
  { apply Znth_default_irrelevant__solver_traversal_steps.
    rewrite PreH33. lia. }
  rewrite Hdefault.
  eapply traversal_adj_append_advance__solver_traversal_steps;
    [exact PreH38 | exact PreH39 | exact PreH40 |
     rewrite PreH34; exact PreH20 | exact PreH27 | exact PreH17 |
     exact PreH16 | exact PreH41].
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_3 : solver_entail_wit_11_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    rewrite Zlength_replace_Znth__solver_traversal_steps; exact PreH35).
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_4 : solver_entail_wit_11_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH34; lia).
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_5 : solver_entail_wit_11_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(idtac).
  pose proof (traversal_adj_append_advance__solver_traversal_steps
    nv kv edges i order_data_2 parent_cells_2 head_data_2 to_data_2
    next_data_2 v parent_v e PreH38 PreH39 PreH40 ltac:(
      rewrite PreH34; exact PreH20) PreH27 PreH17 PreH16 PreH41) as Hnew.
  assert (Hdefault_parent :
    Znth v (replace_Znth (Znth e to_data_2 0) (Some v) parent_cells_2)
      __default__App_option_Z =
    Znth v (replace_Znth (Znth e to_data_2 0) (Some v) parent_cells_2) None).
  { apply Znth_default_irrelevant__solver_traversal_steps.
    rewrite Zlength_replace_Znth__solver_traversal_steps, PreH35. lia. }
  rewrite Hdefault_parent.
  unfold TraversalAdjState in Hnew. tauto.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_6 : solver_entail_wit_11_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(
    rewrite Znth_app_left__solver_traversal_steps;
    [exact PreH27 | rewrite PreH34; lia]).
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_11_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Hdefault : Znth e next_data_2 0 = Znth e next_data_2 (-1)).
  { apply Znth_default_irrelevant__solver_traversal_steps.
    rewrite PreH18. lia. }
  rewrite Hdefault in *.
  rewrite <- PreH19.
  eapply traversal_adj_parent_next_length__solver_traversal_steps;
    [exact PreH23 | exact PreH25 | rewrite PreH19; exact PreH5 | exact PreH12 |
     exact PreH2 | exact PreH1 | exact PreH26 | tauto | tauto].
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_2 : solver_entail_wit_11_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Hdefault : Znth e next_data_2 0 = Znth e next_data_2 (-1)).
  { apply Znth_default_irrelevant__solver_traversal_steps.
    rewrite PreH18. lia. }
  rewrite Hdefault.
  eapply traversal_adj_advance_parent__solver_traversal_steps;
    [exact PreH23 | exact PreH25 | rewrite PreH19; exact PreH5 |
     exact PreH12 | exact PreH2 | exact PreH1 | exact PreH26].
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = top) by lia.
  unfold TraversalEntryState in PreH17.
  destruct PreH17 as [Htraversal Hentry].
  destruct (traversal_complete_rooted_order__solver_traversal_finish
    nv kv edges i order_data_2 parent_cells PreH14 ltac:(lia) Htraversal)
    as [parent_data [Horder_length
      [Hparent_cells [Hrooted Hpointwise]]]].
  assert (Htop : top = nv) by lia.
  pose proof PreH14 as Hpre_fields.
  unfold Pre in Hpre_fields.
  destruct Hpre_fields as [Hkn [Hnmax Hpre_rest]].
  pose proof (search_state_initial__solver_traversal_finish
    nv kv edges PreH14) as Hsearch.
  assert (Hparent_length : Zlength parent_data = nv).
  { rewrite Hparent_cells in PreH11.
    rewrite !Zlength_correct, length_map in PreH11.
    rewrite Zlength_correct. exact PreH11. }
  subst top.
  rewrite Hparent_cells.
  sep_apply_l_atomic
    (IntArray.mixed_full_to_full parent_p_2 nv parent_data).
  rewrite Horder_length.
  rewrite IntArray.undef_seg_empty.
  sep_apply_l_atomic
    (IntArray.seg_to_full order_p_2 0 nv order_data_2).
  replace (order_p_2 + 0 * sizeof (INT)) with order_p_2 by lia.
  replace (nv - 0) with nv by lia.
  Exists size_p_2 order_p_2 parent_p_2 next_p_2 to_p_2 head_p_2
    next_data_2 to_data_2 order_data_2 parent_data head_data_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try exact Hparent_length.
    all: try exact Hsearch.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_3 : solver_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_4 : solver_entail_wit_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_5 : solver_entail_wit_13_split_goal_5.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_6 : solver_entail_wit_13_split_goal_6.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_7 : solver_entail_wit_13_split_goal_7.
Proof.
  LLM_pre_process ltac:(unfold SearchState in *; intuition eauto; lia).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SearchState in PreH22 |- *.
  destruct PreH22 as
    [Hlo [Hhi [Hbest [optimum
      [Hspec [Hoptimum [Hbestopt Hregion]]]]]]].
  destruct Hlo as [Hlo_lower Hlo_upper].
  destruct Hhi as [Hhi_lower Hhi_upper].
  destruct Hbest as [Hbest_lower Hbest_upper].
  destruct Hoptimum as [Hoptimum_lower Hoptimum_upper].
  destruct Hbestopt as [Hbestopt_lower Hbestopt_upper].
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  apply (proj1 PreH3) in PreH23.
  unfold ThresholdFeasible in PreH23.
  destruct PreH23 as [feasible_optimum [Hfeasible_spec Hmidopt]].
  assert (Hsame : feasible_optimum = optimum).
  { eapply spec_unique__solver_search_transitions; eauto. }
  subst feasible_optimum.
  split; [split; lia |].
  split; [split; lia |].
  split; [split; lia |].
  exists optimum.
  split; [exact Hspec |].
  split; [split; lia |].
  split; [split; lia |].
  destruct Hregion as [Hinterval | [Hbesteq Hoptlt]].
  - destruct (Z.eq_dec (Z.quot (lo + hi) 2) optimum) as [Heq | Hneq].
    + right. lia.
    + left. lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_5 : solver_entail_wit_14_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SearchState in PreH22 |- *.
  destruct PreH22 as
    [Hlo [Hhi [Hbest [optimum
      [Hspec [Hoptimum [Hbestopt Hregion]]]]]]].
  destruct Hlo as [Hlo_lower Hlo_upper].
  destruct Hhi as [Hhi_lower Hhi_upper].
  destruct Hbest as [Hbest_lower Hbest_upper].
  destruct Hoptimum as [Hoptimum_lower Hoptimum_upper].
  destruct Hbestopt as [Hbestopt_lower Hbestopt_upper].
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  assert (Hinfeasible :
      ~ ThresholdFeasible nv kv edges (Z.quot (lo + hi) 2)).
  { intro Hfeasible.
    apply (proj2 PreH3) in Hfeasible.
    apply Hfeasible. exact PreH23. }
  assert (Hoptmid : optimum < Z.quot (lo + hi) 2).
  { destruct (Z_lt_ge_dec optimum (Z.quot (lo + hi) 2)) as [Hlt | Hge].
    - exact Hlt.
    - exfalso. apply Hinfeasible.
      exists optimum. split; [exact Hspec | lia]. }
  split; [split; lia |].
  split; [split; lia |].
  split; [split; lia |].
  exists optimum.
  split; [exact Hspec |].
  split; [split; lia |].
  split; [split; lia |].
  destruct Hregion as [Hinterval | Hfinished].
  - left. lia.
  - right. exact Hfinished.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (midpoint_bounds__solver_search_transitions lo hi ltac:(lia) PreH5) as Hmid.
  destruct Hmid as [Hmidlo Hmidhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply search_state_closed_spec__solver_finalization; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH2.
  destruct PreH2 as [_ [_ [Hedges _]]].
  rewrite Hedges.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_1 : solver_partial_solve_wit_29_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  apply Z.div_le_lower_bound; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_2 : solver_partial_solve_wit_29_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  apply Z.div_le_upper_bound; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_3 : solver_partial_solve_wit_29_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH29.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_4 : solver_partial_solve_wit_29_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH29.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_5 : solver_partial_solve_wit_29_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH29.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_6 : solver_partial_solve_wit_29_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure : solver_partial_solve_wit_29_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_5.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_6.
Qed.

Lemma proof_of_solver_partial_solve_wit_31_pure_split_goal_1 : solver_partial_solve_wit_31_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH14.
  destruct PreH14 as [Hkn _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_31_pure : solver_partial_solve_wit_31_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_31_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_32_pure_split_goal_1 : solver_partial_solve_wit_32_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH14.
  destruct PreH14 as [Hkn _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_32_pure : solver_partial_solve_wit_32_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_32_pure_split_goal_1.
Qed.
