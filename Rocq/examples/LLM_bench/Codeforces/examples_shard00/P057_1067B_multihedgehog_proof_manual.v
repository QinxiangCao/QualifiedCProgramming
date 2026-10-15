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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P057_1067B_multihedgehog_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P057_1067B_multihedgehog_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P057_1067B_multihedgehog_lib.
Local Open Scope sac.

Lemma proof_of_bfs_safety_wit_15_split_goal_1 : bfs_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
    unfold BFSAdjState in PreH19;
    destruct PreH19 as
      [Hqueue [_ [_ [_ [_ [Hslot [_ [Hfrontier _]]]]]]]];
    unfold BFSQueueState in Hqueue;
    destruct Hqueue as [_ [Hdlen [_ [_ [_ [_ [Hsrc _]]]]]]];
    pose proof (PreH17 PreH2) as Hneighbor;
    destruct Hneighbor as [[Hneighbor _] _];
    destruct PreH6 as [_ [_ [_ [_ [_ [_ [Hmodel _]]]]]]];
    assert (Hedge :
      In (v + 1, Znth e to_data_bfs_run 0 + 1) edges_bfs_run \/
      In (Znth e to_data_bfs_run 0 + 1, v + 1) edges_bfs_run) by
      (apply (proj2 (Hmodel v (Znth e to_data_bfs_run 0)
        ltac:(lia) Hneighbor)); exists e; split;
       [destruct Hslot as [Hbad | Hslot]; [contradiction | exact Hslot] |
        reflexivity]);
    unfold BFSFrontierState in Hfrontier;
    assert (Hneg : Znth (Znth e to_data_bfs_run 0) dist_data (-1) < 0) by
      (rewrite (Znth_indep dist_data (Znth e to_data_bfs_run 0) (-1) 0)
         by lia; exact PreH1);
    pose proof (Hfrontier (Znth e to_data_bfs_run 0)
      Hneighbor Hedge Hneg) as Hdistance;
    rewrite (Znth_indep dist_data v (-1) 0) in Hdistance by lia;
    destruct PreH5 as [Htree _];
    pose proof (graph_distance_bounds__bounds_safety nv_bfs_run edges_bfs_run
      (src_pre + 1) (Znth e to_data_bfs_run 0 + 1)
      (Znth v dist_data 0 + 1) Htree ltac:(lia) Hdistance);
    lia.
Qed.

Lemma proof_of_bfs_safety_wit_15_split_goal_2 : bfs_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
    unfold BFSAdjState in PreH19;
    destruct PreH19 as
      [Hqueue [_ [_ [_ [_ [Hslot [_ [Hfrontier _]]]]]]]];
    unfold BFSQueueState in Hqueue;
    destruct Hqueue as [_ [Hdlen [_ [_ [_ [_ [Hsrc _]]]]]]];
    pose proof (PreH17 PreH2) as Hneighbor;
    destruct Hneighbor as [[Hneighbor _] _];
    destruct PreH6 as [_ [_ [_ [_ [_ [_ [Hmodel _]]]]]]];
    assert (Hedge :
      In (v + 1, Znth e to_data_bfs_run 0 + 1) edges_bfs_run \/
      In (Znth e to_data_bfs_run 0 + 1, v + 1) edges_bfs_run) by
      (apply (proj2 (Hmodel v (Znth e to_data_bfs_run 0)
        ltac:(lia) Hneighbor)); exists e; split;
       [destruct Hslot as [Hbad | Hslot]; [contradiction | exact Hslot] |
        reflexivity]);
    unfold BFSFrontierState in Hfrontier;
    assert (Hneg : Znth (Znth e to_data_bfs_run 0) dist_data (-1) < 0) by
      (rewrite (Znth_indep dist_data (Znth e to_data_bfs_run 0) (-1) 0)
         by lia; exact PreH1);
    pose proof (Hfrontier (Znth e to_data_bfs_run 0)
      Hneighbor Hedge Hneg) as Hdistance;
    rewrite (Znth_indep dist_data v (-1) 0) in Hdistance by lia;
    destruct PreH5 as [Htree _];
    pose proof (graph_distance_bounds__bounds_safety nv_bfs_run edges_bfs_run
      (src_pre + 1) (Znth e to_data_bfs_run 0 + 1)
      (Znth v dist_data 0 + 1) Htree ltac:(lia) Hdistance);
    lia.
Qed.

Lemma proof_of_bfs_safety_wit_15 : bfs_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_bfs_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_bfs_entail_wit_1 : bfs_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hshape : forall x lo hi,
    IntArray.seg_shape x lo hi |--
      EX data : list Z,
        “ Zlength data = hi - lo ” && IntArray.seg x lo hi data).
  {
    intros x lo hi.
    unfold IntArray.seg_shape, IntArray.seg.
    set (len := Z.to_nat (hi - lo)).
    assert (Hlen : len = Z.to_nat (hi - lo)) by reflexivity.
    clearbody len.
    revert lo hi Hlen.
    induction len as [|len IH]; intros lo hi Hlen; simpl.
    - Exists (@nil Z).
      Intros.
      subst hi.
      replace (lo - lo) with 0 by lia.
      rewrite Zlength_nil.
      andp_cancel.
      simpl store_array_rec.
      andp_cancel.
    - Intros a.
      assert (Htail : len = Z.to_nat (hi - (lo + 1))).
      {
        replace (Z.to_nat (hi - lo)) with
          (S (Z.to_nat (hi - (lo + 1)))) in Hlen by lia.
        inversion Hlen.
        reflexivity.
      }
      sep_apply (IH (lo + 1) hi Htail).
      Intros data.
      Exists (a :: data).
      simpl.
      LLM_pre_process ltac:(lia || nia || int_auto).
      replace (Zlength (a :: data)) with (hi - lo) by
        (rewrite Zlength_cons; lia).
      andp_cancel.
  }
  sep_apply IntArray.full_shape_to_seg_shape.
  sep_apply Hshape.
  Intros parent_data.
  sep_apply IntArray.seg_to_full.
  sep_apply IntArray.full_shape_to_seg_shape.
  sep_apply Hshape.
  Intros dist_data.
  sep_apply IntArray.seg_to_full.
  sep_apply IntArray.seg_single.
  Exists dist_data parent_data.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (dist_pre + 0 * sizeof (INT)) with dist_pre by lia.
  replace (parent_pre + 0 * sizeof (INT)) with parent_pre by lia.
  replace (nv_bfs_run - 0) with nv_bfs_run in H, H0 |- * by lia.
  replace (0 + 1) with 1 by lia.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_bfs_entail_wit_2_split_goal_1 : bfs_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH13.
Qed.

Lemma proof_of_bfs_entail_wit_2_split_goal_2 : bfs_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH12.
Qed.

Lemma proof_of_bfs_entail_wit_2 : bfs_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_bfs_entail_wit_3_split_goal_1 : bfs_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = nv_bfs_run) as Hi by lia.
  subst i.
  unfold BFSQueueState.
  split; [exact PreH12 |].
  split.
  - rewrite Zlength_replace_Znth. exact PreH13.
  - split; [rewrite Zlength_cons, Zlength_nil; lia |].
    split; [rewrite Zlength_cons, Zlength_nil; lia |].
    split.
    + constructor; [simpl; tauto | constructor].
    + split; [rewrite Znth0_cons; reflexivity |].
      split; [lia |].
      split; [lia |].
      split.
      * unfold BFSParentState.
        split.
        -- rewrite <- (Znth_indep parent_data_2 src_pre 0 (-1)) by
             (rewrite PreH12; lia).
           apply PreH14. lia.
        -- intros vertex Hvertex Hnot_source Hseen.
           rewrite Znth_replace_Znth_Diff in Hseen by
             (try rewrite PreH13; lia).
           rewrite <- (Znth_indep dist_data_2 vertex 0 (-1)) in Hseen by
             (rewrite PreH13; lia).
           rewrite PreH15 in Hseen by lia.
           lia.
      * split.
        -- intros qindex Hqindex.
           assert (qindex = 0) by
             (rewrite Zlength_cons, Zlength_nil in Hqindex; lia).
           subst qindex. rewrite Znth0_cons. split; [lia |].
           rewrite Znth_replace_Znth_Same by
             (rewrite PreH13; lia).
           lia.
        -- split.
           ++ intros vertex Hvertex.
              split.
              ** intros Hin.
                 simpl in Hin.
                 destruct Hin as [Heq | Hfalse]; [subst vertex | contradiction].
                 rewrite Znth_replace_Znth_Same by
                   (rewrite PreH13; lia).
                 lia.
              ** intros Hseen.
                 destruct (Z.eq_dec vertex src_pre) as [Heq | Hneq].
                 --- subst vertex. simpl. auto.
                 --- rewrite Znth_replace_Znth_Diff in Hseen by
                       (try rewrite PreH13; lia).
                     rewrite <- (Znth_indep dist_data_2 vertex 0 (-1)) in Hseen by
                       (rewrite PreH13; lia).
                     rewrite PreH15 in Hseen by lia.
                     lia.
           ++ split.
              ** intros qindex Hqindex. lia.
              ** split.
                 --- intros qindex neighbor Hqindex. lia.
                 --- intros vertex Hvertex Hseen.
                     assert (vertex = src_pre) as Heq.
                     {
                       destruct (Z.eq_dec vertex src_pre) as [Heq | Hneq];
                         [exact Heq |].
                       rewrite Znth_replace_Znth_Diff in Hseen by
                         (try rewrite PreH13; lia).
                       rewrite <- (Znth_indep dist_data_2 vertex 0 (-1)) in Hseen by
                         (rewrite PreH13; lia).
                       rewrite PreH15 in Hseen by lia.
                       lia.
                     }
                     subst vertex.
                     rewrite Znth_replace_Znth_Same by
                       (rewrite PreH13; lia).
                     apply graph_distance_zero_refl__bfs_initialization.
Qed.

Lemma proof_of_bfs_entail_wit_3_split_goal_2 : bfs_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (qindex = 0) by lia.
  subst qindex.
  rewrite Znth0_cons, PreH12.
  lia.
Qed.

Lemma proof_of_bfs_entail_wit_3_split_goal_3 : bfs_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_bfs_entail_wit_3 : bfs_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_bfs_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_bfs_entail_wit_4_1_split_goal_1 : bfs_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  eapply bfs_adj_entry__bfs_queue_entry with (old_farthest := far).
  - exact PreH5.
  - exact PreH6.
  - exact PreH14.
  - rewrite <- PreH9. exact PreH2.
  - apply PreH13. lia.
  - lia.
  - intros qindex Hqindex.
    unfold BFSQueueState in PreH14.
    destruct PreH14 as
      [_ [Hdistances [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hprior _]]]]]]]]]]]].
    specialize (Hprior qindex Hqindex).
    rewrite <- (Znth_indep dist_data_2 (Znth l queue_data 0) (-1) 0)
      in PreH1 by (rewrite Hdistances; apply PreH13; lia).
    rewrite <- (Znth_indep dist_data_2 far (-1) 0)
      in PreH1 by (rewrite Hdistances; lia).
    lia.
Qed.

Lemma proof_of_bfs_entail_wit_4_1_split_goal_2 : bfs_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  match goal with
  | H : _ /\ _ |- _ => destruct H as [Hhead Hnegative]
  end.
  pose proof (unseen_head_implies_queue_not_full__bfs_queue_entry
    nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2
    dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run
    PreH6 PreH14 ltac:(rewrite <- PreH9; exact PreH2)
    Hhead Hnegative) as Hnotfull.
  rewrite <- PreH9 in Hnotfull.
  exact Hnotfull.
Qed.

Lemma proof_of_bfs_entail_wit_4_1_split_goal_3 : bfs_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof (adjacency_head_facts__bfs_queue_entry
    nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run
    next_data_bfs_run (Znth l queue_data 0) PreH6
    ltac:(apply PreH13; lia)) as [_ Hfacts].
  specialize (Hfacts H).
  destruct Hfacts as [Hto [Hnext_lo Hnext_hi]].
  exact (conj (conj Hto Hnext_lo) Hnext_hi).
Qed.

Lemma proof_of_bfs_entail_wit_4_1_split_goal_4 : bfs_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof (adjacency_head_facts__bfs_queue_entry
    nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run
    next_data_bfs_run (Znth l queue_data 0) PreH6
    ltac:(apply PreH13; lia)) as [Hbounds _].
  lia.
Qed.

Lemma proof_of_bfs_entail_wit_4_1_split_goal_5 : bfs_entail_wit_4_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof (adjacency_head_facts__bfs_queue_entry
    nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run
    next_data_bfs_run (Znth l queue_data 0) PreH6
    ltac:(apply PreH13; lia)) as [Hbounds _].
  lia.
Qed.

Lemma proof_of_bfs_entail_wit_4_1 : bfs_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_bfs_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_bfs_entail_wit_4_1_split_goal_4.
  - Goal_apply proof_of_bfs_entail_wit_4_1_split_goal_5.
Qed.

Lemma proof_of_bfs_entail_wit_4_2_split_goal_1 : bfs_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof PreH14 as Hqueue_facts.
  unfold BFSQueueState in Hqueue_facts.
  destruct Hqueue_facts as [_ [Hdistances _]].
  rewrite <- (Znth_indep dist_data_2 (Znth l queue_data 0) (-1) 0)
    in PreH1 by (rewrite Hdistances; apply PreH13; lia).
  rewrite <- (Znth_indep dist_data_2 far (-1) 0)
    in PreH1 by (rewrite Hdistances; lia).
  eapply bfs_adj_entry__bfs_queue_entry with (old_farthest := far).
  - exact PreH5.
  - exact PreH6.
  - exact PreH14.
  - rewrite <- PreH9. exact PreH2.
  - exact (conj PreH11 PreH12).
  - exact PreH1.
  - unfold BFSQueueState in PreH14.
    destruct PreH14 as
      [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hprior _]]]]]]]]]]]].
    exact Hprior.
Qed.

Lemma proof_of_bfs_entail_wit_4_2_split_goal_2 : bfs_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  match goal with
  | H : _ /\ _ |- _ => destruct H as [Hhead Hnegative]
  end.
  pose proof (unseen_head_implies_queue_not_full__bfs_queue_entry
    nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2
    dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run
    PreH6 PreH14 ltac:(rewrite <- PreH9; exact PreH2)
    Hhead Hnegative) as Hnotfull.
  rewrite <- PreH9 in Hnotfull.
  exact Hnotfull.
Qed.

Lemma proof_of_bfs_entail_wit_4_2_split_goal_3 : bfs_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof (adjacency_head_facts__bfs_queue_entry
    nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run
    next_data_bfs_run (Znth l queue_data 0) PreH6
    ltac:(apply PreH13; lia)) as [_ Hfacts].
  specialize (Hfacts H).
  destruct Hfacts as [Hto [Hnext_lo Hnext_hi]].
  exact (conj (conj Hto Hnext_lo) Hnext_hi).
Qed.

Lemma proof_of_bfs_entail_wit_4_2_split_goal_4 : bfs_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof (adjacency_head_facts__bfs_queue_entry
    nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run
    next_data_bfs_run (Znth l queue_data 0) PreH6
    ltac:(apply PreH13; lia)) as [Hbounds _].
  lia.
Qed.

Lemma proof_of_bfs_entail_wit_4_2_split_goal_5 : bfs_entail_wit_4_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (l - 0) with l in * by lia.
  pose proof (adjacency_head_facts__bfs_queue_entry
    nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run
    next_data_bfs_run (Znth l queue_data 0) PreH6
    ltac:(apply PreH13; lia)) as [Hbounds _].
  lia.
Qed.

Lemma proof_of_bfs_entail_wit_4_2 : bfs_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_bfs_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_bfs_entail_wit_4_2_split_goal_4.
  - Goal_apply proof_of_bfs_entail_wit_4_2_split_goal_5.
Qed.

Lemma proof_of_bfs_entail_wit_5_1_split_goal_1 : bfs_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  destruct PreH5 as [Htree _].
  eapply bfs_adj_undiscovered_advance__bfs_neighbor_step;
    [exact Htree | exact PreH6 | exact PreH19 | exact PreH2 |
     exact PreH1 | rewrite <- PreH9; apply PreH18; split; assumption].
Qed.

Lemma proof_of_bfs_entail_wit_5_1_split_goal_2 : bfs_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(intros).
  match goal with
  | Hcond : Znth e next_data_bfs_run 0 <> -1 /\ _ |- _ =>
      destruct Hcond as [Hnext_not_minus Hnext_negative]
  end.
  destruct PreH5 as [Htree _].
  assert (Hnew :
      BFSAdjState nv_bfs_run edges_bfs_run src_pre l far
        (queue_data_2 ++ (Znth e to_data_bfs_run 0 :: nil))
        (replace_Znth (Znth e to_data_bfs_run 0) v parent_data_2)
        (replace_Znth (Znth e to_data_bfs_run 0)
          (Znth v dist_data_2 0 + 1) dist_data_2)
        head_data_bfs_run to_data_bfs_run next_data_bfs_run v
        (Znth e next_data_bfs_run 0)).
  { eapply bfs_adj_undiscovered_advance__bfs_neighbor_step;
      [exact Htree | exact PreH6 | exact PreH19 | exact PreH2 |
       exact PreH1 | rewrite <- PreH9; apply PreH18; split; assumption]. }
  unfold BFSAdjState in Hnew.
  destruct Hnew as [Hqueue_new _].
  pose proof PreH6 as Hmodel.
  destruct Hmodel as
    [_ [_ [Hnextlen [_ [_ [Hslot_info _]]]]]].
  destruct (PreH17 PreH2) as [[Hcurrent_target Hnext_lower] Hnext_upper].
  pose proof (Hslot_info (Znth e next_data_bfs_run 0) ltac:(lia))
    as [Hnext_target _].
  pose proof (bfs_queue_missing_length__bfs_neighbor_step
    _ _ _ _ _ _ _ _ _ Hqueue_new Hnext_target Hnext_negative) as Hlen.
  rewrite Zlength_app, Zlength_cons, Zlength_nil, <- PreH9 in Hlen.
  exact Hlen.
Qed.

Lemma proof_of_bfs_entail_wit_5_1_split_goal_3 : bfs_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(intros).
  match goal with
  | Hcond : Znth e next_data_bfs_run 0 <> -1 |- _ =>
      rename Hcond into Hnext_not_minus
  end.
  pose proof PreH6 as Hmodel.
  destruct Hmodel as
    [_ [_ [Hnextlen [_ [_ [Hslot_info _]]]]]].
  destruct (PreH17 PreH2) as [[Hcurrent_target Hnext_lower] Hnext_upper].
  pose proof (Hslot_info (Znth e next_data_bfs_run 0) ltac:(lia))
    as [Hnext_target Hnext_cases].
  assert (Hdefault :
      Znth (Znth e next_data_bfs_run 0) next_data_bfs_run (-1) =
      Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0).
  { apply Znth_indep. rewrite Hnextlen. lia. }
  rewrite Hdefault in Hnext_cases.
  destruct Hnext_cases; repeat split; lia.
Qed.

Lemma proof_of_bfs_entail_wit_5_1_split_goal_4 : bfs_entail_wit_5_1_split_goal_4.
Proof. LLM_pre_process ltac:(intros; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia). Qed.

Lemma proof_of_bfs_entail_wit_5_1 : bfs_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_bfs_entail_wit_5_1_split_goal_3.
  - Goal_apply proof_of_bfs_entail_wit_5_1_split_goal_4.
Qed.

Lemma proof_of_bfs_entail_wit_5_2_split_goal_1 : bfs_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  destruct PreH5 as [Htree _].
  eapply bfs_adj_existing_advance__bfs_neighbor_step;
    [exact Htree | exact PreH6 | exact PreH19 | exact PreH2 | lia].
Qed.

Lemma proof_of_bfs_entail_wit_5_2_split_goal_2 : bfs_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(intros).
  match goal with
  | Hcond : Znth e next_data_bfs_run 0 <> -1 /\ _ |- _ =>
      destruct Hcond as [Hnext_not_minus Hnext_negative]
  end.
  unfold BFSAdjState in PreH19.
  destruct PreH19 as [Hqueue _].
  pose proof PreH6 as Hmodel.
  destruct Hmodel as
    [_ [_ [Hnextlen [_ [_ [Hslot_info _]]]]]].
  destruct (PreH17 PreH2) as [[Hcurrent_target Hnext_lower] Hnext_upper].
  pose proof (Hslot_info (Znth e next_data_bfs_run 0) ltac:(lia))
    as [Hnext_target _].
  pose proof (bfs_queue_missing_length__bfs_neighbor_step
    _ _ _ _ _ _ _ _ _ Hqueue Hnext_target Hnext_negative) as Hlen.
  rewrite <- PreH9 in Hlen. exact Hlen.
Qed.

Lemma proof_of_bfs_entail_wit_5_2_split_goal_3 : bfs_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(intros).
  match goal with
  | Hcond : Znth e next_data_bfs_run 0 <> -1 |- _ =>
      rename Hcond into Hnext_not_minus
  end.
  pose proof PreH6 as Hmodel.
  destruct Hmodel as
    [_ [_ [Hnextlen [_ [_ [Hslot_info _]]]]]].
  destruct (PreH17 PreH2) as [[Hcurrent_target Hnext_lower] Hnext_upper].
  pose proof (Hslot_info (Znth e next_data_bfs_run 0) ltac:(lia))
    as [Hnext_target Hnext_cases].
  assert (Hdefault :
      Znth (Znth e next_data_bfs_run 0) next_data_bfs_run (-1) =
      Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0).
  { apply Znth_indep. rewrite Hnextlen. lia. }
  rewrite Hdefault in Hnext_cases.
  destruct Hnext_cases; repeat split; lia.
Qed.

Lemma proof_of_bfs_entail_wit_5_2 : bfs_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_bfs_entail_wit_5_2_split_goal_3.
Qed.

Lemma proof_of_bfs_entail_wit_6_split_goal_1 : bfs_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros).
  subst e.
  eapply bfs_adj_close__bfs_neighbor_step; exact PreH18.
Qed.

Lemma proof_of_bfs_entail_wit_6_split_goal_2 : bfs_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(intros).
  subst e.
  unfold BFSAdjState in PreH18.
  destruct PreH18 as [Hq _].
  unfold BFSQueueState in Hq.
  destruct Hq as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hentries _]]]]]]]]]].
  match goal with
  | Hidx : 0 <= qindex /\ qindex < r |- _ =>
      apply Hentries; rewrite <- PreH8; exact Hidx
  end.
Qed.

Lemma proof_of_bfs_entail_wit_6 : bfs_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_bfs_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_bfs_entail_wit_7 : bfs_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (bfs_queue_complete_result__bfs_final_result
      nv_bfs_run edges_bfs_run src_pre l far queue_data_2
      parent_data_2 dist_data_2 PreH4 PreH13 ltac:(lia))
    as [Hqueue_complete Hbfs].
  assert (Hr : r = nv_bfs_run) by lia.
  assert (Hl : l = nv_bfs_run) by lia.
  Exists parent_data_2 dist_data_2 queue_data_2.
  split_pure_spatial.
  - replace r with nv_bfs_run by (symmetry; exact Hr).
    replace l with nv_bfs_run by (symmetry; exact Hl).
    rewrite (IntArray.undef_seg_empty q nv_bfs_run).
    sep_apply_l_atomic
      (IntArray.seg_to_full q 0 nv_bfs_run queue_data_2).
    replace (q + 0 * sizeof (INT)) with q by lia.
    replace (nv_bfs_run - 0) with nv_bfs_run by lia.
    repeat cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Hqueue_complete.
    + dump_pre_spatial. exact Hbfs.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
    specialize (PreH17 i ltac:(lia));
    destruct PreH17 as [[[[Hu _] _] _] _];
    unfold Pre, GraphPre, TreeInput in PreH6;
    destruct PreH6 as [_ [[_ [Hedges _]] _]];
    pose proof (degree_prefix_bounds__bounds_safety nv edges i degree_data
      (Znth i eu_data 0) PreH15 ltac:(lia) ltac:(lia));
    lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
    specialize (PreH17 i ltac:(lia));
    destruct PreH17 as [[[[Hu _] _] _] _];
    unfold Pre, GraphPre, TreeInput in PreH6;
    destruct PreH6 as [_ [[_ [Hedges _]] _]];
    pose proof (degree_prefix_bounds__bounds_safety nv edges i degree_data
      (Znth i eu_data 0) PreH15 ltac:(lia) ltac:(lia));
    lia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
    specialize (PreH17 i ltac:(lia));
    destruct PreH17 as [[[[Hu Hv0] Hvlt] _] _];
    unfold Pre, GraphPre, TreeInput in PreH6;
    destruct PreH6 as [_ [[_ [Hedges _]] _]];
    pose proof (degree_prefix_bounds__bounds_safety nv edges i degree_data
      (Znth i ev_data 0) PreH15 ltac:(lia) ltac:(lia)) as Hdeg;
    destruct (Z.eq_dec (Znth i eu_data 0) (Znth i ev_data 0))
      as [Heq | Hneq];
    [rewrite Heq; rewrite Znth_replace_Znth_Same by lia |
     rewrite Znth_replace_Znth_Diff by lia];
    lia.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
    specialize (PreH17 i ltac:(lia));
    destruct PreH17 as [[[[Hu Hv0] Hvlt] _] _];
    unfold Pre, GraphPre, TreeInput in PreH6;
    destruct PreH6 as [_ [[_ [Hedges _]] _]];
    pose proof (degree_prefix_bounds__bounds_safety nv edges i degree_data
      (Znth i ev_data 0) PreH15 ltac:(lia) ltac:(lia)) as Hdeg;
    destruct (Z.eq_dec (Znth i eu_data 0) (Znth i ev_data 0))
      as [Heq | Hneq];
    [rewrite Heq; rewrite Znth_replace_Znth_Same by lia |
     rewrite Znth_replace_Znth_Diff by lia];
    lia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros j Hj.
  pose proof (PreH10 j ltac:(lia)) as [[[Hfu1 Hfun] Hfv1] Hfvn].
  pose proof (PreH15 j ltac:(lia)) as [Heu Hev].
  repeat split; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst nn_pre.
  unfold Pre in PreH11.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH11 as Hheadvals.
  assert (i = nv) by lia. subst i.
  assert (Hbuild : AdjacencyBuildState nv edges 0 head_init (@nil Z) (@nil Z)).
  { unfold AdjacencyBuildState.
    split; [pose proof (Zlength_nonneg edges); lia |].
    split; [exact H |].
    split; [rewrite Zlength_nil; lia |].
    split; [rewrite Zlength_nil; lia |].
    split.
    - intros u Hu. left.
      rewrite <- (Znth_indep head_init u 0 (-1)) by lia.
      apply Hheadvals. lia.
    - split.
      + intros slot Hslot. lia.
      + split.
        * intros u v Hu Hv. split.
          -- unfold sublist. simpl. tauto.
          -- intros [slot [Hslot Hto]].
             unfold AdjacencySlot in Hslot.
             destruct Hslot as [_ [Hbound _]].
             rewrite Zlength_nil in Hbound. lia.
        * intros u slot1 slot2 Hslot1.
          unfold AdjacencySlot in Hslot1.
          destruct Hslot1 as [_ [Hbound _]].
          rewrite Zlength_nil in Hbound. lia. }
  assert (Hdegree : DegreePrefix nv edges 0 (repeat_Z 0 nv)).
  { unfold DegreePrefix. split.
    - unfold repeat_Z.
      rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
      reflexivity.
    - intros v Hv.
      unfold repeat_Z. rewrite Znth_repeat.
      unfold Degree, sublist. reflexivity. }
  assert (Hfresh : forall index, CurrentEdgeFresh edges index).
  { unfold GraphPre in PreH7.
    destruct PreH7 as [Htree _].
    unfold TreeInput in Htree.
    destruct Htree as [_ [_ [_ [Hfresh _]]]].
    exact Hfresh. }
  Exists deg_p_2 next_p_2 to_p_2 head_p_2
    (repeat_Z 0 nv) (@nil Z) (@nil Z) head_init.
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
    unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH17 i ltac:(lia)).
  destruct PreH17 as [[[[[Hu0 Hun] Hv0] Hvn] Heu] Hev].
  pose proof PreH6 as Hpre.
  unfold Pre in Hpre. destruct Hpre as [_ Hgraph].
  unfold GraphPre in Hgraph. destruct Hgraph as [Htree _].
  unfold TreeInput in Htree. destruct Htree as [_ [Hedges _]].
  assert (Hindex : 0 <= i < Zlength edges) by lia.
  assert (Hedge_i : Znth i edges __default__Prod_Z_Z =
      (Znth i eu_data 0 + 1, Znth i ev_data 0 + 1)).
  { destruct (Znth i edges __default__Prod_Z_Z) as [a b] eqn:Hedge.
    simpl in Heu, Hev. f_equal; lia. }
  pose proof (PreH16 i) as Hfresh.
  unfold CurrentEdgeFresh in Hfresh. specialize (Hfresh Hindex).
  replace (Znth i edges (0, 0)) with
      (Znth i edges __default__Prod_Z_Z) in Hfresh.
  2:{ apply Znth_indep. exact Hindex. }
  rewrite Hedge_i in Hfresh. simpl in Hfresh.
  destruct Hfresh as [Huv _].
  apply (degree_prefix_extend__solver_build_step
    nv edges i degree_data_2 (Znth i eu_data 0) (Znth i ev_data 0)
    __default__Prod_Z_Z); try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH17 i ltac:(lia)).
  destruct PreH17 as [[[[[Hu0 Hun] Hv0] Hvn] Heu] Hev].
  pose proof PreH6 as Hpre.
  unfold Pre in Hpre. destruct Hpre as [_ Hgraph].
  unfold GraphPre in Hgraph. destruct Hgraph as [Htree _].
  unfold TreeInput in Htree. destruct Htree as [_ [Hedges _]].
  assert (Hindex : 0 <= i < Zlength edges) by lia.
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
    (rewrite Zlength_replace_Znth__solver_build_step; lia).
  assert (Hedge_i : Znth i edges __default__Prod_Z_Z =
      (Znth i eu_data 0 + 1, Znth i ev_data 0 + 1)).
  { destruct (Znth i edges __default__Prod_Z_Z) as [a b] eqn:Hedge.
    simpl in Heu, Hev. f_equal; lia. }
  apply (adjacency_build_extend__solver_build_step
    nv edges i head_data_2 to_done_2 next_done_2
    (Znth i eu_data 0) (Znth i ev_data 0) __default__Prod_Z_Z);
    try assumption; try lia.
  exact (PreH16 i).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_replace_Znth__solver_build_step.
  exact PreH13.
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
  repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
  rewrite Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_6 : solver_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Zlength_replace_Znth__solver_build_step.
  exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = nv - 1) by lia.
  assert (Hec : ec = 2 * nv - 2) by lia.
  pose proof PreH6 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as [_ Hgraph].
  assert (Hedges : Zlength edges = nv - 1).
  {
    unfold GraphPre in Hgraph.
    destruct Hgraph as [Htree _].
    unfold TreeInput in Htree. tauto.
  }
  assert (Hmodel :
    AdjacencyModel nv edges head_data_2 to_done next_done).
  {
    eapply adjacency_build_complete__solver_build_finish.
    - exact Hedges.
    - rewrite <- Hi. exact PreH14.
  }
  assert (Hdegree : DegreePrefix nv edges (nv - 1) degree_data_2).
  { rewrite <- Hi. exact PreH15. }
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 degree_data_2
    head_data_2 to_done next_done.
  split_pure_spatial.
  - rewrite Hec.
    rewrite !IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full to_p_2 0 (2 * nv - 2) to_done).
    replace (to_p_2 + 0 * sizeof (INT)) with to_p_2 by lia.
    replace (2 * nv - 2 - 0) with (2 * nv - 2) by lia.
    sep_apply_l_atomic
      (IntArray.seg_to_full next_p_2 0 (2 * nv - 2) next_done).
    replace (next_p_2 + 0 * sizeof (INT)) with next_p_2 by lia.
    replace (2 * nv - 2 - 0) with (2 * nv - 2) by lia.
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists deg_p_2 next_p_2 to_p_2 head_p_2
    degree_data_2 head_data_2 to_data_2 next_data_2
    parent_data dist_data.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_to_full_shape retval nv parent_data).
    sep_apply_l_atomic
      (IntArray.full_to_full_shape retval_2 nv dist_data).
    repeat cancel.
  - split_pures;
      dump_pre_spatial;
      try reflexivity;
      assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold BFSResult in PreH1.
  destruct PreH1 as [_ [Hbounds _]].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold BFSResult in PreH1.
  destruct PreH1 as [_ [Hbounds _]].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold BFSResult in PreH2.
  destruct PreH2 as [_ [Hbounds _]].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold BFSResult in PreH2.
  destruct PreH2 as [_ [Hbounds _]].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AncestorAfter.
  exists (b :: nil).
  simpl.
  repeat split; try reflexivity; try lia.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_2 : solver_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold DiameterDecision.
  left.
  split; [reflexivity | exact PreH1].
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AncestorAfter.
  exists (b :: nil).
  simpl.
  repeat split; try reflexivity; try lia.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_2 : solver_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold DiameterDecision.
  right.
  split; [reflexivity | exact PreH1].
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH4 as Hresult.
  unfold BFSResult in Hresult.
  destruct Hresult as [Hdata Hrest].
  unfold BFSData in Hdata.
  destruct Hdata as [Hparents_len Hdata].
  apply ancestor_after_extend__solver_bfs_pipeline.
  - lia.
  - rewrite Hparents_len. lia.
  - exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (ancestor_parent_bounds__solver_bfs_pipeline
    nv edges a second_parent_2 second_dist_2 b k_pre i center ok
    PreH4 PreH13 PreH2 PreH11 (conj PreH14 PreH1)
    (conj PreH16 PreH17) PreH18) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (ancestor_parent_bounds__solver_bfs_pipeline
    nv edges a second_parent_2 second_dist_2 b k_pre i center ok
    PreH4 PreH13 PreH2 PreH11 (conj PreH14 PreH1)
    (conj PreH16 PreH17) PreH18) as Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = k_pre) by lia.
  assert (Hok : ok = 1).
  {
    unfold DiameterDecision in PreH13.
    destruct PreH13 as [[Hzero _] | [Hone _]]; lia.
  }
  assert (Hdiam : Znth b second_dist_2 0 = 2 * k_pre).
  {
    unfold DiameterDecision in PreH13.
    destruct PreH13 as [[Hzero Hneq] | [Hone Heq]].
    - exfalso. apply PreH2. exact Hzero.
    - exact Heq.
  }
  assert (Hancestor : AncestorAfter second_parent_2 b k_pre center).
  { rewrite <- Hi. exact PreH18. }
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 degree_data_2
    head_data_2 to_data_2 next_data_2 second_parent_2 second_dist_2
    first_parent_2 first_dist_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_to_full_shape p nv second_parent_2).
    sep_apply_l_atomic
      (IntArray.full_to_full_shape d nv second_dist_2).
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsolver :
    SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center
      parent_data dist_data degree_data_2 0 ok).
  {
    unfold SolverDecision. right.
    split; [exact PreH16|].
    split; [exact PreH15|].
    split; [exact (proj1 PreH1)|].
    unfold DecisionPrefix. split.
    - right. exact PreH7.
    - split.
      + intros _. intros v Hv. lia.
      + intros _. exact PreH7.
  }
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 parent_data dist_data
    degree_data_2 head_data_2 to_data_2 next_data_2 second_parent_2
    second_dist_2 first_parent_2 first_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdiam : Znth b second_dist_2 0 <> 2 * k_pre).
  {
    unfold DiameterDecision in PreH12.
    destruct PreH12 as [[_ Hneq] | [Hone _]].
    - exact Hneq.
    - lia.
  }
  assert (Hsolver :
    SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center
      second_parent_2 second_dist_2 degree_data_2 0 ok).
  {
    unfold SolverDecision. left. split; assumption.
  }
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 second_parent_2
    second_dist_2 degree_data_2 head_data_2 to_data_2 next_data_2
    second_parent_2 second_dist_2 first_parent_2 first_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength d nv center_dist_2).
  Intros_p Hdistlen.
  assert (Hbad : ~ HedgehogVertexOK k_pre center v
    (Znth v center_dist_2 (-1)) (Znth v degree_data_2 0)).
  {
    unfold HedgehogVertexOK.
    intros [_ [Hleaf _]].
    apply PreH1.
    apply Hleaf.
    rewrite <- (Znth_indep center_dist_2 v 0 (-1)) by
      (rewrite Hdistlen; lia).
    exact PreH2.
  }
  pose proof (solver_decision_reject_next__solver_decision_reject
    nv k_pre edges second_parent_2 second_dist_2 b center
    center_parent_2 center_dist_2 degree_data_2 v ok
    PreH14 Hbad PreH16) as Hreject.
  Exists deg_p_2 next_p_2 to_p_2 head_p_2
    center_parent_2 center_dist_2 degree_data_2
    head_data_2 to_data_2 next_data_2
    second_parent_2 second_dist_2 first_parent_2 first_dist_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength d nv center_dist_2).
  Intros_p Hdistlen.
  rewrite (Znth_indep center_dist_2 v 0 (-1)) in PreH1 by
    (rewrite Hdistlen; lia).
  assert (Hbad : ~ HedgehogVertexOK k_pre center v
    (Znth v center_dist_2 (-1)) (Znth v degree_data_2 0)).
  {
    unfold HedgehogVertexOK.
    intros [Hdistance _].
    lia.
  }
  pose proof (solver_decision_reject_next__solver_decision_reject
    nv k_pre edges second_parent_2 second_dist_2 b center
    center_parent_2 center_dist_2 degree_data_2 v ok
    PreH12 Hbad PreH14) as Hreject.
  Exists deg_p_2 next_p_2 to_p_2 head_p_2
    center_parent_2 center_dist_2 degree_data_2
    head_data_2 to_data_2 next_data_2
    second_parent_2 second_dist_2 first_parent_2 first_dist_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength d nv center_dist_2).
  Intros_p Hdistlen.
  rewrite (Znth_indep center_dist_2 v 0 (-1)) in PreH3 by
    (rewrite Hdistlen; lia).
  subst v.
  assert (Hbad : ~ HedgehogVertexOK k_pre center center
    (Znth center center_dist_2 (-1)) (Znth center degree_data_2 0)).
  {
    unfold HedgehogVertexOK.
    intros [_ [_ Hinternal]].
    specialize (Hinternal PreH3).
    destruct Hinternal as [Hcenter _].
    specialize (Hcenter eq_refl).
    lia.
  }
  pose proof (solver_decision_reject_next__solver_decision_reject
    nv k_pre edges second_parent_2 second_dist_2 b center
    center_parent_2 center_dist_2 degree_data_2 center ok
    PreH16 Hbad PreH18) as Hreject.
  Exists deg_p_2 next_p_2 to_p_2 head_p_2
    center_parent_2 center_dist_2 degree_data_2
    head_data_2 to_data_2 next_data_2
    second_parent_2 second_dist_2 first_parent_2 first_dist_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 center_parent_2 center_dist_2
    degree_data_2 head_data_2 to_data_2 next_data_2 second_parent_2
    second_dist_2 first_parent_2 first_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    dump_pre_spatial.
    eapply solver_decision_advance_fail__solver_decision_accept; eauto.
    eapply hedgehog_internal_noncenter_failure__solver_decision_accept;
      eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_5 : solver_entail_wit_14_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 center_parent_2 center_dist_2
    degree_data_2 head_data_2 to_data_2 next_data_2 second_parent_2
    second_dist_2 first_parent_2 first_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    dump_pre_spatial.
    eapply solver_decision_advance_pass__solver_decision_accept; eauto.
    eapply hedgehog_internal_noncenter__solver_decision_accept; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_6 : solver_entail_wit_14_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 center_parent_2 center_dist_2
    degree_data_2 head_data_2 to_data_2 next_data_2 second_parent_2
    second_dist_2 first_parent_2 first_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    dump_pre_spatial.
    eapply solver_decision_advance_pass__solver_decision_accept; eauto.
    eapply hedgehog_internal_center__solver_decision_accept; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_7 : solver_entail_wit_14_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists deg_p_2 next_p_2 to_p_2 head_p_2 center_parent_2 center_dist_2
    degree_data_2 head_data_2 to_data_2 next_data_2 second_parent_2
    second_dist_2 first_parent_2 first_dist_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    dump_pre_spatial.
    eapply solver_decision_advance_pass__solver_decision_accept; eauto.
    eapply hedgehog_boundary_leaf__solver_decision_accept.
    + exact PreH3.
    + exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_15_1 : solver_entail_wit_15_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst ok.
  assert (Hdecision :
    SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center
      center_parent_2 center_dist_2 degree_data_2 nv 0).
  {
    unfold SolverDecision in *.
    destruct PreH12 as [Hreject | [Hdiam [Hancestor [Hcenter Hprefix]]]].
    - left. exact Hreject.
    - right.
      split; [exact Hdiam |].
      split; [exact Hancestor |].
      split; [exact Hcenter |].
      unfold DecisionPrefix in *.
      destruct Hprefix as [Hout Hiff].
      split.
      + left. reflexivity.
      + split.
        * lia.
        * intros Hall.
          exfalso.
          assert (0 = 1) as Hfalse.
          {
            apply Hiff.
            intros x Hx.
            apply Hall.
            lia.
          }
          lia.
  }
  assert (Hcertificate :
    SolverCertificate nv k_pre edges first_parent_2 first_dist_2 a
      second_parent_2 second_dist_2 b center center_parent_2 center_dist_2
      degree_data_2 0).
  {
    unfold SolverCertificate.
    split; [exact PreH2 |].
    split; [exact PreH3 |].
    split; [exact PreH8 | exact Hdecision].
  }
  assert (Hspec : Spec nv k_pre edges 0).
  {
    unfold Spec.
    split.
    - left. reflexivity.
    - split.
      + lia.
      + intros Hlayers.
        exfalso.
        pose proof (proj2 (proj2 PreH4) k_pre (conj PreH5 PreH6))
          as Hcomplete.
        specialize (Hcomplete
          first_parent_2 first_dist_2 a
          second_parent_2 second_dist_2 b center
          center_parent_2 center_dist_2 degree_data_2
          PreH2 PreH3 PreH8 Hdecision).
        exact (Hcomplete Hlayers).
  }
  Exists deg_p_2 next_p_2 to_p_2 head_p_2
    head_data_2 to_data_2 next_data_2
    first_parent_2 first_dist_2 second_parent_2 second_dist_2
    center_parent_2 center_dist_2 degree_data_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures;
      dump_pre_spatial;
      assumption.
Qed.

Lemma proof_of_solver_entail_wit_15_2 : solver_entail_wit_15_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = nv) as Hv by lia.
  subst v.
  unfold SolverDecision in PreH13.
  destruct PreH13 as [[Hout0 Hreject] |
    [Hdiam [Hancestor [Hcenter Hprefix]]]].
  - exfalso. apply PreH2. exact Hout0.
  - pose proof Hprefix as Hprefix_full.
    unfold DecisionPrefix in Hprefix.
    destruct Hprefix as [Hout Hiff].
    assert (ok = 1) as Hok by lia.
    subst ok.
    pose proof (proj1 Hiff eq_refl) as HallOK.
    pose proof Hcenter as Hcenter_data.
    unfold BFSData in Hcenter_data.
    destruct Hcenter_data as
      [Hparent_len [Hdist_len [Hcenter_bounds [Hparent_state Hdistance]]]].
    pose proof PreH9 as Hdegree_prefix.
    unfold DegreePrefix in Hdegree_prefix.
    destruct Hdegree_prefix as [Hdegree_len Hdegree].
    pose proof (proj1 (proj2 (proj1 PreH5))) as Hedges_len.
    assert (Hedges_full : sublist 0 (nv - 1) edges = edges).
    {
      rewrite <- Hedges_len.
      apply sublist_self.
      reflexivity.
    }
    assert (Hlayers : HedgehogLayers nv k_pre (center + 1) edges).
    {
      unfold HedgehogLayers.
      split.
      + lia.
      + intros vertex Hvertex.
        exists (Znth (vertex - 1) center_dist_2 (-1)).
        split.
        * pose proof (Hdistance (vertex - 1) ltac:(lia)) as Hvertex_distance.
          replace (vertex - 1 + 1) with vertex in Hvertex_distance by lia.
          exact Hvertex_distance.
        * specialize (HallOK (vertex - 1) ltac:(lia)).
          specialize (Hdegree (vertex - 1) ltac:(lia)).
          replace (vertex - 1 + 1) with vertex in Hdegree by lia.
          rewrite Hedges_full in Hdegree.
          rewrite <- Hdegree.
          replace (center + 1 - 1) with center by lia.
          exact HallOK.
    }
    assert (Hdecision :
      SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center
        center_parent_2 center_dist_2 degree_data_2 nv 1).
    {
      unfold SolverDecision.
      right.
      split; [exact Hdiam |].
      split; [exact Hancestor |].
      split; [exact Hcenter | exact Hprefix_full].
    }
    assert (Hcertificate :
      SolverCertificate nv k_pre edges first_parent_2 first_dist_2 a
        second_parent_2 second_dist_2 b center center_parent_2 center_dist_2
        degree_data_2 1).
    {
      unfold SolverCertificate.
      split; [exact PreH3 |].
      split; [exact PreH4 |].
      split; [exact PreH9 | exact Hdecision].
    }
    assert (Hspec : Spec nv k_pre edges 1).
    {
      unfold Spec.
      split.
      + right. reflexivity.
      + split.
        * intros _. exists (center + 1). exact Hlayers.
        * intros _. reflexivity.
    }
    Exists deg_p_2 next_p_2 to_p_2 head_p_2
      head_data_2 to_data_2 next_data_2
      first_parent_2 first_dist_2 second_parent_2 second_dist_2
      center_parent_2 center_dist_2 degree_data_2.
    split_pure_spatial.
    + repeat cancel.
    + split_pures;
        dump_pre_spatial;
        assumption.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GraphPre in PreH4.
  destruct PreH4 as [Htree _].
  unfold TreeInput in Htree.
  destruct Htree as [_ [Hlength _]].
  rewrite Hlength.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_1 : solver_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold BFSResult in PreH11.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_2 : solver_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold BFSResult in PreH11.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_34_pure_split_goal_1 : solver_partial_solve_wit_34_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold GraphPre, TreeInput in PreH18.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_34_pure_split_goal_2 : solver_partial_solve_wit_34_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength head_p nv head_data).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_34_pure : solver_partial_solve_wit_34_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_34_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_34_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_35_pure_split_goal_1 : solver_partial_solve_wit_35_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold GraphPre, TreeInput in PreH18.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_35_pure_split_goal_2 : solver_partial_solve_wit_35_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength to_p ((2 * nv) - 2) to_data).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_35_pure : solver_partial_solve_wit_35_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_35_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_35_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_36_pure_split_goal_1 : solver_partial_solve_wit_36_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold GraphPre, TreeInput in PreH18.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_36_pure_split_goal_2 : solver_partial_solve_wit_36_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength next_p ((2 * nv) - 2) next_data).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_36_pure : solver_partial_solve_wit_36_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_36_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_36_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_37_pure_split_goal_1 : solver_partial_solve_wit_37_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength deg_p nv degree_data).
  Intros_p Hlen.
  dump_pre_spatial.
  rewrite <- Hlen.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_partial_solve_wit_37_pure_split_goal_2 : solver_partial_solve_wit_37_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength deg_p nv degree_data).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_37_pure : solver_partial_solve_wit_37_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_37_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_37_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_38_pure_split_goal_1 : solver_partial_solve_wit_38_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength p nv center_parent).
  Intros_p Hlen.
  dump_pre_spatial.
  rewrite <- Hlen.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_partial_solve_wit_38_pure_split_goal_2 : solver_partial_solve_wit_38_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength p nv center_parent).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_38_pure : solver_partial_solve_wit_38_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_38_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_38_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_39_pure_split_goal_1 : solver_partial_solve_wit_39_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength d nv center_dist).
  Intros_p Hlen.
  dump_pre_spatial.
  rewrite <- Hlen.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_partial_solve_wit_39_pure_split_goal_2 : solver_partial_solve_wit_39_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength d nv center_dist).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_39_pure : solver_partial_solve_wit_39_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_39_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_39_pure_split_goal_2.
Qed.
