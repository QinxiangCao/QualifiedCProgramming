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
From SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum Require Import sliding_window_maximum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib.
Local Open Scope sac.

Lemma proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1.
Proof.
  pre_process.
  Exists nil.
  Exists q0.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.full q_pre n_pre q0).
    sep_apply (IntArray.undef_full_split_to_undef_seg out_pre 0 (n_pre - k_pre + 1)).
    + cancel (IntArray.undef_seg out_pre 0 (n_pre - k_pre + 1)).
      rewrite (IntArray.undef_seg_empty out_pre 0).
      rewrite (IntArray.seg_empty out_pre 0 0).
      entailer!.
    + lia.
  - entailer!.
    + unfold SWMQueueState, SWMQueueEntriesValid, SWMQueueIndexIncreasing,
        SWMQueueValueDecreasing, SWMQueueCoversWindow.
      repeat split; intros; try lia.
    + unfold SWMOutputPrefix.
      repeat split; try lia; simpl; intros; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + unfold SWMQueueState in PreH18.
      destruct PreH18 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      intros p r Hp. apply Hdec. lia.
    + unfold SWMQueueState in PreH18.
      destruct PreH18 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      intros p r Hp. apply Hinc. lia.
    + unfold SWMQueueState in PreH18.
      destruct PreH18 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      intros pos Hpos.
      unfold SWMQueueEntriesValid in Hvalid.
      specialize (Hvalid pos Hpos) as (? & ? & ?). lia.
    + unfold SWMQueueState in PreH18.
      unfold SWMQueueDropLoopState.
      destruct PreH18 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      repeat split; try lia; try assumption.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueCoversAfterDrop.
        intros idx Hidx0 HidxLen Hrange.
        unfold SWMQueueCoversWindow in Hcover.
        apply Hcover; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + intros p r Hp. apply PreH22. lia.
    + intros p r Hp. apply PreH21. lia.
    + intros pos Hpos. apply PreH20. lia.
    + intros pos Hpos. apply PreH19. lia.
    + unfold SWMQueueDropLoopState in *.
      destruct PreH18 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover).
      repeat split; try lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueIndexIncreasing in *.
        intros p r Hp. apply Hinc. lia.
      * unfold SWMQueueValueDecreasing in *.
        intros p r Hp. apply Hdec. lia.
      * unfold SWMQueueCoversAfterDrop in *.
        intros idx Hidx0 HidxLen Hrange.
        destruct (Hcover idx Hidx0 HidxLen Hrange) as
          [pos0 [[HposHead HposTail] [HidxLe [HposI Hval]]]].
        assert (pos0 <> head) by (intro Heq; subst; lia).
        exists pos0. repeat split; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    unfold SWMQueueDropLoopState in PreH18.
    destruct PreH18 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
      HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover).
    assert (HvalidAfter :
      SWMQueueEntriesValidAfterDrop l q_l_2 head tail i k_pre).
    {
      unfold SWMQueueEntriesValidAfterDrop.
      intros pos Hpos.
      unfold SWMQueueEntriesValid in Hvalid.
      specialize (Hvalid pos Hpos) as (Hpos0 & HposLen & HposLeft & HposI).
      repeat split; try lia.
      destruct (Z.eq_dec pos head) as [-> | Hneq].
      * lia.
      * unfold SWMQueueIndexIncreasing in Hinc.
        specialize (Hinc head pos ltac:(lia)). lia.
    }
    assert (Hdrop : SWMQueueAfterDrop l q_l_2 head tail i k_pre).
    {
      unfold SWMQueueAfterDrop.
      exact (conj HK1 (conj HK2 (conj HI0 (conj HIle (conj HH0
        (conj HHtail (conj HtailLen (conj HtailI (conj HvalidAfter
        (conj Hinc (conj Hdec Hcover))))))))))).
    }
    assert (Hdroploop : SWMQueueDropLoopState l q_l_2 head tail i k_pre).
    {
      unfold SWMQueueDropLoopState.
      exact (conj HK1 (conj HK2 (conj HI0 (conj HIle (conj HH0
        (conj HHtail (conj HtailLen (conj HtailI (conj Hvalid
        (conj Hinc (conj Hdec Hcover))))))))))).
    }
    unfold SWMQueueAfterDrop, SWMQueueDropLoopState.
    repeat split; try lia; try assumption.
    + unfold SWMQueueEntriesValidAfterDrop in HvalidAfter.
      assert (HposRange : head <= pos_2 < tail) by lia.
      specialize (HvalidAfter pos_2 HposRange) as (_ & _ & ? & _). lia.
    + unfold SWMQueueEntriesValidAfterDrop in HvalidAfter.
      assert (HposRange : head <= pos_2 < tail) by lia.
      specialize (HvalidAfter pos_2 HposRange) as (_ & _ & _ & ?). lia.
    + intro.
      specialize (PreH19 (tail - 1) ltac:(lia)) as (? & ?).
      lia.
    + unfold SWMQueueAfterDrop, SWMQueueDropLoopState in *.
      destruct PreH18 as (HK1' & HK2' & HI0' & HIle' & HH0' & HHtail' &
        HtailLen' & HtailI' & Hvalid' & Hinc' & Hdec' & Hcover').
      assert (HvalidAfter' :
        SWMQueueEntriesValidAfterDrop l q_l_2 head tail i k_pre).
      {
        unfold SWMQueueEntriesValidAfterDrop.
        intros pos Hpos.
        unfold SWMQueueEntriesValid in Hvalid'.
        specialize (Hvalid' pos Hpos) as (Hpos0 & HposLen & HposLeft & HposI).
        repeat split; try lia.
        destruct (Z.eq_dec pos head) as [-> | Hneq].
        - lia.
        - unfold SWMQueueIndexIncreasing in Hinc'.
          specialize (Hinc' head pos ltac:(lia)). lia.
      }
      exact (conj HK1' (conj HK2' (conj HI0' (conj HIle' (conj HH0'
        (conj HHtail' (conj HtailLen' (conj HtailI' (conj HvalidAfter'
        (conj Hinc' (conj Hdec' Hcover'))))))))))).
    Unshelve.
    all: try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    unfold SWMQueueAfterDrop, SWMQueueDropLoopState in *.
    destruct PreH17 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
      HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover).
    assert (HvalidAfter :
      SWMQueueEntriesValidAfterDrop l q_l_2 head tail i k_pre).
    {
      unfold SWMQueueEntriesValidAfterDrop.
      intros pos Hpos. lia.
    }
    exact (conj HK1 (conj HK2 (conj HI0 (conj HIle (conj HH0
      (conj HHtail (conj HtailLen (conj HtailI (conj HvalidAfter
      (conj Hinc (conj Hdec Hcover))))))))))).
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
    cancel (IntArray.full q_pre n_pre q_l_2).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial;
                  eapply SWMQueueAfterDrop_to_PendingState; eauto;
                  rewrite PreH4; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.full q_pre n_pre q_l_2).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial;
                  eapply SWMQueuePendingState_pop_back_dominated; eauto
                | dump_pre_spatial; intros;
                  specialize (PreH19 (tail - 1 - 1) ltac:(lia)); lia
                | dump_pre_spatial; intros; eapply PreH19; lia
                | dump_pre_spatial; intros; eapply PreH21; lia
                | dump_pre_spatial; intros; eapply PreH22; lia
                | dump_pre_spatial; intros; eapply PreH23; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
    cancel (IntArray.full q_pre n_pre q_l_2).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial; intros; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.full q_pre n_pre q_l_2).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8.
Proof.
  pre_process.
  Exists out_l_2. Exists (replace_Znth tail i q_l_2).
  split_pure_spatial.
  - cancel (IntArray.full q_pre n_pre (replace_Znth tail i q_l_2)).
    cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
  - assert (Hpush :
        SWMQueueState l (replace_Znth tail i q_l_2) head (tail + 1) (i + 1) k_pre).
    {
      eapply SWMQueuePendingState_push_current; eauto.
      - rewrite PreH5, PreH4. reflexivity.
      - rewrite PreH4. lia.
    }
    pose proof Hpush as Hpush_components.
    unfold SWMQueueState in Hpush_components.
    destruct Hpush_components as
      [_ [_ [_ [_ [_ [_ [_ [_ [Hnew_valid _]]]]]]]]].
    split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial; rewrite Zlength_replace_Znth; eauto
                | dump_pre_spatial; exact Hpush
                | dump_pre_spatial; intros pos Hpos;
                  specialize (Hnew_valid pos Hpos); rewrite PreH4 in Hnew_valid; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + replace (i - k_pre + 1) with (i + 1 - k_pre) by lia.
      eapply SWMQueueState_window_max; [exact PreH17 | exact PreH10 | lia].
    + destruct (PreH18 head ltac:(lia)) as [_ Hq]; exact Hq.
    + destruct (PreH18 head ltac:(lia)) as [Hq _]; exact Hq.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10.
Proof.
  pre_process.
  Exists (out_l_2 ++ Znth (Znth head q_l_2 0) l 0 :: nil). Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    apply SWMOutputPrefix_snoc; [exact PreH17 | lia |].
    replace out_idx with (i - k_pre + 1) by lia.
    replace (i - k_pre + 1 + k_pre) with (i + 1) by lia.
    exact PreH20.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_11_1 : maxSlidingWindow_entail_wit_11_1.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_11_2 : maxSlidingWindow_entail_wit_11_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - assert (Hi : i = n_pre) by lia; subst i.
    assert (Houtidx : out_idx = n_pre - k_pre + 1) by (apply PreH15; lia).
    rewrite Houtidx.
    repeat cancel.
    unfold IntArray.full, IntArray.seg, IntArray.undef_seg.
    replace (Z.to_nat (n_pre - k_pre + 1 - (n_pre - k_pre + 1))) with O by lia.
    simpl; entailer!.
  - entailer!.
    apply SWMOutputPrefix_complete with (out_idx := out_idx).
    + exact PreH17.
    + rewrite PreH5.
      assert (Hi : i = n_pre) by lia; subst i.
      apply PreH15; lia.
Qed.
