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
Require Import stock_trading_goal.
Require Import stock_trading_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib.
Local Open Scope sac.

(* Split from stock_trading_proof_manual.v, part 2 of 5. *)
Lemma proof_of_maximum_profit_entail_wit_13_1 : maximum_profit_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (value := (- j) * ask_price).
  set (row' := replace_Znth j value (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l. split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + i * width * sizeof (INT)) j width value
      (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr : dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr. sep_apply Hrowmerge; try lia. fold row'.
    change (IntArray.full (dp_pre + i * width * sizeof (INT)) width row')
      with (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_pre width i) width row').
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre i (days_pre + 1) width dp_l_2 row') as Htablemerge.
    sep_apply Htablemerge; try lia.
    fold dp_l. cancel.
  - assert (Hcur : 0 <= i < Zlength dp_l_2).
    { unfold StockTableShape in PreH24. destruct PreH24 as [Hlen _]. lia. }
    assert (Hroweq : row' = replace_Znth j value (Znth i dp_l_2 nil)).
    { unfold row'. rewrite (Znth_indep dp_l_2 i __default__List_Z nil)
        by exact Hcur. reflexivity. }
    pose proof PreH23 as Hprogress.
    unfold StockEarlyBuyProgress in Hprogress.
    destruct Hprogress as [Hdone [Hday [Hnext [Hzero Hcells]]]].
    specialize (Hcells j ltac:(lia)). destruct (Z_lt_dec j j); [lia |].
    rewrite <- (same_index_different_default i dp_l_2 __default__List_Z Hcur)
      in PreH1.
    assert (Hmax : value = Z.max (Znth j (Znth (i - 1) dp_l_2 nil) 0)
      (- j * Znth (i - 1) ap_l 0)).
    { unfold value. subst ask_price. rewrite <- Hcells. symmetry.
      apply Z.max_r. lia. }
    pose proof (stock_early_buy_update_step__early_buy
      ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre
      i j value days_pre PreH22 PreH23 ltac:(lia) ltac:(lia) Hmax) as Hstep.
    simpl in Hstep. rewrite <- Hroweq in Hstep.
    change (StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre
      wait_days_pre i (j + 1) /\ StockTableShape dp_l days_pre max_stock_pre)
      in Hstep.
    destruct Hstep as [Hprogress' Hshape']. split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_2 : maximum_profit_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (value := Znth j (Znth i dp_l_2 __default__List_Z) 0).
  set (row' := replace_Znth j value (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l. split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + i * width * sizeof (INT)) j width value
      (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr : dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr. sep_apply Hrowmerge; try lia. fold row'.
    change (IntArray.full (dp_pre + i * width * sizeof (INT)) width row')
      with (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_pre width i) width row').
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre i (days_pre + 1) width dp_l_2 row') as Htablemerge.
    sep_apply Htablemerge; try lia.
    fold dp_l. cancel.
  - assert (Hcur : 0 <= i < Zlength dp_l_2).
    { unfold StockTableShape in PreH24. destruct PreH24 as [Hlen _]. lia. }
    assert (Hroweq : row' = replace_Znth j value (Znth i dp_l_2 nil)).
    { unfold row'. rewrite (Znth_indep dp_l_2 i __default__List_Z nil)
        by exact Hcur. reflexivity. }
    pose proof PreH23 as Hprogress.
    unfold StockEarlyBuyProgress in Hprogress.
    destruct Hprogress as [Hdone [Hday [Hnext [Hzero Hcells]]]].
    specialize (Hcells j ltac:(lia)). destruct (Z_lt_dec j j); [lia |].
    rewrite <- (same_index_different_default i dp_l_2 __default__List_Z Hcur)
      in PreH1.
    assert (Hmax : value = Z.max (Znth j (Znth (i - 1) dp_l_2 nil) 0)
      (- j * Znth (i - 1) ap_l 0)).
    { unfold value.
      rewrite <- (same_index_different_default i dp_l_2 __default__List_Z Hcur).
      subst ask_price. rewrite Hcells. symmetry. apply Z.max_l. lia. }
    pose proof (stock_early_buy_update_step__early_buy
      ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre
      i j value days_pre PreH22 PreH23 ltac:(lia) ltac:(lia) Hmax) as Hstep.
    simpl in Hstep. rewrite <- Hroweq in Hstep.
    change (StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre
      wait_days_pre i (j + 1) /\ StockTableShape dp_l days_pre max_stock_pre)
      in Hstep.
    destruct Hstep as [Hprogress' Hshape']. split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_14_split_goal_1 :
  maximum_profit_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HDone :
    StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre
      wait_days_pre (i + 1)).
  { eapply stock_early_buy_complete__early_buy; eauto; lia. }
  exact HDone.
Qed.

Lemma proof_of_maximum_profit_entail_wit_14 : maximum_profit_entail_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_1 :
  maximum_profit_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellQueue.
  split; [lia |].
  split.
  - intros pos Hpos; lia.
  - split.
    + intros left right Hlr; lia.
    + intros candidate Hcandidate.
      unfold StockFiniteIndexInWindow in Hcandidate.
      destruct Hcandidate as [_ [Hcandlen [_ [Hcandlow _]]]].
      unfold StockTableShape in PreH17.
      destruct PreH17 as [_ Hrows].
      specialize (Hrows (i - wait_days_pre - 1) ltac:(lia)).
      lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_2 :
  maximum_profit_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH15 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [Hasklen _].
  unfold StockCopyProgress in PreH16.
  destruct PreH16 as [Hdone [Hday [Hcol Hcells]]].
  unfold StockSellProgress.
  split; [exact Hdone |].
  split; [rewrite Hasklen; lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split.
  - intros stock Hstock; apply Hcells; lia.
  - split.
    + intros stock Hstock; lia.
    + apply Hcells; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_3 :
  maximum_profit_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [_ [_ [_ Hsellbounds]]]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_4 :
  maximum_profit_entail_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [_ [_ [_ Hsellbounds]]]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_5 :
  maximum_profit_entail_wit_15_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [[Hbidlo Hbidle] [Hask1000 _]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_6 :
  maximum_profit_entail_wit_15_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [[Hbidlo Hbidle] _].
  exact Hbidlo.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15 : maximum_profit_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_6.
Qed.

Lemma proof_of_maximum_profit_entail_wit_16_split_goal_1 :
  maximum_profit_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hexp :
    StockSellQueueExpiring dp_l_2 queue_l_2 source_day bid_price
      (j + 2) (j + sell_cap) head tail).
  { unfold StockSellQueueExpiring. left.
    replace (j + sell_cap + 1) with ((j + sell_cap) + 1) by lia.
    exact PreH29. }
  rewrite <- PreH13. exact Hexp.
Qed.

Lemma proof_of_maximum_profit_entail_wit_16 : maximum_profit_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_16_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_17_split_goal_1 :
  maximum_profit_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hexpired : Znth head queue_l_2 0 > j + sell_cap) by lia.
  assert (Hqueue :
    StockSellQueue dp_l_2 queue_l_2 source_day bid_price
      (j + 2) (j + sell_cap) (head + 1) tail).
  { eapply StockSellQueue_drop_expired__sell_expire; eauto. }
  assert (Hexp :
    StockSellQueueExpiring dp_l_2 queue_l_2 source_day bid_price
      (j + 2) (j + sell_cap) (head + 1) tail).
  { unfold StockSellQueueExpiring. right. exact Hqueue. }
  rewrite <- PreH14. exact Hexp.
Qed.

Lemma proof_of_maximum_profit_entail_wit_17 : maximum_profit_entail_wit_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_17_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_1_split_goal_1 :
  maximum_profit_entail_wit_18_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hqueue :
    StockSellQueue dp_l_2 queue_l_2 source_day bid_price
      (j + 2) (j + sell_cap) head tail).
  { eapply StockSellQueueExpiring_empty__sell_expire; eauto. }
  rewrite <- PreH13. exact Hqueue.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_1 : maximum_profit_entail_wit_18_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_18_1_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_2_split_goal_1 :
  maximum_profit_entail_wit_18_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hhead_upper : Znth head queue_l_2 0 <= j + sell_cap) by lia.
  assert (Hqueue :
    StockSellQueue dp_l_2 queue_l_2 source_day bid_price
      (j + 2) (j + sell_cap) head tail).
  { eapply StockSellQueueExpiring_head_bounded__sell_expire; eauto. }
  rewrite <- PreH14. exact Hqueue.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_2_split_goal_2 :
  maximum_profit_entail_wit_18_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hhead_upper : Znth head queue_l_2 0 <= j + sell_cap) by lia.
  assert (Hqueue :
    StockSellQueue dp_l_2 queue_l_2 source_day bid_price
      (j + 2) (j + sell_cap) head tail).
  { eapply StockSellQueueExpiring_head_bounded__sell_expire; eauto. }
  assert (Hhead_lower : j <= Znth head queue_l_2 0).
  { unfold StockSellQueue in Hqueue.
    destruct Hqueue as [_ [Helems _]].
    specialize (Helems head ltac:(lia)).
    destruct Helems as [_ [_ [_ [Hlower _]]]].
    lia. }
  exact Hhead_lower.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_2 : maximum_profit_entail_wit_18_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_18_2_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_18_2_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_entail_wit_19_1 : maximum_profit_entail_wit_19_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l dp_l.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + source_day * width * sizeof ( INT )) (j + 1) width
    (Znth (j + 1) (Znth source_day dp_l __default__List_Z) 0)
    (Znth source_day dp_l __default__List_Z)) as Hcell.
  assert (Haddr :
    dp_pre + source_day * width * sizeof ( INT ) + (j + 1) * sizeof ( INT ) =
    dp_pre + (source_day * width + (j + 1)) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre source_day (days_pre + 1) width dp_l
    (Znth source_day dp_l __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre width source_day) width
    (Znth source_day dp_l __default__List_Z)) with
    (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
      width (Znth source_day dp_l __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  - unfold StockSellQueue in PreH30.
    destruct PreH30 as [_ [Hvalid _]].
    specialize (Hvalid (tail - 1) ltac:(lia)).
    unfold StockFiniteIndexInWindow in Hvalid.
    destruct Hvalid as [Hnonneg _].
    exact Hnonneg.
  - unfold StockSellQueue in PreH30.
    destruct PreH30 as [_ [Hvalid _]].
    specialize (Hvalid (tail - 1) ltac:(lia)).
    unfold StockFiniteIndexInWindow in Hvalid.
    destruct Hvalid as [_ [Hlt _]].
    unfold StockTableShape in PreH31.
    destruct PreH31 as [_ Hrows].
    specialize (Hrows source_day ltac:(lia)).
    rewrite Hrows in Hlt. lia.
  - eapply StockSellQueue_begin_popping__sell_pop_append.
    + lia.
    + unfold StockTableShape in PreH31.
      destruct PreH31 as [_ Hrows].
      specialize (Hrows source_day ltac:(lia)).
      rewrite Hrows. lia.
    + assert (Hsource_len : 0 <= source_day < Zlength dp_l).
      { unfold StockTableShape in PreH31.
        destruct PreH31 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (same_index_different_default source_day dp_l
        __default__List_Z Hsource_len).
      unfold STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
    + replace (j + 1 + 1) with (j + 2) by lia.
      exact PreH30.
  - intros pos Hpos.
    unfold StockSellQueue in PreH30.
    destruct PreH30 as [_ [Hvalid _]].
    specialize (Hvalid pos Hpos).
    unfold StockFiniteIndexInWindow in Hvalid.
    destruct Hvalid as [Hnonneg [Hlt _]].
    unfold StockTableShape in PreH31.
    destruct PreH31 as [_ Hrows].
    specialize (Hrows source_day ltac:(lia)).
    rewrite Hrows in Hlt.
    lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_19_2 : maximum_profit_entail_wit_19_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre source_day (days_pre + 1) width dp_l
    (Znth source_day dp_l __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre width source_day) width
    (Znth source_day dp_l __default__List_Z)) with
    (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
      width (Znth source_day dp_l __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + source_day * width * sizeof ( INT )) (j + 1) width
    (Znth (j + 1) (Znth source_day dp_l __default__List_Z) 0)
    (Znth source_day dp_l __default__List_Z)) as Hcell.
  assert (Haddr :
    dp_pre + source_day * width * sizeof ( INT ) + (j + 1) * sizeof ( INT ) =
    dp_pre + (source_day * width + (j + 1)) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  eapply StockSellQueue_begin_popping__sell_pop_append.
  - lia.
  - unfold StockTableShape in PreH31.
    destruct PreH31 as [_ Hrows].
    specialize (Hrows source_day ltac:(lia)).
    rewrite Hrows. lia.
  - assert (Hsource_len : 0 <= source_day < Zlength dp_l).
    { unfold StockTableShape in PreH31.
      destruct PreH31 as [Hlen _]. rewrite Hlen. lia. }
    rewrite (same_index_different_default source_day dp_l
      __default__List_Z Hsource_len).
    unfold STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
  - replace (j + 1 + 1) with (j + 2) by lia.
    exact PreH30.
  all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_20_1 : maximum_profit_entail_wit_20_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre source_day (days_pre + 1) width dp_l_2
    (Znth source_day dp_l_2 __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre width source_day) width
    (Znth source_day dp_l_2 __default__List_Z)) with
    (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
      width (Znth source_day dp_l_2 __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + source_day * width * sizeof ( INT )) last_index width
    (Znth last_index (Znth source_day dp_l_2 __default__List_Z) 0)
    (Znth source_day dp_l_2 __default__List_Z)) as Hcell.
  assert (Haddr :
    dp_pre + source_day * width * sizeof ( INT ) + last_index * sizeof ( INT ) =
    dp_pre + (source_day * width + last_index) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  - pose proof (PreH32 (tail - 1 - 1) ltac:(lia)). lia.
  - pose proof (PreH32 (tail - 1 - 1) ltac:(lia)). lia.
  - eapply StockSellQueuePopping_drop_tail__sell_pop_append.
    + exact PreH31.
    + lia.
    + unfold StockSellScore.
      rewrite <- (PreH28 ltac:(lia)).
      assert (Hsource_len : 0 <= source_day < Zlength dp_l_2).
      { unfold StockTableShape in PreH33.
        destruct PreH33 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (same_index_different_default source_day dp_l_2
        __default__List_Z Hsource_len).
      rewrite PreH27 in PreH2. exact PreH2.
  - intros pos Hpos. apply PreH32. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_20_2 : maximum_profit_entail_wit_20_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre source_day (days_pre + 1) width dp_l_2
    (Znth source_day dp_l_2 __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre width source_day) width
    (Znth source_day dp_l_2 __default__List_Z)) with
    (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
      width (Znth source_day dp_l_2 __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + source_day * width * sizeof ( INT )) last_index width
    (Znth last_index (Znth source_day dp_l_2 __default__List_Z) 0)
    (Znth source_day dp_l_2 __default__List_Z)) as Hcell.
  assert (Haddr :
    dp_pre + source_day * width * sizeof ( INT ) + last_index * sizeof ( INT ) =
    dp_pre + (source_day * width + last_index) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  eapply StockSellQueuePopping_drop_tail__sell_pop_append.
  - exact PreH31.
  - lia.
  - unfold StockSellScore.
    rewrite <- (PreH28 ltac:(lia)).
    assert (Hsource_len : 0 <= source_day < Zlength dp_l_2).
    { unfold StockTableShape in PreH33.
      destruct PreH33 as [Hlen _]. rewrite Hlen. lia. }
    rewrite (same_index_different_default source_day dp_l_2
      __default__List_Z Hsource_len).
    rewrite PreH27 in PreH2. exact PreH2.
  all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_1 : maximum_profit_entail_wit_21_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength queue_index_pre width queue_l_2);
    Intros_p Hqueue_len.
  assert (HPending : StockSellQueuePending dp_l_2 queue_l_2 source_day
      bid_price (j + 1) (j + sell_cap) head tail).
  { unfold StockSellQueuePending.
    split; [exact PreH29|].
    split; [lia|].
    intros. lia. }
  Exists dp_l_2 queue_l_2.
  split_pure_spatial.
  - cancel (IntArray.full queue_index_pre width queue_l_2).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_2 : maximum_profit_entail_wit_21_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength queue_index_pre width queue_l_2);
    Intros_p Hqueue_len.
  assert (HPending : StockSellQueuePending dp_l_2 queue_l_2 source_day
      bid_price (j + 1) (j + sell_cap) head tail).
  { unfold StockSellQueuePending. split.
    - exact PreH30.
    - split; [lia|].
      intros Hht. unfold StockSellScore.
      rewrite <- (PreH27 Hht).
      assert (Hsource_len : 0 <= source_day < Zlength dp_l_2).
      { unfold StockTableShape in PreH32.
        destruct PreH32 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (same_index_different_default source_day dp_l_2
        __default__List_Z Hsource_len).
      rewrite PreH26 in PreH1. lia. }
  Exists dp_l_2 queue_l_2.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre source_day (days_pre + 1) width dp_l_2
    (Znth source_day dp_l_2 __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre width source_day) width
    (Znth source_day dp_l_2 __default__List_Z)) with
    (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
      width (Znth source_day dp_l_2 __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + source_day * width * sizeof ( INT )) last_index width
    (Znth last_index (Znth source_day dp_l_2 __default__List_Z) 0)
    (Znth source_day dp_l_2 __default__List_Z)) as Hcell.
  assert (Haddr :
    dp_pre + source_day * width * sizeof ( INT ) + last_index * sizeof ( INT ) =
    dp_pre + (source_day * width + last_index) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_22_split_goal_1 :
  maximum_profit_entail_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH23 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hvalues]]]]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [_ [_ [_ Hsell]]].
  rewrite <- PreH14 in Hsell.
  assert (Hiu : j + 1 <= j + sell_cap) by lia.
  apply StockSellQueuePending_append__sell_pop_append.
  - exact Hiu.
  - exact PreH25.
Qed.

Lemma proof_of_maximum_profit_entail_wit_22 : maximum_profit_entail_wit_22.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_22_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_1_split_goal_1 :
  maximum_profit_entail_wit_23_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellProgress in PreH21.
  destruct PreH21 as [_ [_ [Hsource [Hsrange _]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_1 : maximum_profit_entail_wit_23_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_23_1_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_2 : maximum_profit_entail_wit_23_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + source_day * width * sizeof (INT)) (j + 1) width
         (Znth (j + 1) (Znth source_day dp_l_2 __default__List_Z) 0)
         (Znth source_day dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + source_day * width * sizeof (INT) + (j + 1) * sizeof (INT) =
      dp_pre + (source_day * width + (j + 1)) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    pose proof
      (IntArray2.missing_i_merge_to_full
         dp_pre source_day (days_pre + 1) width dp_l_2
         (Znth source_day dp_l_2 __default__List_Z)) as Htablemerge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_pre width source_day) width
         (Znth source_day dp_l_2 __default__List_Z))
      with
      (IntArray.full
         (dp_pre + source_day * width * sizeof (INT)) width
         (Znth source_day dp_l_2 __default__List_Z))
      in Htablemerge.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - eapply stock_sell_queue_extend_lower_neg_inf__sell_cell_progress.
    + assert (Hsrc : 0 <= source_day < Zlength dp_l_2).
      { unfold StockTableShape in PreH30. lia. }
      rewrite <- (same_index_different_default source_day dp_l_2
        __default__List_Z Hsrc) in PreH1.
      unfold STOCK_NEG_INF. lia.
    + replace (j + 1 + 1) with (j + 2) by lia.
      exact PreH29.
Qed.

Lemma proof_of_maximum_profit_entail_wit_24_split_goal_1 :
  maximum_profit_entail_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellQueue in PreH24.
  destruct PreH24 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  destruct Hentries as [_ [Hrow [_ Hbounds]]].
  unfold StockTableShape in PreH25.
  destruct PreH25 as [_ Hshape].
  specialize (Hshape source_day ltac:(lia)).
  rewrite Hshape in Hrow.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_24_split_goal_2 :
  maximum_profit_entail_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellQueue in PreH24.
  destruct PreH24 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  destruct Hentries as [Hidx _].
  exact Hidx.
Qed.

Lemma proof_of_maximum_profit_entail_wit_24_split_goal_3 :
  maximum_profit_entail_wit_24_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbid [Hask _]].
  rewrite <- PreH17 in Hbid.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_24_split_goal_4 :
  maximum_profit_entail_wit_24_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbid _].
  rewrite <- PreH17 in Hbid.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_24 : maximum_profit_entail_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_24_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_24_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_24_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_24_split_goal_4.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25 : maximum_profit_entail_wit_25.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists dp_l queue_l_2.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof
    (IntArray.missing_i_merge_to_full
       (dp_pre + source_day * width * sizeof (INT)) best_index width
       (Znth best_index (Znth source_day dp_l __default__List_Z) 0)
       (Znth source_day dp_l __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    dp_pre + source_day * width * sizeof (INT) + best_index * sizeof (INT) =
    dp_pre + (source_day * width + best_index) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       dp_pre source_day (days_pre + 1) width dp_l
       (Znth source_day dp_l __default__List_Z)) as Htablemerge.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr dp_pre width source_day) width
       (Znth source_day dp_l __default__List_Z))
    with
    (IntArray.full
       (dp_pre + source_day * width * sizeof (INT)) width
       (Znth source_day dp_l __default__List_Z))
    in Htablemerge.
  sep_apply Htablemerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

