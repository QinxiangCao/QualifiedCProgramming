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

(* Split from stock_trading_proof_manual.v, part 4 of 5. *)
Lemma proof_of_maximum_profit_entail_wit_27_split_goal_1 :
  maximum_profit_entail_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyQueue.
  split; [lia |].
  split.
  - intros pos Hpos. lia.
  - split.
    + intros left right Hpositions. lia.
    + intros candidate Hcandidate.
      unfold StockFiniteIndexInWindow in Hcandidate.
      destruct Hcandidate as [Hnonneg [_ [_ [_ Hupper]]]].
      lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27_split_goal_2 :
  maximum_profit_entail_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellProgress in PreH28.
  destruct PreH28 as [Hdone [Hday [Hsource [Hsrange
    [Hjrange [Hcopy [Hsell Hmaxeq]]]]]]].
  unfold StockBuyProgress.
  split; [exact Hdone |].
  split; [exact Hday |].
  split; [reflexivity |].
  split; [rewrite <- Hsource; exact Hsrange |].
  split; [lia |].
  split.
  - intros stock Hstock.
    assert (stock = 0) by lia. subst stock.
    pose proof (Hsell 0 ltac:(lia)) as Hsell0.
    rewrite Hsource in Hsell0.
    unfold StockBuyCellValue, StockBuyCandidate.
    split.
    + split.
      * exists 0. left. split; [lia | exact Hsell0].
      * intros amount candidate Hcandidate.
        destruct Hcandidate as [[Hamount Hsellcandidate] | Hpositive].
        -- subst amount.
           destruct Hsell0 as [_ Hmaximal].
           destruct Hsellcandidate as [[sell_amount Hsellcandidate] _].
           apply Hmaximal with (amount := sell_amount).
           exact Hsellcandidate.
        -- lia.
    + exists (Znth 0 (Znth i dp_l_2 nil) 0). exact Hsell0.
  - intros stock Hstock.
    destruct (Z.eq_dec stock max_stock_pre) as [Heq | Hneq].
    + subst stock.
      unfold StockSellCellValue, StockSellCandidate.
      split.
      * exists 0. left. split; [lia | exact Hmaxeq].
      * intros amount candidate Hcandidate.
        destruct Hcandidate as [[Hamount Hcandidate] | Hpositive].
        -- subst amount candidate. lia.
        -- lia.
    + rewrite <- Hsource. apply Hsell. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27_split_goal_3 :
  maximum_profit_entail_wit_27_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH27.
  destruct PreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [_ [_ [Hbuy _]]]. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27_split_goal_4 :
  maximum_profit_entail_wit_27_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH27.
  destruct PreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [_ [_ [Hbuy _]]]. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27_split_goal_5 :
  maximum_profit_entail_wit_27_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH27.
  destruct PreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [_ [Hask _]]. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27_split_goal_6 :
  maximum_profit_entail_wit_27_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH27.
  destruct PreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [Hbidask _]. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27 : maximum_profit_entail_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_6.
Qed.

Lemma proof_of_maximum_profit_entail_wit_28_split_goal_1 :
  maximum_profit_entail_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyQueueExpiring. left.
  rewrite <- PreH9. exact PreH27.
Qed.

Lemma proof_of_maximum_profit_entail_wit_28_split_goal_2 :
  maximum_profit_entail_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH25. tauto.
Qed.

Lemma proof_of_maximum_profit_entail_wit_28_split_goal_3 :
  maximum_profit_entail_wit_28_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH25. tauto.
Qed.

Lemma proof_of_maximum_profit_entail_wit_28 : maximum_profit_entail_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_28_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_28_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_28_split_goal_3.
Qed.

Lemma proof_of_maximum_profit_entail_wit_29_split_goal_1 :
  maximum_profit_entail_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH14.
  unfold StockBuyQueueExpiring, StockBuyQueue in *.
  destruct PreH32 as [Hqueue | Hqueue].
  - right.
    destruct Hqueue as [Hbounds [Hentries [Hordered Hcovers]]].
    split; [lia |].
    split.
    + intros pos Hpos.
      pose proof (Hentries pos ltac:(lia)) as Hpos_entry.
      pose proof (Hentries head ltac:(lia)) as Hhead_entry.
      pose proof (Hordered head pos ltac:(lia)) as Hhead_before.
      destruct Hpos_entry as [Hpos_nonneg [Hpos_len [Hpos_valid Hpos_range]]].
      destruct Hhead_entry as [_ [_ [_ Hhead_range]]].
      destruct Hhead_before as [Hindices _].
      destruct Hpos_range as [_ Hpos_upper].
      destruct Hhead_range as [Hhead_lower Hhead_upper].
      repeat split; try assumption; lia.
    + split.
      * intros left right0 Hpositions. apply Hordered. lia.
      * intros candidate Hcandidate.
      destruct Hcandidate as [Hnonneg [Hinrow [Hvalid Hrange]]].
      specialize (Hcovers candidate).
      assert (Holdrange :
        0 <= candidate /\
        candidate < Zlength (Znth source_day dp_l_2 nil) /\
        Znth candidate (Znth source_day dp_l_2 nil) 0 <> STOCK_NEG_INF /\
        j - buy_cap - 1 <= candidate <= j - 2) by
        (repeat split; try assumption; lia).
      specialize (Hcovers Holdrange).
      destruct Hcovers as [pos [Hpos [Hcandidate_le Hscore]]].
      destruct Hpos as [Hpos_lower Hpos_upper].
      destruct Hrange as [Hcandidate_lower Hcandidate_upper].
      pose proof (Hentries head ltac:(lia)) as Hhead_entry.
      destruct Hhead_entry as [_ [_ [_ Hhead_range]]].
      destruct Hhead_range as [Hhead_lower Hhead_upper].
      assert (head < pos).
      { destruct (Z.eq_dec pos head) as [Heq | Hneq].
        - subst pos. lia.
        - lia. }
      exists pos. split; [lia |].
      split; assumption.
  - destruct Hqueue as [_ [Hentries _]].
    specialize (Hentries head ltac:(lia)).
      destruct Hentries as [_ [_ [_ Hrange]]].
      lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_29 : maximum_profit_entail_wit_29.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_29_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_30_1_split_goal_1 :
  maximum_profit_entail_wit_30_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH13.
  unfold StockBuyQueueExpiring in PreH31.
  unfold StockBuyQueue in *.
  destruct PreH31 as [Hqueue | Hqueue];
    destruct Hqueue as [Hbounds [Hentries [Hordered Hcovers]]].
  - split; [exact Hbounds |].
    split.
    + intros pos Hpos. lia.
    + split.
      * intros left right Hpositions. lia.
      * intros candidate Hcandidate. apply Hcovers.
      unfold StockFiniteIndexInWindow in *.
      destruct Hcandidate as [Hnonneg [Hinrow [Hvalid Hrange]]].
      repeat split; try assumption; lia.
  - split; [exact Hbounds |].
    split.
    + intros pos Hpos. lia.
    + split.
      * intros left right Hpositions. lia.
      * exact Hcovers.
Qed.

Lemma proof_of_maximum_profit_entail_wit_30_1 : maximum_profit_entail_wit_30_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_30_1_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_30_2_split_goal_1 :
  maximum_profit_entail_wit_30_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH14.
  unfold StockBuyQueueExpiring in PreH32.
  destruct PreH32 as [Hqueue | Hqueue]; [| exact Hqueue].
  unfold StockBuyQueue in *.
  destruct Hqueue as [Hbounds [Hentries [Hordered Hcovers]]].
  split; [exact Hbounds |].
  split.
  - intros pos Hpos.
    pose proof (Hentries pos Hpos) as Hpos_entry.
    pose proof (Hentries head ltac:(lia)) as Hhead_entry.
    destruct Hpos_entry as [Hpos_nonneg [Hpos_len [Hpos_valid Hpos_range]]].
    destruct Hhead_entry as [_ [_ [_ Hhead_range]]].
    assert (j - buy_cap <= Znth pos queue_l_2 0).
    + destruct (Z.eq_dec pos head) as [Heq | Hneq].
      * subst pos. lia.
      * pose proof (Hordered head pos ltac:(lia)) as Hhead_before.
        destruct Hhead_before as [Hindices _]. lia.
    + repeat split; try assumption; lia.
  - split.
    + exact Hordered.
    + intros candidate Hcandidate.
      destruct Hcandidate as [Hnonneg [Hinrow [Hvalid Hrange]]].
      apply Hcovers.
      repeat split; try assumption; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_30_2 : maximum_profit_entail_wit_30_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_30_2_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_31_1 : maximum_profit_entail_wit_31_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l dp_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_pre source_day (days_pre + 1) width dp_l
      (Znth source_day dp_l __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre width source_day) width
      (Znth source_day dp_l __default__List_Z)) with
      (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
        width (Znth source_day dp_l __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + source_day * width * sizeof ( INT )) (j - 1) width
      (Znth (j - 1) (Znth source_day dp_l __default__List_Z) 0)
      (Znth source_day dp_l __default__List_Z)) as Hcell.
    assert (Haddr :
      dp_pre + source_day * width * sizeof ( INT ) +
        (j - 1) * sizeof ( INT ) =
      dp_pre + (source_day * width + (j - 1)) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + unfold StockBuyQueue in PreH30.
      destruct PreH30 as [_ [Hvalid _]].
      specialize (Hvalid (tail - 1) ltac:(lia)).
      unfold StockFiniteIndexInWindow in Hvalid. tauto.
    + unfold StockBuyQueue in PreH30.
      destruct PreH30 as [_ [Hvalid _]].
      specialize (Hvalid (tail - 1) ltac:(lia)).
      destruct Hvalid as [_ [Hlt _]].
      unfold StockTableShape in PreH31.
      destruct PreH31 as [_ Hrows].
      specialize (Hrows source_day ltac:(lia)). rewrite Hrows in Hlt. lia.
    + eapply (StockBuyQueue_begin_popping__buy_pop_append
        dp_l queue_l source_day ask_price (j - buy_cap) (j - 1)
        head tail).
      * lia.
      * unfold StockTableShape in PreH31.
        destruct PreH31 as [_ Hrows].
        specialize (Hrows source_day ltac:(lia)). rewrite Hrows. lia.
      * assert (Hsource_len : 0 <= source_day < Zlength dp_l).
        { unfold StockTableShape in PreH31.
          destruct PreH31 as [Hlen _]. rewrite Hlen. lia. }
        rewrite (same_index_different_default source_day dp_l
          __default__List_Z Hsource_len).
        unfold STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
      * replace (j - 1 - 1) with (j - 2) by lia. exact PreH30.
Qed.

Lemma proof_of_maximum_profit_entail_wit_31_2 : maximum_profit_entail_wit_31_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_pre source_day (days_pre + 1) width dp_l
      (Znth source_day dp_l __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre width source_day) width
      (Znth source_day dp_l __default__List_Z)) with
      (IntArray.full (dp_pre + source_day * width * sizeof ( INT ))
        width (Znth source_day dp_l __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + source_day * width * sizeof ( INT )) (j - 1) width
      (Znth (j - 1) (Znth source_day dp_l __default__List_Z) 0)
      (Znth source_day dp_l __default__List_Z)) as Hcell.
    assert (Haddr :
      dp_pre + source_day * width * sizeof ( INT ) +
        (j - 1) * sizeof ( INT ) =
      dp_pre + (source_day * width + (j - 1)) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    eapply (StockBuyQueue_begin_popping__buy_pop_append
      dp_l queue_l_2 source_day ask_price (j - buy_cap) (j - 1)
      head tail).
    + lia.
    + unfold StockTableShape in PreH31.
      destruct PreH31 as [_ Hrows].
      specialize (Hrows source_day ltac:(lia)). rewrite Hrows. lia.
    + assert (Hsource_len : 0 <= source_day < Zlength dp_l).
      { unfold StockTableShape in PreH31.
        destruct PreH31 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (same_index_different_default source_day dp_l
        __default__List_Z Hsource_len).
      unfold STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
    + replace (j - 1 - 1) with (j - 2) by lia. exact PreH30.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_1 : maximum_profit_entail_wit_32_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
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
      dp_pre + source_day * width * sizeof ( INT ) +
        last_index * sizeof ( INT ) =
      dp_pre + (source_day * width + last_index) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + unfold StockBuyQueuePopping in PreH33.
      destruct PreH33 as [_ [_ [Hentries _]]].
      specialize (Hentries (tail - 1 - 1) ltac:(lia)).
      unfold StockFiniteIndexInWindow in Hentries. tauto.
    + unfold StockBuyQueuePopping in PreH33.
      destruct PreH33 as [_ [_ [Hentries _]]].
      specialize (Hentries (tail - 1 - 1) ltac:(lia)).
      unfold StockFiniteIndexInWindow in Hentries.
      unfold StockTableShape in PreH34.
      destruct PreH34 as [_ Hrowlen].
      pose proof (Hrowlen source_day ltac:(lia)) as Hsource_len.
      lia.
    + eapply StockBuyQueuePopping_drop_tail__buy_pop_append.
      * exact PreH33.
      * lia.
      * unfold StockBuyScore.
        assert (Hsource_len : 0 <= source_day < Zlength dp_l_2).
        { unfold StockTableShape in PreH34.
          destruct PreH34 as [Hlen _]. rewrite Hlen. lia. }
        rewrite (same_index_different_default source_day dp_l_2
          __default__List_Z Hsource_len).
        rewrite <- PreH29.
        rewrite (PreH30 PreH3) in PreH2. exact PreH2.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_2 : maximum_profit_entail_wit_32_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
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
      dp_pre + source_day * width * sizeof ( INT ) +
        last_index * sizeof ( INT ) =
      dp_pre + (source_day * width + last_index) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    eapply StockBuyQueuePopping_drop_tail__buy_pop_append.
    + exact PreH33.
    + lia.
    + unfold StockBuyScore.
      assert (Hsource_len : 0 <= source_day < Zlength dp_l_2).
      { unfold StockTableShape in PreH34.
        destruct PreH34 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (same_index_different_default source_day dp_l_2
        __default__List_Z Hsource_len).
      rewrite <- PreH29.
      rewrite (PreH30 PreH3) in PreH2. exact PreH2.
Qed.

Lemma proof_of_maximum_profit_entail_wit_33_1 : maximum_profit_entail_wit_33_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength queue_index_pre width queue_l_2).
  Intros_p Hqueue_len.
  Exists dp_l_2 queue_l_2.
  split_pure_spatial.
  - cancel (IntArray.full queue_index_pre width queue_l_2).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    unfold StockBuyQueuePending.
    split; [exact PreH31 |].
    split; [lia |].
    intros Hlt. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_33_2 : maximum_profit_entail_wit_33_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength queue_index_pre width queue_l_2).
  Intros_p Hqueue_len.
  Exists dp_l_2 queue_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
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
      dp_pre + source_day * width * sizeof ( INT ) +
        last_index * sizeof ( INT ) =
      dp_pre + (source_day * width + last_index) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    unfold StockBuyQueuePending.
    split; [exact PreH32 |].
    split; [lia |].
    intros Hlt.
    unfold StockBuyScore.
    assert (Hsource_len : 0 <= source_day < Zlength dp_l_2).
    { unfold StockTableShape in PreH33.
      destruct PreH33 as [Hlen _]. rewrite Hlen. lia. }
    rewrite (same_index_different_default source_day dp_l_2
      __default__List_Z Hsource_len).
    rewrite <- (PreH29 Hlt).
    rewrite <- PreH28.
    lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_34 : maximum_profit_entail_wit_34.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (replace_Znth tail (j - 1) queue_l_2) dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full queue_index_pre width
      (replace_Znth tail (j - 1) queue_l_2)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + unfold StockBuyProgress in PreH20.
      destruct PreH20 as [_ [Hirange _]]. lia.
    + unfold StockBuyProgress in PreH20.
      destruct PreH20 as [_ [Hirange _]].
      unfold StockInputsBounded in PreH19.
      destruct PreH19 as [Hasklen _]. rewrite Hasklen in Hirange. lia.
    + unfold StockBuyProgress in PreH20.
      destruct PreH20 as [_ [_ [_ [Hsource_range _]]]]. lia.
    + unfold StockBuyProgress in PreH20.
      destruct PreH20 as [_ [_ [_ [Hsource_range _]]]]. lia.
    + apply (StockBuyQueuePending_append__buy_pop_append
        dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1)
        head tail).
      * exact PreH21.
      * unfold StockInputsBounded in PreH19.
        destruct PreH19 as [Hasklen [_ [_ [_ [_ [_ Hinputs]]]]]].
        unfold StockBuyProgress in PreH20.
        destruct PreH20 as [_ [Hirange _]].
        rewrite Hasklen in Hirange.
        specialize (Hinputs i ltac:(lia)).
        destruct Hinputs as [_ [_ [Hbuy _]]].
        rewrite <- PreH14 in Hbuy. lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_35_2 : maximum_profit_entail_wit_35_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + source_day * width * sizeof (INT)) (j - 1) width
         (Znth (j - 1) (Znth source_day dp_l_2 __default__List_Z) 0)
         (Znth source_day dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + source_day * width * sizeof (INT) + (j - 1) * sizeof (INT) =
      dp_pre + (source_day * width + (j - 1)) * sizeof (INT)) by lia.
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
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    eapply StockBuyQueue_extend_invalid__buy_cell_progress.
    + replace (j - 1 - 1) with (j - 2) by lia.
      exact PreH29.
    + unfold StockTableShape in PreH30.
      destruct PreH30 as [Htablelen Hrows].
      specialize (Hrows source_day ltac:(lia)).
      lia.
    + assert (Hsrc : 0 <= source_day < Zlength dp_l_2).
      { pose proof PreH30 as Hshape.
        unfold StockTableShape in Hshape.
        destruct Hshape as [Htablelen _]. lia. }
      rewrite <- (same_index_different_default source_day dp_l_2
        __default__List_Z Hsrc) in PreH1.
      unfold STOCK_NEG_INF. lia.
Qed.

