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

(* Split from stock_trading_proof_manual.v, part 3 of 5. *)
Lemma proof_of_maximum_profit_entail_wit_26_1 : maximum_profit_entail_wit_26_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH25 as Hinput_bounds0.
  unfold StockInputsBounded in Hinput_bounds0.
  destruct Hinput_bounds0 as [_ [_ [_ [_ [_ [_ Hinput_at0]]]]]].
  specialize (Hinput_at0 i ltac:(lia)).
  destruct Hinput_at0 as
    [Hbid_bounds0 [Hask_bound0 [_ Hsell_bounds0]]].
  rewrite <- PreH23 in Hbid_bounds0.
  rewrite <- PreH24 in Hsell_bounds0.
  pose proof PreH26 as Hprogress_bounds0.
  unfold StockSellProgress in Hprogress_bounds0.
  destruct Hprogress_bounds0 as
    [_ [_ [Hsource_eq0 [Hsource_range0 _]]]].
  Exists queue_l_2 (replace_Znth i
    (replace_Znth j sell_candidate
      (Znth i dp_l_2 __default__List_Z)) dp_l_2).
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof
    (IntArray.missing_i_merge_to_full
       (dp_pre + i * width * sizeof (INT)) j width sell_candidate
       (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
    dp_pre + (i * width + j) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       dp_pre i (days_pre + 1) width dp_l_2
       (replace_Znth j sell_candidate
         (Znth i dp_l_2 __default__List_Z))) as Htablemerge.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr dp_pre width i) width
       (replace_Znth j sell_candidate
         (Znth i dp_l_2 __default__List_Z)))
    with
    (IntArray.full
       (dp_pre + i * width * sizeof (INT)) width
       (replace_Znth j sell_candidate
         (Znth i dp_l_2 __default__List_Z)))
    in Htablemerge.
  sep_apply Htablemerge; try lia.
  cancel.
  3: {
    unfold StockTableShape in *.
    destruct PreH29 as [Htable_len Hrow_len].
    split.
    - rewrite Zlength_replace_Znth. exact Htable_len.
    - intros row Hrow.
      destruct (Z.eq_dec row i) as [-> | Hneq].
      + rewrite Znth_replace_Znth_Same by lia.
        rewrite Zlength_replace_Znth.
        assert (Hi_len : 0 <= i < Zlength dp_l_2) by
          (rewrite Htable_len; lia).
        rewrite <- (same_index_different_default i dp_l_2
          __default__List_Z) by exact Hi_len.
        apply Hrow_len. lia.
      + rewrite Znth_replace_Znth_Diff by lia.
        apply Hrow_len. lia.
  }
  2: {
    replace (j - 1 + 2) with (j + 1) by lia.
    replace (j - 1 + sell_cap + 1) with (j + sell_cap) by lia.
    assert (Hsrc: 0 <= source_day < Zlength dp_l_2).
    { unfold StockTableShape in PreH29. lia. }
    unfold StockSellQueue in *.
    destruct PreH28 as [Hheadtail [Hentries [Horder Hcover]]].
    split; [exact Hheadtail |].
    split; [intros pos Hpos |].
    + specialize (Hentries pos Hpos).
      destruct Hentries as [Hnonneg [Hlen [Hninf Hrange]]].
      split; [exact Hnonneg |].
      split.
      * rewrite Znth_replace_Znth_Diff.
        -- exact Hlen.
        -- unfold StockTableShape in PreH29. lia.
        -- exact Hsrc.
        -- lia.
      * split; [| exact Hrange].
        rewrite Znth_replace_Znth_Diff.
        -- exact Hninf.
        -- unfold StockTableShape in PreH29. lia.
        -- exact Hsrc.
        -- lia.
    + split.
      * intros left right Hlr.
        destruct (Horder left right Hlr) as [Horder_stock Horder_score].
        split; [exact Horder_stock |].
        unfold StockSellScore.
        rewrite Znth_replace_Znth_Diff.
        -- unfold StockSellScore in Horder_score. exact Horder_score.
        -- unfold StockTableShape in PreH29. lia.
        -- exact Hsrc.
        -- lia.
      * intros candidate Hcandidate.
        destruct Hcandidate as [Hnonneg [Hlen [Hninf Hrange]]].
        unfold StockTableShape in PreH29.
        destruct PreH29 as [Htable_len _].
        assert (Hsource_row :
          Znth source_day
            (replace_Znth i
               (replace_Znth j sell_candidate
                  (Znth i dp_l_2 __default__List_Z)) dp_l_2) (@nil Z) =
          Znth source_day dp_l_2 (@nil Z)).
        { rewrite Znth_replace_Znth_Diff.
          - reflexivity.
          - rewrite Htable_len. lia.
          - exact Hsrc.
          - lia. }
        rewrite Hsource_row in Hlen, Hninf.
        unfold StockSellScore.
        rewrite Hsource_row.
        apply Hcover.
        repeat split; try assumption; lia.
  }
  unfold StockSellProgress in PreH26 |- *.
  destruct PreH26 as [Hdone [Hday [Hsource [Hsrange
      [Hjrange [Hcopy [Hcells Hlast]]]]]]].
    unfold StockSellQueue in PreH28.
    destruct PreH28 as [Hht [Hentries [Horder Hcover]]].
    pose proof (Hentries head ltac:(lia)) as Hbest.
    destruct Hbest as [Hbest0 [Hbestlen [Hbestfinite Hbestrange]]].
    rewrite <- PreH19 in Hbest0, Hbestlen, Hbestfinite, Hbestrange.
    unfold StockDaysDone in Hdone.
    destruct Hdone as [Hshape [Hbounded [Hdone0 Hportfolio]]].
    unfold StockTableShape in Hshape.
    destruct Hshape as [Htablelen Hrowlen].
    assert (Hasklen : Zlength ap_l = days_pre).
    { pose proof PreH25 as Hinputs_copy.
      unfold StockInputsBounded in Hinputs_copy. tauto. }
    rewrite Hasklen in Htablelen, Hrowlen, Hbounded.
    assert (Hirow : 0 <= i < Zlength dp_l_2) by (rewrite Htablelen; lia).
    assert (Hsrcrow : 0 <= source_day < Zlength dp_l_2) by
      (rewrite Htablelen; lia).
    assert (Hrowi : Zlength (Znth i dp_l_2 (@nil Z)) = max_stock_pre + 1).
    { apply Hrowlen. lia. }
    assert (Hsrcdefault :
      Znth source_day dp_l_2 __default__List_Z =
      Znth source_day dp_l_2 (@nil Z)).
    { symmetry. apply same_index_different_default. exact Hsrcrow. }
    assert (Hidefault :
      Znth i dp_l_2 __default__List_Z = Znth i dp_l_2 (@nil Z)).
    { symmetry. apply same_index_different_default. exact Hirow. }
    assert (Hfeasible : StockFeasiblePortfolio ap_l bp_l buy_l sell_l
      max_stock_pre wait_days_pre source_day best_index
      (Znth best_index (Znth source_day dp_l_2 (@nil Z)) 0)).
    { pose proof (Hportfolio source_day best_index ltac:(lia)
        ltac:(lia)) as Hvalue.
      unfold StockPortfolioValue in Hvalue.
      destruct Hvalue as [_ [[Hneg Hnone] | [Hfeas _]]].
      - exfalso. apply Hbestfinite. exact Hneg.
      - exact Hfeas. }
    assert (Hnewhist : StockTradingHistory ap_l bp_l buy_l sell_l
      max_stock_pre wait_days_pre i j sell_candidate).
    { unfold StockFeasiblePortfolio in Hfeasible.
      destruct Hfeasible as [[Hstock0 Hprofit0] |
        [last_day [[Hlastlo Hlasthi] Hhist]]].
      - subst best_index.
        exfalso. lia.
      - rewrite Hsrcdefault in PreH27.
        rewrite PreH23 in PreH27.
        replace j with (best_index - (best_index - j)) by lia.
        replace sell_candidate with
          (Znth best_index (Znth source_day dp_l_2 (@nil Z)) 0 +
           (best_index - j) * Znth (i - 1) bp_l 0) by lia.
        eapply StockTradingHistory_sell with
          (previous_day := last_day) (previous_stock := best_index)
          (previous_profit := Znth best_index
             (Znth source_day dp_l_2 (@nil Z)) 0)
          (amount := best_index - j).
        + exact Hhist.
        + lia.
        + rewrite <- PreH24. lia.
        + lia. }
    assert (Hsellbounded : STOCK_NEG_INF <= sell_candidate <= STOCK_MAX_PROFIT).
    { pose proof (stock_trading_history_profit_bound__sell_cell_progress
        ap_l bp_l buy_l sell_l max_stock_pre wait_days_pre i j
        sell_candidate days_pre PreH25 PreH8 PreH12 Hnewhist) as Hb.
      unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in *.
      nia. }
    assert (Hshape' : StockTableShape
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      days_pre max_stock_pre).
    { unfold StockTableShape. split.
      - rewrite Zlength_replace_Znth. exact Htablelen.
      - intros row Hrow.
        destruct (Z.eq_dec row i) as [-> | Hneq].
        + rewrite Znth_replace_Znth_Same by exact Hirow.
          rewrite Zlength_replace_Znth, Hidefault. exact Hrowi.
        + rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
          apply Hrowlen. lia. }
    assert (Hbounded' : StockTableValuesBounded
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      days_pre max_stock_pre).
    { unfold StockTableValuesBounded in *.
      intros row stock Hrow Hstock.
      destruct (Z.eq_dec row i) as [-> | Hneq].
      - rewrite Znth_replace_Znth_Same by exact Hirow.
        destruct (Z.eq_dec stock j) as [-> | Hstockneq].
        + rewrite Znth_replace_Znth_Same by (rewrite Hidefault, Hrowi; lia).
          exact Hsellbounded.
        + rewrite Znth_replace_Znth_Diff by
            (try rewrite Hidefault, Hrowi; lia).
          rewrite Hidefault. apply Hbounded; lia.
      - rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
        apply Hbounded; lia. }
    assert (Hdone' : StockDaysDone ap_l bp_l buy_l sell_l
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      max_stock_pre wait_days_pre i).
    { unfold StockDaysDone. rewrite Hasklen.
      split; [exact Hshape' |].
      split; [exact Hbounded' |]. split; [exact Hdone0 |].
      intros row stock Hrow Hstock.
      rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      apply Hportfolio; lia. }
    assert (Hsource_new : Znth source_day
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2) (@nil Z) =
      Znth source_day dp_l_2 (@nil Z)).
    { rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      reflexivity. }
    assert (Hprev_new : Znth (i - 1)
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2) (@nil Z) =
      Znth (i - 1) dp_l_2 (@nil Z)).
    { rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      reflexivity. }
  split; [exact Hdone' |]. split; [exact Hday |].
  split; [exact Hsource |]. split; [exact Hsrange |].
  split; [lia |]. split.
  - intros stock Hstock.
      rewrite Znth_replace_Znth_Same by exact Hirow.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hidefault, Hrowi; lia).
      rewrite Hidefault.
      rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      apply Hcopy. lia.
  - split.
    + intros stock Hstock.
      destruct (Z.eq_dec stock j) as [-> | Hneq].
      { rewrite Znth_replace_Znth_Same by exact Hirow.
        rewrite Znth_replace_Znth_Same by
          (rewrite Hidefault, Hrowi; lia).
        unfold StockSellCellValue. split.
        -- exists (best_index - j). unfold StockSellCandidate. right.
           split; [rewrite <- PreH24; lia |].
           split; [lia |]. split.
           ++ replace (j + (best_index - j)) with best_index by lia.
              rewrite Hsource_new. exact Hbestfinite.
           ++ rewrite Znth_replace_Znth_Diff by
                (try rewrite Htablelen; lia).
              rewrite PreH27, PreH23.
              replace (j + (best_index - j)) with best_index by lia.
              rewrite Hsrcdefault. ring.
        -- intros amount candidate Hcand.
           unfold StockSellCandidate in Hcand.
           destruct Hcand as [[Hzero Hval] |
             [Hamount [Hstockbound [Hfinite Hval]]]].
           ++ subst amount candidate.
              rewrite Hprev_new in *.
              specialize (Hcopy j ltac:(lia)).
              rewrite <- Hcopy, <- Hidefault. lia.
           ++ assert (Hwindow : StockFiniteIndexInWindow dp_l_2 source_day
                (j + 1) (j + sell_cap) (j + amount)).
               { unfold StockFiniteIndexInWindow.
                 split; [lia |].
                 split.
                 - pose proof (Hrowlen source_day ltac:(lia)) as Hsrclen.
                   rewrite Hsrclen. lia.
                 - split.
                   + rewrite Hsource_new in Hfinite. exact Hfinite.
                   + split; [lia |].
                     rewrite PreH24. lia. }
              destruct (Hcover (j + amount) Hwindow) as
                [pos [Hpos [Hindex Hscore]]].
              assert (Hheadscore : StockSellScore dp_l_2 source_day bid_price
                (Znth pos queue_l_2 0) <=
                StockSellScore dp_l_2 source_day bid_price best_index).
              { destruct (Z.eq_dec pos head) as [-> | Hneqpos].
                - rewrite PreH19. lia.
                - destruct (Horder head pos ltac:(lia)) as [_ Hord].
                  rewrite <- PreH19 in Hord. lia. }
              unfold StockSellScore in *.
              rewrite Hsource_new in Hval.
              rewrite <- PreH23 in Hval.
              rewrite Hsrcdefault in PreH27.
              lia. }
      { rewrite Znth_replace_Znth_Same by exact Hirow.
         rewrite Znth_replace_Znth_Diff by
           (try rewrite Hidefault, Hrowi; lia).
         rewrite Hidefault.
         rewrite Hidefault in Hsource_new, Hprev_new.
         specialize (Hcells stock ltac:(lia)).
         unfold StockSellCellValue, StockSellCandidate in *.
         rewrite Hsource_new, Hprev_new.
         exact Hcells. }
    + rewrite Znth_replace_Znth_Same by exact Hirow.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hidefault, Hrowi; lia).
      rewrite Hidefault.
      rewrite Hidefault in Hprev_new.
      rewrite Hprev_new. exact Hlast.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_2 : maximum_profit_entail_wit_26_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hprogress' : StockSellProgress ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre wait_days_pre i source_day (j - 1)).
  { unfold StockSellProgress in PreH26 |- *.
    destruct PreH26 as [Hdone [Hday [Hsource [Hsrange
      [Hjrange [Hcopy [Hcells Hlast]]]]]]].
    unfold StockSellQueue in PreH28.
    destruct PreH28 as [Hht [Hentries [Horder Hcover]]].
    unfold StockTableShape in PreH29.
    destruct PreH29 as [Htablelen Hrowlen].
    assert (Hsrcrow : 0 <= source_day < Zlength dp_l_2) by
      (rewrite Htablelen; lia).
    assert (Hirow : 0 <= i < Zlength dp_l_2) by
      (rewrite Htablelen; lia).
    assert (Hsrcdefault :
      Znth source_day dp_l_2 __default__List_Z =
      Znth source_day dp_l_2 (@nil Z)).
    { symmetry. apply same_index_different_default. exact Hsrcrow. }
    assert (Hidefault :
      Znth i dp_l_2 __default__List_Z = Znth i dp_l_2 (@nil Z)).
    { symmetry. apply same_index_different_default. exact Hirow. }
    split; [exact Hdone |].
    split; [exact Hday |].
    split; [exact Hsource |].
    split; [exact Hsrange |].
    split; [lia |].
    split.
    - intros stock Hstock. apply Hcopy. lia.
    - split.
      + intros stock Hstock.
        destruct (Z.eq_dec stock j) as [-> | Hneq].
        { unfold StockSellCellValue, StockSellCandidate.
          split.
          - exists 0. left. split; [lia |]. apply Hcopy. lia.
          - intros amount candidate Hcand.
            destruct Hcand as [[Hzero Hval] |
              [Hamount [Hstockbound [Hfinite Hval]]]].
            + subst amount candidate. specialize (Hcopy j ltac:(lia)). lia.
            + assert (Hwindow : StockFiniteIndexInWindow dp_l_2 source_day
                 (j + 1) (j + sell_cap) (j + amount)).
              { unfold StockFiniteIndexInWindow.
                split; [lia |]. split.
                - pose proof (Hrowlen source_day ltac:(lia)) as Hsrclen.
                  rewrite Hsrclen. lia.
                - split; [exact Hfinite |].
                  split; [lia |]. rewrite PreH24. lia. }
              destruct (Hcover (j + amount) Hwindow) as
                [pos [Hpos [Hindex Hscore]]].
              assert (Hheadscore : StockSellScore dp_l_2 source_day bid_price
                (Znth pos queue_l_2 0) <=
                StockSellScore dp_l_2 source_day bid_price best_index).
              { destruct (Z.eq_dec pos head) as [-> | Hneqpos].
                - rewrite PreH19. lia.
                - destruct (Horder head pos ltac:(lia)) as [_ Hord].
                  rewrite <- PreH19 in Hord. lia. }
              unfold StockSellScore in *.
              rewrite Hsrcdefault in PreH27.
              rewrite Hidefault in PreH1.
              rewrite <- PreH23 in Hval.
              lia. }
        { apply Hcells. lia. }
      + exact Hlast. }
  pose proof PreH25 as Hinputs_copy.
  unfold StockInputsBounded in Hinputs_copy.
  destruct Hinputs_copy as [_ [_ [_ [_ [_ [_ Hinput_at]]]]]].
  specialize (Hinput_at i ltac:(lia)).
  destruct Hinput_at as [Hbid_bounds [Hask_bounds [_ Hsell_bounds]]].
  rewrite <- PreH23 in Hbid_bounds.
  rewrite <- PreH24 in Hsell_bounds.
  assert (Hsource_pos : 0 < source_day).
  { unfold StockSellProgress in PreH26. tauto. }
  assert (Hsource_eq : source_day = i - wait_days_pre - 1).
  { unfold StockSellProgress in PreH26. tauto. }
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: split_pures.
  all: try dump_pre_spatial.
  all: try assumption; try lia.
  pose proof
    (IntArray.missing_i_merge_to_full
       (dp_pre + i * width * sizeof (INT)) j width
       (Znth j (Znth i dp_l_2 __default__List_Z) 0)
       (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
    dp_pre + (i * width + j) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       dp_pre i (days_pre + 1) width dp_l_2
       (Znth i dp_l_2 __default__List_Z)) as Htablemerge.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr dp_pre width i) width
       (Znth i dp_l_2 __default__List_Z))
    with
    (IntArray.full
       (dp_pre + i * width * sizeof (INT)) width
       (Znth i dp_l_2 __default__List_Z))
    in Htablemerge.
  sep_apply Htablemerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  Unshelve.
  - replace (j - 1 + 2) with (j + 1) by lia.
    replace (j - 1 + sell_cap + 1) with (j + sell_cap) by lia.
    exact PreH28.
  all: try assumption; try lia; try exact Hprogress'.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_1 :
  maximum_profit_entail_wit_26_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (j - 1 + 2) with (j + 1) by lia.
  replace (j - 1 + sell_cap + 1) with (j + sell_cap) by lia.
  exact PreH24.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_2 :
  maximum_profit_entail_wit_26_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [Hasklen [Hbidlen [Hbuylen [Hselllen
    [Hdays [Hmaxstock Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [Hbid [Hask [Hbuy Hsell]]].
  unfold StockSellProgress in PreH23 |- *.
  destruct PreH23 as [Hdone [Hday [Hsource [Hsrange
    [Hjrange [Hcopy [Hcells Hlast]]]]]]].
  split; [exact Hdone |].
  split; [exact Hday |].
  split; [exact Hsource |].
  split; [exact Hsrange |].
  split; [lia |].
  split.
  - intros stock Hstock. apply Hcopy. lia.
  - split.
    + intros stock Hstock.
    destruct (Z.eq_dec stock j) as [-> | Hneq].
      * unfold StockSellCellValue, StockSellCandidate.
        split.
        -- exists 0. left. split; [lia |]. apply Hcopy. lia.
        -- intros amount candidate Hcand.
           destruct Hcand as [[Hzero Hval] |
             [Hamount [Hstockbound [Hfinite Hval]]]].
           ++ subst amount candidate. specialize (Hcopy j ltac:(lia)). lia.
           ++ unfold StockSellQueue in PreH24.
              destruct PreH24 as [_ [_ [_ Hcover]]].
              assert (Hwindow : StockFiniteIndexInWindow dp_l_2 source_day
                (j + 1) (j + sell_cap) (j + amount)).
              { unfold StockTableShape in PreH25.
                destruct PreH25 as [_ Hrowlen].
                unfold StockFiniteIndexInWindow.
                split; [lia |]. split.
                - pose proof (Hrowlen source_day ltac:(lia)) as Hsrclen.
                  rewrite Hsrclen. lia.
                - split; [exact Hfinite |].
                  split; [lia |]. rewrite PreH18. lia. }
              destruct (Hcover (j + amount) Hwindow) as [pos [Hpos _]].
              lia.
      * apply Hcells. lia.
    + exact Hlast.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_3 :
  maximum_profit_entail_wit_26_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold StockSellProgress in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_4 :
  maximum_profit_entail_wit_26_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold StockSellProgress in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_5 :
  maximum_profit_entail_wit_26_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold StockSellProgress in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_6 :
  maximum_profit_entail_wit_26_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH22.
  destruct PreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold StockSellProgress in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_7 :
  maximum_profit_entail_wit_26_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellProgress in PreH23.
  destruct PreH23 as [_ [_ [Hsource [Hsrange _]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3_split_goal_8 :
  maximum_profit_entail_wit_26_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellProgress in PreH23.
  destruct PreH23 as [_ [_ [Hsource _]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_3 : maximum_profit_entail_wit_26_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_6.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_7.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_3_split_goal_8.
Qed.

