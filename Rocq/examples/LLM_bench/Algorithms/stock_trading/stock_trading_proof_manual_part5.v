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

(* Split from stock_trading_proof_manual.v, part 5 of 5. *)
Lemma proof_of_maximum_profit_entail_wit_36_split_goal_1 :
  maximum_profit_entail_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyQueue in PreH25.
  destruct PreH25 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  unfold StockFiniteIndexInWindow in Hentries.
  destruct Hentries as [Hidx [_ [_ [_ Hupper]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_split_goal_2 :
  maximum_profit_entail_wit_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyQueue in PreH25.
  destruct PreH25 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  unfold StockFiniteIndexInWindow in Hentries.
  destruct Hentries as [Hidx _].
  exact Hidx.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_split_goal_3 :
  maximum_profit_entail_wit_36_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbidask [Hask _]].
  rewrite <- PreH18 in Hask.
  exact Hask.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_split_goal_4 :
  maximum_profit_entail_wit_36_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbidask _].
  rewrite <- PreH18 in Hbidask.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36 : maximum_profit_entail_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_split_goal_4.
Qed.

Lemma proof_of_maximum_profit_entail_wit_37 : maximum_profit_entail_wit_37.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists dp_l queue_l_2.
  split_pure_spatial.
  - pose proof
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
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia; try reflexivity.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_1 : maximum_profit_entail_wit_38_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsrc : 0 <= source_day < Zlength dp_l_2).
  { unfold StockTableShape in PreH30. lia. }
  assert (Hirow : 0 <= i < Zlength dp_l_2).
  { unfold StockTableShape in PreH30. lia. }
  rewrite <- (same_index_different_default source_day dp_l_2
    __default__List_Z Hsrc) in PreH28.
  rewrite <- (same_index_different_default i dp_l_2
    __default__List_Z Hirow) in PreH1.
  assert (Hcell : StockBuyCellValue ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre i source_day j buy_candidate).
  { eapply StockBuyCellValue_improve__buy_cell_progress with
      (queue := queue_l_2) (price := ask_price) (buy_cap := buy_cap)
      (head := head) (tail := tail) (best := best_index); eauto; try lia. }
  pose proof (StockBuyProgress_replace_improved_step__buy_semantics
    ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
    i source_day j buy_candidate PreH26 ltac:(lia) PreH30 PreH27
    ltac:(lia) ltac:(lia) Hcell) as Hstep.
  cbn in Hstep.
  destruct Hstep as [Hprogress Hshape].
  rewrite (same_index_different_default i dp_l_2
    __default__List_Z Hirow) in Hprogress, Hshape.
  assert (HqueueNext : StockBuyQueue
    (replace_Znth i
      (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z))
      dp_l_2)
    queue_l_2 source_day ask_price
    (j + 1 - buy_cap - 1) (j + 1 - 2) head tail).
  { replace (j + 1 - buy_cap - 1) with (j - buy_cap) by lia.
    replace (j + 1 - 2) with (j - 1) by lia.
    eapply StockBuyQueue_replace_other_row__buy_cell_progress; eauto; lia. }
  pose proof PreH26 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbidask [Hask [Hbuy _]]].
  rewrite <- PreH21 in Hbidask, Hask.
  rewrite <- PreH22 in Hbuy.
  pose proof PreH27 as Hprogress0.
  unfold StockBuyProgress in Hprogress0.
  destruct Hprogress0 as [_ [_ [Hsource [Hsrange _]]]].
  Exists queue_l_2 (replace_Znth i
    (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z))
    dp_l_2).
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + i * width * sizeof (INT)) j width buy_candidate
         (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    pose proof
      (IntArray2.missing_i_merge_to_full dp_pre i (days_pre + 1) width dp_l_2
         (replace_Znth j buy_candidate
           (Znth i dp_l_2 __default__List_Z))) as Htablemerge.
    change
      (IntArray2.ElemArray.full (IntArray2.row_addr dp_pre width i) width
        (replace_Znth j buy_candidate
          (Znth i dp_l_2 __default__List_Z)))
      with
      (IntArray.full (dp_pre + i * width * sizeof (INT)) width
        (replace_Znth j buy_candidate
          (Znth i dp_l_2 __default__List_Z))) in Htablemerge.
    sep_apply Htablemerge; try lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial; try exact HqueueNext; try exact Hprogress;
      try exact Hshape; try assumption; try lia; try reflexivity.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_2 : maximum_profit_entail_wit_38_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsrc : 0 <= source_day < Zlength dp_l_2).
  { unfold StockTableShape in PreH30. lia. }
  assert (Hirow : 0 <= i < Zlength dp_l_2).
  { unfold StockTableShape in PreH30. lia. }
  rewrite <- (same_index_different_default source_day dp_l_2
    __default__List_Z Hsrc) in PreH28.
  rewrite <- (same_index_different_default i dp_l_2
    __default__List_Z Hirow) in PreH1.
  assert (Hcell : StockBuyCellValue ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre i source_day j (Znth j (Znth i dp_l_2 nil) 0)).
  { eapply StockBuyCellValue_keep__buy_cell_progress with
      (queue := queue_l_2) (price := ask_price) (buy_cap := buy_cap)
      (head := head) (tail := tail) (best := best_index)
      (value := buy_candidate); eauto; try lia. }
  pose proof (StockBuyProgress_step_same__buy_cell_progress
    ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j
    PreH27 ltac:(lia) Hcell) as Hnext.
  pose proof PreH26 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbidask [Hask [Hbuy _]]].
  pose proof PreH27 as Hprogress.
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [_ [_ [Hsource [Hsrange _]]]].
  rewrite <- PreH21 in Hbidask, Hask.
  rewrite <- PreH22 in Hbuy.
  assert (HqueueNext : StockBuyQueue dp_l_2 queue_l_2 source_day ask_price
    (j + 1 - buy_cap - 1) (j + 1 - 2) head tail).
  { replace (j + 1 - buy_cap - 1) with (j - buy_cap) by lia.
    replace (j + 1 - 2) with (j - 1) by lia. exact PreH29. }
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof
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
      (IntArray2.missing_i_merge_to_full dp_pre i (days_pre + 1) width dp_l_2
         (Znth i dp_l_2 __default__List_Z)) as Htablemerge.
    change
      (IntArray2.ElemArray.full (IntArray2.row_addr dp_pre width i) width
        (Znth i dp_l_2 __default__List_Z))
      with
      (IntArray.full (dp_pre + i * width * sizeof (INT)) width
        (Znth i dp_l_2 __default__List_Z)) in Htablemerge.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial; try exact HqueueNext; try exact Hnext;
      try assumption; try lia; try reflexivity.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_1 :
  maximum_profit_entail_wit_38_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (j + 1 - buy_cap - 1) with (j - buy_cap) by lia.
  replace (j + 1 - 2) with (j - 1) by lia.
  exact PreH25.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_2 :
  maximum_profit_entail_wit_38_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrowlen : j < Zlength (Znth source_day dp_l_2 nil)).
  { unfold StockTableShape in PreH26.
    destruct PreH26 as [_ Hrows].
    specialize (Hrows source_day ltac:(lia)). lia. }
  assert (Hcell : StockBuyCellValue ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre i source_day j (Znth j (Znth i dp_l_2 nil) 0)).
  { eapply StockBuyCellValue_empty_queue__buy_cell_progress; eauto; try lia. }
  pose proof (StockBuyProgress_step_same__buy_cell_progress
    ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j
    PreH24 ltac:(lia) Hcell) as Hnext.
  exact Hnext.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_3 :
  maximum_profit_entail_wit_38_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [_ [Hbuy _]]].
  rewrite <- PreH19 in Hbuy.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_4 :
  maximum_profit_entail_wit_38_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [_ [Hbuy _]]].
  rewrite <- PreH19 in Hbuy.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_5 :
  maximum_profit_entail_wit_38_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [Hask _]].
  rewrite <- PreH18 in Hask.
  exact Hask.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_6 :
  maximum_profit_entail_wit_38_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH23.
  destruct PreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbidask _].
  rewrite <- PreH18 in Hbidask.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_7 :
  maximum_profit_entail_wit_38_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH24.
  destruct PreH24 as [_ [_ [_ [Hsrange _]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_8 :
  maximum_profit_entail_wit_38_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH24.
  destruct PreH24 as [_ [_ [Hsource _]]].
  exact Hsource.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3_split_goal_9 :
  maximum_profit_entail_wit_38_3_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH24.
  destruct PreH24 as [_ [_ [Hsource [Hsrange _]]]].
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38_3 : maximum_profit_entail_wit_38_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_6.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_7.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_8.
  - Goal_apply proof_of_maximum_profit_entail_wit_38_3_split_goal_9.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_split_goal_1 :
  maximum_profit_entail_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH25 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbid [Hask [Hbuy Hsell]]].
  rewrite <- PreH12 in Hbid.
  rewrite <- PreH13 in Hsell.
  pose proof (StockBuyProgress_complete_day__buy_semantics
    ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
    i source_day j PreH25 PreH4 PreH7 ltac:(lia) PreH26) as Hdone.
  exact Hdone.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_split_goal_2 :
  maximum_profit_entail_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH25.
  destruct PreH25 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [_ [_ Hsell]]].
  rewrite <- PreH13 in Hsell.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_split_goal_3 :
  maximum_profit_entail_wit_39_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH25.
  destruct PreH25 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [_ [_ Hsell]]].
  rewrite <- PreH13 in Hsell.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_split_goal_4 :
  maximum_profit_entail_wit_39_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH25.
  destruct PreH25 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbid _].
  rewrite <- PreH12 in Hbid.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_split_goal_5 :
  maximum_profit_entail_wit_39_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH25.
  destruct PreH25 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbid _].
  rewrite <- PreH12 in Hbid.
  lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39 : maximum_profit_entail_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_39_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_39_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_39_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_39_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_39_split_goal_5.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_1_split_goal_1 :
  maximum_profit_entail_wit_40_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH19.
  intuition lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_1_split_goal_2 :
  maximum_profit_entail_wit_40_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH19.
  intuition lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_1_split_goal_3 :
  maximum_profit_entail_wit_40_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH19.
  intuition lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_1 : maximum_profit_entail_wit_40_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_40_1_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_40_1_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_40_1_split_goal_3.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_2_split_goal_1 :
  maximum_profit_entail_wit_40_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH9.
  intuition lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_2_split_goal_2 :
  maximum_profit_entail_wit_40_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH9.
  intuition lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_2_split_goal_3 :
  maximum_profit_entail_wit_40_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH9.
  intuition lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_2 : maximum_profit_entail_wit_40_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_40_2_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_40_2_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_40_2_split_goal_3.
Qed.

Lemma proof_of_maximum_profit_entail_wit_41_split_goal_1 :
  maximum_profit_entail_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH12 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [Hask [Hbid [Hbuy [Hsell [Hdays [Hmax Hbounds]]]]]].
  eapply stock_answer_init__outer_answer; eauto; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_41 : maximum_profit_entail_wit_41.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_41_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_42_1 : maximum_profit_entail_wit_42_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_pre days_pre (days_pre + 1) width dp_l_2
      (Znth days_pre dp_l_2 __default__List_Z)) as Htablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre width days_pre) width
      (Znth days_pre dp_l_2 __default__List_Z)) with
      (IntArray.full (dp_pre + days_pre * width * sizeof (INT))
        width (Znth days_pre dp_l_2 __default__List_Z)) in Htablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + days_pre * width * sizeof (INT)) j width
      (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0)
      (Znth days_pre dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr :
      dp_pre + days_pre * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (days_pre * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    all: try (
      dump_pre_spatial;
      apply (stock_answer_improve__outer_answer
        ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
        j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0));
      [ lia
      | exact PreH13
      | exact PreH2
      | exact PreH16
      | assert (Hday : 0 <= days_pre < Zlength dp_l_2);
        [ unfold StockTableShape in PreH17; destruct PreH17 as [Hlen _]; lia
        | rewrite <- (same_index_different_default days_pre dp_l_2
            __default__List_Z Hday); reflexivity ]
      | exact PreH1 ]).
    all: unfold StockAnswerProgress in PreH16.
    all: destruct PreH16 as [Hdone _].
    all: unfold StockDaysDone in Hdone.
    all: destruct Hdone as [_ [Hbounded _]].
    all: unfold StockTableValuesBounded in Hbounded.
    all: pose proof PreH15 as Hinputs.
    all: unfold StockInputsBounded in Hinputs.
    all: destruct Hinputs as [Hask _].
    all: rewrite Hask in Hbounded.
    all: specialize (Hbounded days_pre j ltac:(lia) ltac:(lia)).
    all: unfold STOCK_MAX_PROFIT in Hbounded.
    all: assert (Hday : 0 <= days_pre < Zlength dp_l_2) by
      (unfold StockTableShape in PreH17;
       destruct PreH17 as [Hlen _]; lia).
    all: rewrite <- (same_index_different_default days_pre dp_l_2
      __default__List_Z Hday).
    all: dump_pre_spatial.
    all: lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_42_2 : maximum_profit_entail_wit_42_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      dp_pre days_pre (days_pre + 1) width dp_l_2
      (Znth days_pre dp_l_2 __default__List_Z)) as Htablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre width days_pre) width
      (Znth days_pre dp_l_2 __default__List_Z)) with
      (IntArray.full (dp_pre + days_pre * width * sizeof (INT))
        width (Znth days_pre dp_l_2 __default__List_Z)) in Htablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + days_pre * width * sizeof (INT)) j width
      (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0)
      (Znth days_pre dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr :
      dp_pre + days_pre * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (days_pre * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    dump_pre_spatial.
    apply (stock_answer_keep__outer_answer
      ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
      j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0)).
    + lia.
    + exact PreH2.
    + exact PreH16.
    + assert (Hday : 0 <= days_pre < Zlength dp_l_2).
      { unfold StockTableShape in PreH17. destruct PreH17 as [Hlen _]. lia. }
      rewrite <- (same_index_different_default days_pre dp_l_2
        __default__List_Z Hday).
      reflexivity.
    + exact PreH1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_43_split_goal_1 :
  maximum_profit_entail_wit_43_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (stock_answer_finish__outer_answer
    ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
    j answer).
  - lia.
  - exact PreH1.
  - exact PreH11.
  - exact PreH15.
Qed.

Lemma proof_of_maximum_profit_entail_wit_43 : maximum_profit_entail_wit_43.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_43_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_return_wit_1 : maximum_profit_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst width.
  split_pure_spatial.
  - cancel (IntArray.full ap_pre days_pre ap_l).
    cancel (IntArray.full bp_pre days_pre bp_l).
    cancel (IntArray.full buy_limit_pre days_pre buy_l).
    cancel (IntArray.full sell_limit_pre days_pre sell_l).
    sep_apply_l_atomic
      (IntArray.full_to_undef_full queue_index_pre (max_stock_pre + 1) queue_l).
    sep_apply_l_atomic
      (IntArray2.full_to_undef_full dp_pre (days_pre + 1)
        (max_stock_pre + 1) dp_l).
    cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.
