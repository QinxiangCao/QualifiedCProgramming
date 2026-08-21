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

(* Split from stock_trading_proof_manual.v, part 1 of 5. *)
Lemma proof_of_maximum_profit_safety_wit_54_split_goal_1 :
  maximum_profit_safety_wit_54_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellQueueExpiring, StockSellQueue,
    StockFiniteIndexInWindow in PreH29.
  destruct PreH29 as [Hqueue | Hqueue];
    destruct Hqueue as [_ [Hentries _]];
    specialize (Hentries head ltac:(lia));
    destruct Hentries as [_ [_ [_ Hindex]]];
    split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_54_split_goal_2 :
  maximum_profit_safety_wit_54_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockSellQueueExpiring, StockSellQueue,
    StockFiniteIndexInWindow in PreH29.
  destruct PreH29 as [Hqueue | Hqueue];
    destruct Hqueue as [_ [Hentries _]];
    specialize (Hentries head ltac:(lia));
    destruct Hentries as [_ [_ [_ Hindex]]];
    split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_54 : maximum_profit_safety_wit_54.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_54_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_54_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_63_split_goal_1 :
  maximum_profit_safety_wit_63_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH29; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day (j + 1) __default__List_Z
       PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_63_split_goal_2 :
  maximum_profit_safety_wit_63_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH29; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day (j + 1) __default__List_Z
       PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_63 : maximum_profit_safety_wit_63.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_63_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_63_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_70_split_goal_1 :
  maximum_profit_safety_wit_70_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH29; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day (j + 1) __default__List_Z
       PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_70_split_goal_2 :
  maximum_profit_safety_wit_70_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH29; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day (j + 1) __default__List_Z
       PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_70 : maximum_profit_safety_wit_70.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_70_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_70_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_77_split_goal_1 :
  maximum_profit_safety_wit_77_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH28; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day last_index __default__List_Z
       PreH27 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_77_split_goal_2 :
  maximum_profit_safety_wit_77_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH28; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day last_index __default__List_Z
       PreH27 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_77 : maximum_profit_safety_wit_77.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_77_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_77_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_86_split_goal_1 :
  maximum_profit_safety_wit_86_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH27; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day best_index __default__List_Z
       PreH26 Hdone PreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_86_split_goal_2 :
  maximum_profit_safety_wit_86_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH27; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day best_index __default__List_Z
       PreH26 Hdone PreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_86 : maximum_profit_safety_wit_86.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_86_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_86_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_88_split_goal_1 :
  maximum_profit_safety_wit_88_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH27; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day best_index __default__List_Z
       PreH26 Hdone PreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_88_split_goal_2 :
  maximum_profit_safety_wit_88_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone : StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold StockSellProgress in PreH27; tauto).
  pose proof
    (StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i source_day best_index __default__List_Z
       PreH26 Hdone PreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_88 : maximum_profit_safety_wit_88.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_88_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_88_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_103_split_goal_1 :
  maximum_profit_safety_wit_103_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyQueueExpiring in PreH31.
  destruct PreH31 as [Hqueue | Hqueue];
  unfold StockBuyQueue in Hqueue;
  destruct Hqueue as [_ [Hentries _]];
  specialize (Hentries head ltac:(lia));
  unfold StockFiniteIndexInWindow in Hentries;
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_103_split_goal_2 :
  maximum_profit_safety_wit_103_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyQueueExpiring in PreH31.
  destruct PreH31 as [Hqueue | Hqueue];
  unfold StockBuyQueue in Hqueue;
  destruct Hqueue as [_ [Hentries _]];
  specialize (Hentries head ltac:(lia));
  unfold StockFiniteIndexInWindow in Hentries;
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_103 : maximum_profit_safety_wit_103.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_103_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_103_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_112_split_goal_1 :
  maximum_profit_safety_wit_112_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH29.
  destruct PreH29 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day (j - 1) __default__List_Z
    PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_112_split_goal_2 :
  maximum_profit_safety_wit_112_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH29.
  destruct PreH29 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day (j - 1) __default__List_Z
    PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_112 : maximum_profit_safety_wit_112.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_112_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_112_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_119_split_goal_1 :
  maximum_profit_safety_wit_119_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH29.
  destruct PreH29 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day (j - 1) __default__List_Z
    PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_119_split_goal_2 :
  maximum_profit_safety_wit_119_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH29.
  destruct PreH29 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day (j - 1) __default__List_Z
    PreH28 Hdone PreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_119 : maximum_profit_safety_wit_119.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_119_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_119_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_126_split_goal_1 :
  maximum_profit_safety_wit_126_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH30.
  destruct PreH30 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day last_index __default__List_Z
    PreH29 Hdone PreH32 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_126_split_goal_2 :
  maximum_profit_safety_wit_126_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH30.
  destruct PreH30 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day last_index __default__List_Z
    PreH29 Hdone PreH32 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_126 : maximum_profit_safety_wit_126.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_126_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_126_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_135_split_goal_1 :
  maximum_profit_safety_wit_135_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH28.
  destruct PreH28 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day best_index __default__List_Z
    PreH27 Hdone PreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_135_split_goal_2 :
  maximum_profit_safety_wit_135_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH28.
  destruct PreH28 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day best_index __default__List_Z
    PreH27 Hdone PreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_135 : maximum_profit_safety_wit_135.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_135_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_135_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_137_split_goal_1 :
  maximum_profit_safety_wit_137_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH28.
  destruct PreH28 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day best_index __default__List_Z
    PreH27 Hdone PreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_137_split_goal_2 :
  maximum_profit_safety_wit_137_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockBuyProgress in PreH28.
  destruct PreH28 as [Hdone _].
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    source_day best_index __default__List_Z
    PreH27 Hdone PreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_137 : maximum_profit_safety_wit_137.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_137_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_137_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_145_split_goal_1 :
  maximum_profit_safety_wit_145_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH19.
  destruct PreH19 as [Hask [Hbid [Hbuy [Hsell [Hdays [Hstock Hbounds]]]]]].
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_145_split_goal_2 :
  maximum_profit_safety_wit_145_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_maximum_profit_safety_wit_145 : maximum_profit_safety_wit_145.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_145_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_145_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_safety_wit_146_split_goal_1 :
  maximum_profit_safety_wit_146_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH9.
  destruct PreH9 as [Hask [Hbid [Hbuy [Hsell [Hdays [Hstock Hbounds]]]]]].
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_maximum_profit_safety_wit_146_split_goal_2 :
  maximum_profit_safety_wit_146_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_maximum_profit_safety_wit_146 : maximum_profit_safety_wit_146.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_146_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_146_split_goal_2.
Qed.

Lemma proof_of_maximum_profit_entail_wit_3_split_goal_1 :
  maximum_profit_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfill : StockFillRows dp_init days_pre max_stock_pre 0).
  { unfold StockFillRows.
    split; [lia |].
    split; [exact PreH13 |].
    intros r stock Hr Hstock. exfalso; lia. }
  exact Hfill.
Qed.

Lemma proof_of_maximum_profit_entail_wit_3 : maximum_profit_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_4_split_goal_1 :
  maximum_profit_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfill :
    StockFillCells (Znth i dp_l_2 __default__List_Z)
      max_stock_pre i 0).
  { unfold StockFillCells.
    unfold StockInputsBounded in PreH12.
    destruct PreH12 as [_ [_ [_ [_ [_ [Hmax_stock_pre _]]]]]].
    split; [lia |].
    unfold StockFillRows in PreH13.
    destruct PreH13 as [_ [HTableShape Hforall]].
    split.
    - unfold StockTableShape in HTableShape.
      destruct HTableShape as [Hrow Hcol].
      assert (Hi: 0 <= i < days_pre + 1) by lia.
      specialize (Hcol i Hi).
      rewrite <- (same_index_different_default i dp_l_2
        __default__List_Z ltac:(lia)).
      exact Hcol.
    - intros stock Hstock. exfalso; lia. }
  exact Hfill.
Qed.

Lemma proof_of_maximum_profit_entail_wit_4 : maximum_profit_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_5_1 : maximum_profit_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (row' := replace_Znth j 0 (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + i * width * sizeof (INT)) j width 0
         (Znth i dp_l_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold row'.
    pose proof
      (IntArray2.missing_i_merge_to_full
         dp_pre i (days_pre + 1) width dp_l_2 row') as Htable_merge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_pre width i) width row')
      with
      (IntArray.full (dp_pre + i * width * sizeof (INT)) width row')
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold dp_l. cancel.
  - assert (Hvalue : 0 = StockInitialCell i j).
    { subst i j. unfold StockInitialCell.
      destruct (Z.eq_dec 0 0); [reflexivity | contradiction]. }
    pose proof
      (stock_fill_update_step__init_copy
         dp_l_2 days_pre max_stock_pre i j 0 __default__List_Z
         PreH17 PreH18 ltac:(lia) ltac:(lia) Hvalue) as Hstep.
    simpl in Hstep.
    change
      (StockFillRows dp_l days_pre max_stock_pre i /\
       StockFillCells (Znth i dp_l __default__List_Z)
         max_stock_pre i (j + 1)) in Hstep.
    destruct Hstep as [Hrows Hcells].
    split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try (unfold StockFillRows in Hrows; tauto).
Qed.

Lemma proof_of_maximum_profit_entail_wit_5_2 : maximum_profit_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (row' := replace_Znth j neg_inf
    (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + i * width * sizeof (INT)) j width neg_inf
         (Znth i dp_l_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold row'.
    pose proof
      (IntArray2.missing_i_merge_to_full
         dp_pre i (days_pre + 1) width dp_l_2 row') as Htable_merge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_pre width i) width row')
      with
      (IntArray.full (dp_pre + i * width * sizeof (INT)) width row')
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold dp_l. cancel.
  - assert (Hvalue : neg_inf = StockInitialCell i j).
    { subst neg_inf. unfold StockInitialCell.
      destruct (Z.eq_dec i 0); [contradiction | reflexivity]. }
    pose proof
      (stock_fill_update_step__init_copy
         dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z
         PreH16 PreH17 ltac:(lia) ltac:(lia) Hvalue) as Hstep.
    simpl in Hstep.
    change
      (StockFillRows dp_l days_pre max_stock_pre i /\
       StockFillCells (Znth i dp_l __default__List_Z)
         max_stock_pre i (j + 1)) in Hstep.
    destruct Hstep as [Hrows Hcells].
    split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try (unfold StockFillRows in Hrows; tauto).
Qed.

Lemma proof_of_maximum_profit_entail_wit_5_3 : maximum_profit_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (row' := replace_Znth j neg_inf
    (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + i * width * sizeof (INT)) j width neg_inf
         (Znth i dp_l_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold row'.
    pose proof
      (IntArray2.missing_i_merge_to_full
         dp_pre i (days_pre + 1) width dp_l_2 row') as Htable_merge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_pre width i) width row')
      with
      (IntArray.full (dp_pre + i * width * sizeof (INT)) width row')
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold dp_l. cancel.
  - assert (Hvalue : neg_inf = StockInitialCell i j).
    { subst i neg_inf. unfold StockInitialCell.
      destruct (Z.eq_dec 0 0); [|contradiction].
      destruct (Z.eq_dec j 0); [contradiction | reflexivity]. }
    pose proof
      (stock_fill_update_step__init_copy
         dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z
         PreH17 PreH18 ltac:(lia) ltac:(lia) Hvalue) as Hstep.
    simpl in Hstep.
    change
      (StockFillRows dp_l days_pre max_stock_pre i /\
       StockFillCells (Znth i dp_l __default__List_Z)
         max_stock_pre i (j + 1)) in Hstep.
    destruct Hstep as [Hrows Hcells].
    split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    all: try (unfold StockFillRows in Hrows; tauto).
Qed.

Lemma proof_of_maximum_profit_entail_wit_6_split_goal_1 :
  maximum_profit_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfill :
    StockFillRows dp_l_2 days_pre max_stock_pre (i + 1)).
  { unfold StockFillRows in *.
    destruct PreH15 as [_ [HTableShape Hforall]].
    split; [lia |].
    split; [exact HTableShape |].
    intros r stock Hr Hstock.
    destruct (Z_lt_dec r i) as [H_lt | H_ge].
    - apply Hforall; lia.
    - assert (r = i) by lia. subst r.
      assert (j = max_stock_pre + 1) by lia. subst j.
      unfold StockFillCells in PreH16.
      destruct PreH16 as [_ [Hlen Hforall']].
      rewrite (same_index_different_default i dp_l_2
        __default__List_Z ltac:(unfold StockTableShape in HTableShape; lia)).
      split; [exact Hlen |].
      apply Hforall'. exact Hstock. }
  exact Hfill.
Qed.

Lemma proof_of_maximum_profit_entail_wit_6 : maximum_profit_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_7_split_goal_1 :
  maximum_profit_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdone :
    StockDaysDone ap_l bp_l buy_l sell_l dp_l_2
      max_stock_pre wait_days_pre 1).
  { assert (i = days_pre + 1) by lia. subst i.
    exact (proj1
      (stock_completed_initial_table_days_done__init_copy
         ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre
         wait_days_pre ltac:(lia) PreH12 PreH13)). }
  exact Hdone.
Qed.

Lemma proof_of_maximum_profit_entail_wit_7 : maximum_profit_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_9_split_goal_1 :
  maximum_profit_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockCopyProgress.
  split; [exact PreH13 |].
  repeat split; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_9 : maximum_profit_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_maximum_profit_entail_wit_10 : maximum_profit_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
    (IntArray.missing_i_merge_to_full
       (dp_pre + (i - 1) * width * sizeof (INT)) j width
       (Znth j (Znth (i - 1) dp_l __default__List_Z) 0)
       (Znth (i - 1) dp_l __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    dp_pre + (i - 1) * width * sizeof (INT) + j * sizeof (INT) =
    dp_pre + ((i - 1) * width + j) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  change
    (IntArray.full
       (dp_pre + (i - 1) * width * sizeof (INT)) width
       (Znth (i - 1) dp_l __default__List_Z) **
     IntArray2.missing_i dp_pre (i - 1) 0
       (days_pre + 1) width dp_l)
    with
    (IntArray2.ElemArray.full
       (IntArray2.row_addr dp_pre width (i - 1)) width
       (Znth (i - 1) dp_l __default__List_Z) **
     IntArray2.missing_i dp_pre (i - 1) 0
       (days_pre + 1) width dp_l).
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre (i - 1) (days_pre + 1) width dp_l
    (Znth (i - 1) dp_l __default__List_Z)) as Htablemerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre width (i - 1)) width
    (Znth (i - 1) dp_l __default__List_Z)) with
    (IntArray.full (dp_pre + (i - 1) * width * sizeof (INT)) width
      (Znth (i - 1) dp_l __default__List_Z)) in Htablemerge.
  sep_apply Htablemerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_11 : maximum_profit_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (row' := replace_Znth j previous_value
      (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         (dp_pre + i * width * sizeof (INT)) j width previous_value
         (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + i * width * sizeof (INT) + j * sizeof (INT) =
      dp_pre + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    fold row'.
    change
      (IntArray.full (dp_pre + i * width * sizeof (INT)) width row')
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr dp_pre width i) width row').
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre i (days_pre + 1) width dp_l_2 row') as Htablemerge.
    sep_apply Htablemerge; try lia.
    fold dp_l. cancel.
  - assert (HshapeA : StockTableShape dp_l_2 (Zlength ap_l) max_stock_pre).
    { unfold StockCopyProgress in PreH16.
      destruct PreH16 as [HD _]. unfold StockDaysDone in HD. tauto. }
    assert (Hasklen : Zlength ap_l = days_pre).
    { unfold StockTableShape in HshapeA, PreH17.
      destruct HshapeA as [HA _]. destruct PreH17 as [HD _]. lia. }
    assert (Hprev : 0 <= i - 1 < Zlength dp_l_2).
    { unfold StockTableShape in PreH17. destruct PreH17 as [Hlen _]. lia. }
    assert (Hcur : 0 <= i < Zlength dp_l_2).
    { unfold StockTableShape in PreH17. destruct PreH17 as [Hlen _]. lia. }
    assert (Hvalue0 : previous_value = Znth j (Znth (i - 1) dp_l_2 nil) 0).
    { rewrite (Znth_indep dp_l_2 (i - 1) __default__List_Z nil)
        in PreH14 by exact Hprev. exact PreH14. }
    assert (Hroweq : row' = replace_Znth j previous_value (Znth i dp_l_2 nil)).
    { unfold row'. rewrite (Znth_indep dp_l_2 i __default__List_Z nil)
        by exact Hcur. reflexivity. }
    pose proof
      (stock_copy_update_step__init_copy
        ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre
        i j previous_value HshapeA PreH16 Hvalue0
        ltac:(rewrite Hasklen; lia) ltac:(lia) ltac:(lia)) as Hstep.
    simpl in Hstep. rewrite <- Hroweq in Hstep.
    change
      (StockCopyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre
         wait_days_pre i (j + 1) /\
       StockTableShape dp_l (Zlength ap_l) max_stock_pre) in Hstep.
    destruct Hstep as [Hcopy' Hshape'].
    rewrite Hasklen in Hshape'. split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12_split_goal_1 :
  maximum_profit_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH15 as Hinputs.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]].
  unfold StockEarlyBuyProgress.
  unfold StockCopyProgress in PreH16.
  destruct PreH16 as [HD [Hi [Hcol Hcopy]]].
  split; [exact HD |].
  split; [exact Hi |].
  split; [lia |].
  split.
  - apply Hcopy; lia.
  - intros stock Hstock.
    destruct (Z_lt_dec stock 1); [lia |].
    apply Hcopy; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12_split_goal_2 :
  maximum_profit_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12_split_goal_3 :
  maximum_profit_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [Haskmax _]]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12_split_goal_4 :
  maximum_profit_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [Hbidask _]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12_split_goal_5 :
  maximum_profit_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12_split_goal_6 :
  maximum_profit_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StockInputsBounded in PreH15.
  destruct PreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12 : maximum_profit_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_12_split_goal_6.
Qed.

