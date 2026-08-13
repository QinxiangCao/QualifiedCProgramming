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
  exact Hexp.
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
  exact Hexp.
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
  exact Hqueue.
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
  exact Hqueue.
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
  split; [exact Hsource |].
  split; [exact Hsrange |].
  split; [lia |].
  split.
  - intros stock Hstock.
    assert (stock = 0) by lia. subst stock.
    pose proof (Hsell 0 ltac:(lia)) as Hsell0.
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
    + apply Hsell. lia.
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
  unfold StockBuyQueueExpiring. left. exact PreH27.
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
      assert (head < pos) by
        (destruct (Z.eq_dec pos head) as [Heq | Hneq]; [subst pos |]; lia).
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
