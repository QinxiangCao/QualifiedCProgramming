import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part5
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open stock_trading_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2

local macro "finish_entail" : tactic => `(tactic| (
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto))

private theorem product_bounds (x p : Int) (hx : 0 ≤ x ∧ x ≤ 990)
    (hp : 0 ≤ p ∧ p ≤ 1000) : 0 ≤ x*p ∧ x*p ≤ 990000 :=
  ⟨Int.mul_nonneg hx.1 hp.1, Int.mul_le_mul hx.2 hp.2 hp.1 (by omega)⟩


theorem stock_aux_maximum_profit_entail_wit_36_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((Znth head queue_l (0 : Int)) <= max_stock_pre)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have he := PreH25.2.1 head (by omega)
  rcases he with ⟨he0,hel,hef,her⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_36_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((0 : Int) <= (Znth head queue_l (0 : Int)))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  exact (PreH25.2.1 head (by omega)).1


theorem stock_aux_maximum_profit_entail_wit_36_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (ask_price <= 1000)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_36_split_goal_4 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((0 : Int) <= ask_price)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (((j + 1) - buy_cap) - 1) ((j + 1) - 2) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simpa only [show j + 1 - buy_cap - 1 = j - buy_cap by omega, show j + 1 - 2 = j - 1 by omega] using PreH25


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day (j + 1))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hrow := PreH26.2 source_day (by omega)
  apply StockBuyProgress_step_same__buy_cell_progress
  · exact PreH24
  · omega
  · apply StockBuyCellValue_empty_queue__buy_cell_progress
    all_goals first | assumption | omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (buy_cap <= max_stock_pre)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_4 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= buy_cap)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_5 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (ask_price <= 1000)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_6 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= ask_price)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hb := PreH23
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_7 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((0 : Int) < source_day)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rcases PreH24 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_8 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (source_day = ((i - wait_days_pre) - 1))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rcases PreH24 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_38_3_split_goal_9 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (ask_price : Int) (buy_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : ((0 : Int) <= source_day)) (PreH13 : (source_day < i)) (PreH14 : (1 <= j)) (PreH15 : (j <= max_stock_pre)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH19 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= j)) (PreH23 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH24 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH25 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 1) head tail)) (PreH26 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (wait_days_pre < (i - 1))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  rcases PreH24 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_41_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (dp_l_2 : (List (List Int))) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (i > days_pre)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= (days_pre + 1))) (PreH12 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH13 : (StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i)) (PreH14 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockAnswerProgress ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre (0 : Int) (0 : Int))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hi := PreH12
  unfold StockInputsBounded at hi
  apply stock_answer_init__outer_answer
  all_goals first | assumption | omega

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part5
