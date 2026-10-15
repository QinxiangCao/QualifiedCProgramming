import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part2
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


theorem stock_aux_maximum_profit_entail_wit_15_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (j : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : ((i - 1) > wait_days_pre)) (PreH2 : (j > max_stock_pre)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (max_stock_pre + 1))) (PreH15 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH16 : (StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j)) (PreH17 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) (Znth (i - 1) bp_l (0 : Int)) ((max_stock_pre - 1) + 2) (((max_stock_pre - 1) + (Znth (i - 1) sell_l (0 : Int))) + 1) (0 : Int) (0 : Int))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro pos hp; omega
  · intro l r hr; omega
  · intro candidate hc
    have hrow := PreH17.2 (i - wait_days_pre - 1) (by omega)
    rcases hc with ⟨hc0,hcl,hcf,hcr⟩
    omega


theorem stock_aux_maximum_profit_entail_wit_15_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (dp_l_2 : (List (List Int))) (j : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : ((i - 1) > wait_days_pre)) (PreH2 : (j > max_stock_pre)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (max_stock_pre + 1))) (PreH15 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH16 : (StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j)) (PreH17 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) (max_stock_pre - 1))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hlen := PreH15.1
  rcases PreH16 with ⟨HD,Hi,Hcol,Hcells⟩
  refine ⟨HD, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro stock hs; exact Hcells stock (by omega)
  · intro stock hs; omega
  · exact Hcells max_stock_pre (by omega)


theorem stock_aux_maximum_profit_entail_wit_15_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (dp_l_2 : (List (List Int))) (j : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : ((i - 1) > wait_days_pre)) (PreH2 : (j > max_stock_pre)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (max_stock_pre + 1))) (PreH15 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH16 : (StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j)) (PreH17 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((Znth (i - 1) sell_l (0 : Int)) <= max_stock_pre)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_15_split_goal_4 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (dp_l_2 : (List (List Int))) (j : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : ((i - 1) > wait_days_pre)) (PreH2 : (j > max_stock_pre)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (max_stock_pre + 1))) (PreH15 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH16 : (StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j)) (PreH17 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= (Znth (i - 1) sell_l (0 : Int)))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_15_split_goal_5 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (dp_l_2 : (List (List Int))) (j : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : ((i - 1) > wait_days_pre)) (PreH2 : (j > max_stock_pre)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (max_stock_pre + 1))) (PreH15 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH16 : (StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j)) (PreH17 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((Znth (i - 1) bp_l (0 : Int)) <= 1000)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_15_split_goal_6 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (dp_l_2 : (List (List Int))) (j : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : ((i - 1) > wait_days_pre)) (PreH2 : (j > max_stock_pre)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (max_stock_pre + 1))) (PreH15 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH16 : (StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j)) (PreH17 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= (Znth (i - 1) bp_l (0 : Int)))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hdaily := PreH15.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_16_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j >= (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2) (j + sell_cap) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rw [← PreH13]
  left
  simpa only [show j + sell_cap + 1 = j + (sell_cap + 1) by omega] using PreH29


theorem stock_aux_maximum_profit_entail_wit_17_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (bid_price : Int) (tail : Int) (head : Int) (sell_cap : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (((Znth head queue_l_2 (0 : Int)) - sell_cap) > j)) (PreH2 : (head < tail)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : ((0 : Int) <= wait_days_pre)) (PreH6 : (wait_days_pre < days_pre)) (PreH7 : (1 <= days_pre)) (PreH8 : (days_pre <= 990)) (PreH9 : (1 <= max_stock_pre)) (PreH10 : (max_stock_pre <= 990)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : (wait_days_pre < (i - 1))) (PreH14 : (source_day = ((i - wait_days_pre) - 1))) (PreH15 : ((0 : Int) < source_day)) (PreH16 : (source_day < i)) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j < max_stock_pre)) (PreH19 : (1 <= sell_cap)) (PreH20 : (sell_cap <= max_stock_pre)) (PreH21 : ((0 : Int) <= head)) (PreH22 : (head <= tail)) (PreH23 : (tail <= ((max_stock_pre - j) - 1))) (PreH24 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH25 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH26 : (1 <= bid_price)) (PreH27 : (bid_price <= 1000)) (PreH28 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH29 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH30 : (StockSellQueueExpiring dp_l_2 queue_l_2 source_day bid_price (j + 2) (j + sell_cap) head tail)) (PreH31 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2) (j + sell_cap) (head + 1) tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rw [← PreH14]
  right
  apply StockSellQueue_drop_expired__sell_expire
  all_goals first | assumption | omega


theorem stock_aux_maximum_profit_entail_wit_18_1_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (bid_price : Int) (tail : Int) (head : Int) (sell_cap : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j < max_stock_pre)) (PreH18 : (1 <= sell_cap)) (PreH19 : (sell_cap <= max_stock_pre)) (PreH20 : ((0 : Int) <= head)) (PreH21 : (head <= tail)) (PreH22 : (tail <= ((max_stock_pre - j) - 1))) (PreH23 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH24 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH25 : (1 <= bid_price)) (PreH26 : (bid_price <= 1000)) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueueExpiring dp_l_2 queue_l_2 source_day bid_price (j + 2) (j + sell_cap) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2) (j + sell_cap) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rw [← PreH13]
  apply StockSellQueueExpiring_empty__sell_expire
  all_goals first | assumption | omega


theorem stock_aux_maximum_profit_entail_wit_18_2_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (bid_price : Int) (tail : Int) (head : Int) (sell_cap : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (((Znth head queue_l_2 (0 : Int)) - sell_cap) <= j)) (PreH2 : (head < tail)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : ((0 : Int) <= wait_days_pre)) (PreH6 : (wait_days_pre < days_pre)) (PreH7 : (1 <= days_pre)) (PreH8 : (days_pre <= 990)) (PreH9 : (1 <= max_stock_pre)) (PreH10 : (max_stock_pre <= 990)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : (wait_days_pre < (i - 1))) (PreH14 : (source_day = ((i - wait_days_pre) - 1))) (PreH15 : ((0 : Int) < source_day)) (PreH16 : (source_day < i)) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j < max_stock_pre)) (PreH19 : (1 <= sell_cap)) (PreH20 : (sell_cap <= max_stock_pre)) (PreH21 : ((0 : Int) <= head)) (PreH22 : (head <= tail)) (PreH23 : (tail <= ((max_stock_pre - j) - 1))) (PreH24 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH25 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH26 : (1 <= bid_price)) (PreH27 : (bid_price <= 1000)) (PreH28 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH29 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH30 : (StockSellQueueExpiring dp_l_2 queue_l_2 source_day bid_price (j + 2) (j + sell_cap) head tail)) (PreH31 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2) (j + sell_cap) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rw [← PreH14]
  apply StockSellQueueExpiring_head_bounded__sell_expire
  all_goals first | assumption | omega


theorem stock_aux_maximum_profit_entail_wit_18_2_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (bid_price : Int) (tail : Int) (head : Int) (sell_cap : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (((Znth head queue_l_2 (0 : Int)) - sell_cap) <= j)) (PreH2 : (head < tail)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : ((0 : Int) <= wait_days_pre)) (PreH6 : (wait_days_pre < days_pre)) (PreH7 : (1 <= days_pre)) (PreH8 : (days_pre <= 990)) (PreH9 : (1 <= max_stock_pre)) (PreH10 : (max_stock_pre <= 990)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : (wait_days_pre < (i - 1))) (PreH14 : (source_day = ((i - wait_days_pre) - 1))) (PreH15 : ((0 : Int) < source_day)) (PreH16 : (source_day < i)) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j < max_stock_pre)) (PreH19 : (1 <= sell_cap)) (PreH20 : (sell_cap <= max_stock_pre)) (PreH21 : ((0 : Int) <= head)) (PreH22 : (head <= tail)) (PreH23 : (tail <= ((max_stock_pre - j) - 1))) (PreH24 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH25 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH26 : (1 <= bid_price)) (PreH27 : (bid_price <= 1000)) (PreH28 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH29 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH30 : (StockSellQueueExpiring dp_l_2 queue_l_2 source_day bid_price (j + 2) (j + sell_cap) head tail)) (PreH31 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((head < tail) -> (j <= (Znth head queue_l_2 (0 : Int))))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  rcases PreH30 with hq | hq
  all_goals
    have he := hq.2.1 head (by omega)
    have hi := he.2.2.2
    omega


theorem stock_aux_maximum_profit_entail_wit_24_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((Znth head queue_l (0 : Int)) <= max_stock_pre)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have he := PreH24.2.1 head (by omega)
  have hrow := PreH25.2 source_day (by omega)
  rcases he with ⟨he0,hel,hef,her⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_24_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((0 : Int) <= (Znth head queue_l (0 : Int)))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact (PreH24.2.1 head (by omega)).1


theorem stock_aux_maximum_profit_entail_wit_24_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (bid_price <= 1000)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_24_split_goal_4 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head < tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((0 : Int) <= bid_price)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part2
