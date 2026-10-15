import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part4
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


theorem stock_aux_maximum_profit_entail_wit_27_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j < (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) (Znth (i - 1) ap_l (0 : Int)) ((1 - (Znth (i - 1) buy_l (0 : Int))) - 1) (1 - 2) (0 : Int) (0 : Int))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro pos hp; omega
  · intro l r hr; omega
  · intro candidate hc
    rcases hc with ⟨hc0,hcl,hcf,hcr⟩
    omega


theorem stock_aux_maximum_profit_entail_wit_27_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j < (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) 1)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  rcases PreH28 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hsell,Hmaxeq⟩
  refine ⟨HD,Hi,rfl,by omega,by omega,?_,?_⟩
  · intro stock hs
    have he : stock = 0 := by omega
    subst stock
    have hsell := Hsell 0 (by omega)
    rw [Hsrc] at hsell
    refine ⟨⟨⟨0,Or.inl ⟨rfl,hsell⟩⟩,?_⟩,⟨_,hsell⟩⟩
    intro amount candidate hc
    rcases hc with ⟨ha,hc⟩ | ⟨ha,hamt,hn,hc⟩
    · obtain ⟨sa,hsa⟩ := hc.1
      exact hsell.2 sa candidate hsa
    · omega
  · intro stock hs
    by_cases he : stock = max_stock_pre
    · subst stock
      refine ⟨⟨0,Or.inl ⟨rfl,Hmaxeq⟩⟩,?_⟩
      intro amount candidate hc
      rcases hc with ⟨ha,hc⟩ | ⟨ha,hamt,hn,hc⟩ <;> omega
    · rw [← Hsrc]
      exact Hsell stock (by omega)


theorem stock_aux_maximum_profit_entail_wit_27_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j < (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((Znth (i - 1) buy_l (0 : Int)) <= max_stock_pre)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_27_split_goal_4 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j < (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= (Znth (i - 1) buy_l (0 : Int)))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_27_split_goal_5 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j < (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((Znth (i - 1) ap_l (0 : Int)) <= 1000)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_27_split_goal_6 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j < (0 : Int))) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= days_pre)) (PreH7 : (days_pre <= 990)) (PreH8 : (1 <= max_stock_pre)) (PreH9 : (max_stock_pre <= 990)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH17 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH18 : (1 <= bid_price)) (PreH19 : (bid_price <= 1000)) (PreH20 : (1 <= sell_cap)) (PreH21 : (sell_cap <= max_stock_pre)) (PreH22 : ((-1) <= j)) (PreH23 : (j <= (max_stock_pre - 1))) (PreH24 : ((0 : Int) <= head)) (PreH25 : (head <= tail)) (PreH26 : (tail <= ((max_stock_pre - j) - 1))) (PreH27 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH28 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH29 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 2) ((j + sell_cap) + 1) head tail)) (PreH30 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= (Znth (i - 1) ap_l (0 : Int)))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb := PreH27
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_28_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (buy_cap : Int) (ask_price : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j <= max_stock_pre)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= days_pre)) (PreH8 : (wait_days_pre < (i - 1))) (PreH9 : (source_day = ((i - wait_days_pre) - 1))) (PreH10 : ((0 : Int) < source_day)) (PreH11 : (source_day < i)) (PreH12 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH13 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH14 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH15 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH16 : (1 <= ask_price)) (PreH17 : (ask_price <= 1000)) (PreH18 : (1 <= buy_cap)) (PreH19 : (buy_cap <= max_stock_pre)) (PreH20 : (1 <= j)) (PreH21 : (j <= (max_stock_pre + 1))) (PreH22 : ((0 : Int) <= head)) (PreH23 : (head <= tail)) (PreH24 : (tail <= (j - 1))) (PreH25 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH26 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH27 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price ((j - buy_cap) - 1) (j - 2) head tail)) (PreH28 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 2) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  left
  rw [← PreH9]
  exact PreH27


theorem stock_aux_maximum_profit_entail_wit_28_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (buy_cap : Int) (ask_price : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j <= max_stock_pre)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= days_pre)) (PreH8 : (wait_days_pre < (i - 1))) (PreH9 : (source_day = ((i - wait_days_pre) - 1))) (PreH10 : ((0 : Int) < source_day)) (PreH11 : (source_day < i)) (PreH12 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH13 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH14 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH15 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH16 : (1 <= ask_price)) (PreH17 : (ask_price <= 1000)) (PreH18 : (1 <= buy_cap)) (PreH19 : (buy_cap <= max_stock_pre)) (PreH20 : (1 <= j)) (PreH21 : (j <= (max_stock_pre + 1))) (PreH22 : ((0 : Int) <= head)) (PreH23 : (head <= tail)) (PreH24 : (tail <= (j - 1))) (PreH25 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH26 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH27 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price ((j - buy_cap) - 1) (j - 2) head tail)) (PreH28 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (max_stock_pre <= 990)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_28_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (j : Int) (buy_cap : Int) (ask_price : Int) (sell_cap : Int) (bid_price : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (j <= max_stock_pre)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : ((0 : Int) <= wait_days_pre)) (PreH5 : (wait_days_pre < days_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= days_pre)) (PreH8 : (wait_days_pre < (i - 1))) (PreH9 : (source_day = ((i - wait_days_pre) - 1))) (PreH10 : ((0 : Int) < source_day)) (PreH11 : (source_day < i)) (PreH12 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH13 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH14 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH15 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH16 : (1 <= ask_price)) (PreH17 : (ask_price <= 1000)) (PreH18 : (1 <= buy_cap)) (PreH19 : (buy_cap <= max_stock_pre)) (PreH20 : (1 <= j)) (PreH21 : (j <= (max_stock_pre + 1))) (PreH22 : ((0 : Int) <= head)) (PreH23 : (head <= tail)) (PreH24 : (tail <= (j - 1))) (PreH25 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH26 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH27 : (StockBuyQueue dp_l_2 queue_l_2 source_day ask_price ((j - buy_cap) - 1) (j - 2) head tail)) (PreH28 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (days_pre <= 990)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := PreH25
  unfold StockInputsBounded at hb
  rcases hb with ⟨ha,hb,hc,hd,he,hf,hg⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_29_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (buy_cap : Int) (ask_price : Int) (sell_cap : Int) (bid_price : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (((Znth head queue_l_2 (0 : Int)) + buy_cap) < j)) (PreH2 : (head < tail)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : (wait_days_pre < (i - 1))) (PreH14 : (source_day = ((i - wait_days_pre) - 1))) (PreH15 : ((0 : Int) < source_day)) (PreH16 : (source_day < i)) (PreH17 : (1 <= j)) (PreH18 : (j <= max_stock_pre)) (PreH19 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH20 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH21 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH22 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH23 : (1 <= buy_cap)) (PreH24 : (buy_cap <= max_stock_pre)) (PreH25 : (1 <= ask_price)) (PreH26 : (ask_price <= 1000)) (PreH27 : ((0 : Int) <= head)) (PreH28 : (head <= tail)) (PreH29 : (tail <= (j - 1))) (PreH30 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH31 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH32 : (StockBuyQueueExpiring dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 2) head tail)) (PreH33 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 2) (head + 1) tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rw [← PreH14]
  rcases PreH32 with hq | hq
  · right
    rcases hq with ⟨hb,he,ho,hc⟩
    have hhead := he head (by omega)
    have hheadrange := hhead.2.2.2
    refine ⟨by omega,?_,?_,?_⟩
    · intro pos hp
      rcases he pos (by omega) with ⟨hp0,hpl,hpv,hpr⟩
      have hh := (ho head pos (by omega)).1
      exact ⟨hp0,hpl,hpv,by omega⟩
    · intro l r hr; exact ho l r (by omega)
    · intro candidate hh
      rcases hh with ⟨h0,hl,hv,hr⟩
      obtain ⟨pos,hp,hindex,hscore⟩ := hc candidate ⟨h0,hl,hv,by omega⟩
      have hne : pos ≠ head := by intro heq; subst pos; omega
      exact ⟨pos,by omega,hindex,hscore⟩
  · have hh := (hq.2.1 head (by omega)).2.2.2
    omega


theorem stock_aux_maximum_profit_entail_wit_30_1_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (buy_cap : Int) (ask_price : Int) (sell_cap : Int) (bid_price : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= days_pre)) (PreH12 : (wait_days_pre < (i - 1))) (PreH13 : (source_day = ((i - wait_days_pre) - 1))) (PreH14 : ((0 : Int) < source_day)) (PreH15 : (source_day < i)) (PreH16 : (1 <= j)) (PreH17 : (j <= max_stock_pre)) (PreH18 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH19 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH20 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH21 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH22 : (1 <= buy_cap)) (PreH23 : (buy_cap <= max_stock_pre)) (PreH24 : (1 <= ask_price)) (PreH25 : (ask_price <= 1000)) (PreH26 : ((0 : Int) <= head)) (PreH27 : (head <= tail)) (PreH28 : (tail <= (j - 1))) (PreH29 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH30 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH31 : (StockBuyQueueExpiring dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 2) head tail)) (PreH32 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 2) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  rw [← PreH13]
  rcases PreH31 with hq | hq
  · rcases hq with ⟨hb,he,ho,hc⟩
    refine ⟨hb,?_,?_,?_⟩
    · intro pos hp; omega
    · intro l r hr; omega
    · intro candidate hh
      rcases hh with ⟨h0,hl,hv,hr⟩
      exact hc candidate ⟨h0,hl,hv,by omega⟩
  · exact hq


theorem stock_aux_maximum_profit_entail_wit_30_2_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (tail : Int) (head : Int) (buy_cap : Int) (ask_price : Int) (sell_cap : Int) (bid_price : Int) (j : Int) (source_day : Int) (i : Int) (width : Int) (neg_inf : Int) (PreH1 : (((Znth head queue_l_2 (0 : Int)) + buy_cap) >= j)) (PreH2 : (head < tail)) (PreH3 : (neg_inf = (-1000000000))) (PreH4 : (width = (max_stock_pre + 1))) (PreH5 : (1 <= days_pre)) (PreH6 : (days_pre <= 990)) (PreH7 : (1 <= max_stock_pre)) (PreH8 : (max_stock_pre <= 990)) (PreH9 : ((0 : Int) <= wait_days_pre)) (PreH10 : (wait_days_pre < days_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : (wait_days_pre < (i - 1))) (PreH14 : (source_day = ((i - wait_days_pre) - 1))) (PreH15 : ((0 : Int) < source_day)) (PreH16 : (source_day < i)) (PreH17 : (1 <= j)) (PreH18 : (j <= max_stock_pre)) (PreH19 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH20 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH21 : (ask_price = (Znth (i - 1) ap_l (0 : Int)))) (PreH22 : (buy_cap = (Znth (i - 1) buy_l (0 : Int)))) (PreH23 : (1 <= buy_cap)) (PreH24 : (buy_cap <= max_stock_pre)) (PreH25 : (1 <= ask_price)) (PreH26 : (ask_price <= 1000)) (PreH27 : ((0 : Int) <= head)) (PreH28 : (head <= tail)) (PreH29 : (tail <= (j - 1))) (PreH30 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH31 : (StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH32 : (StockBuyQueueExpiring dp_l_2 queue_l_2 source_day ask_price (j - buy_cap) (j - 2) head tail)) (PreH33 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 2) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  rw [← PreH14]
  rcases PreH32 with hq | hq
  · rcases hq with ⟨hb,he,ho,hc⟩
    refine ⟨hb,?_,ho,?_⟩
    · intro pos hp
      rcases he pos hp with ⟨h0,hl,hv,hr⟩
      have hlo : j-buy_cap ≤ Znth pos queue_l_2 0 := by
        by_cases heq : pos = head
        · subst pos; omega
        · have hh := (ho head pos (by omega)).1
          omega
      exact ⟨h0,hl,hv,by omega⟩
    · intro candidate hh
      rcases hh with ⟨h0,hl,hv,hr⟩
      exact hc candidate ⟨h0,hl,hv,by omega⟩
  · exact hq

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part4
