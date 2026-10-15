import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part3
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


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_1 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellQueue dp_l_2 queue_l_2 source_day bid_price ((j - 1) + 2) (((j - 1) + sell_cap) + 1) head tail)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  simpa only [show j - 1 + 2 = j + 1 by omega, show j - 1 + sell_cap + 1 = j + sell_cap by omega] using PreH24


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_2 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day (j - 1))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hcells,Hlast⟩
  refine ⟨HD,Hi,Hsrc,Hsr,by omega,?_,?_,Hlast⟩
  · intro stock hs; exact Hcopy stock (by omega)
  · intro stock hs
    by_cases he : stock = j
    · subst stock
      refine ⟨⟨0,Or.inl ⟨rfl,Hcopy j (by omega)⟩⟩,?_⟩
      intro amount candidate hc
      rcases hc with ⟨ha,hc⟩ | ⟨ha,hs,hn,hc⟩
      · have hv := Hcopy j (by omega); omega
      · have hrow := PreH25.2 source_day (by omega)
        have hq := PreH24.2.2.2 (j+amount) ⟨by omega,by omega,hn,by omega⟩
        obtain ⟨pos,hp,_⟩ := hq
        omega
    · exact Hcells stock (by omega)


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_3 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (sell_cap <= max_stock_pre)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_4 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= sell_cap)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_5 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (bid_price <= 1000)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_6 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (1 <= bid_price)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hb := PreH22
  unfold StockInputsBounded at hb
  have hdaily := hb.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_7 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  ((0 : Int) < source_day)) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega


theorem stock_aux_maximum_profit_entail_wit_26_3_split_goal_8 : (forall (wait_days_pre : Int) (max_stock_pre : Int) (days_pre : Int) (sell_l : (List Int)) (buy_l : (List Int)) (bp_l : (List Int)) (ap_l : (List Int)) (queue_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (neg_inf : Int) (width : Int) (i : Int) (source_day : Int) (j : Int) (bid_price : Int) (sell_cap : Int) (head : Int) (tail : Int) (PreH1 : (head >= tail)) (PreH2 : (neg_inf = (-1000000000))) (PreH3 : (width = (max_stock_pre + 1))) (PreH4 : (1 <= days_pre)) (PreH5 : (days_pre <= 990)) (PreH6 : (1 <= max_stock_pre)) (PreH7 : (max_stock_pre <= 990)) (PreH8 : ((0 : Int) <= wait_days_pre)) (PreH9 : (wait_days_pre < days_pre)) (PreH10 : (wait_days_pre < (i - 1))) (PreH11 : (1 <= i)) (PreH12 : (i <= days_pre)) (PreH13 : ((0 : Int) <= source_day)) (PreH14 : (source_day < i)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j < max_stock_pre)) (PreH17 : (bid_price = (Znth (i - 1) bp_l (0 : Int)))) (PreH18 : (sell_cap = (Znth (i - 1) sell_l (0 : Int)))) (PreH19 : ((0 : Int) <= head)) (PreH20 : (head <= tail)) (PreH21 : (tail <= (max_stock_pre - j))) (PreH22 : (StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre)) (PreH23 : (StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j)) (PreH24 : (StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j + 1) (j + sell_cap) head tail)) (PreH25 : (StockTableShape dp_l_2 days_pre max_stock_pre)) ,
  (source_day = ((i - wait_days_pre) - 1))) := by
  intro wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  rcases PreH23 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hrest⟩
  omega

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part3
