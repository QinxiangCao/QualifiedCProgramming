import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal
import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open rod_cutting_goal rod_cutting_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

-- Preserve the original closed helper contracts and their proved terms.
private noncomputable def legacy_rod_cutting_entail_wit_2_split_goal_1 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))


private noncomputable def legacy_rod_cutting_entail_wit_2_split_goal_2 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j 1 (0 : Int))


private noncomputable def legacy_rod_cutting_entail_wit_2_split_goal_3 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))


private noncomputable def legacy_rod_cutting_entail_wit_4_1_split_goal_1 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))


private noncomputable def legacy_rod_cutting_entail_wit_4_2_split_goal_1 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1) best)


private noncomputable def legacy_rod_cutting_entail_wit_5_split_goal_1 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (j + 1))) -> (((0 : Int) <= (Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int))) ∧ ((Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int)) <= (k_2 * 1000000))))


private noncomputable def legacy_rod_cutting_entail_wit_5_split_goal_2 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (RodCutRevenueTable price_l (revenue_l_2 ++ (best :: (@List.nil Int))) (j + 1))


private noncomputable def legacy_rod_cutting_entail_wit_5_split_goal_3 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  ((Zlength ((revenue_l_2 ++ (best :: (@List.nil Int))))) = (j + 1))


private noncomputable def legacy_rod_cutting_entail_wit_5_split_goal_4 : Prop :=

  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))


private noncomputable def legacy_rod_cutting_entail_wit_1 : Prop :=

  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) ,
  (((revenue_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg revenue_pre 1 (n_pre + 1))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = 1) ” &&
  “ (RodCutRevenueTable price_l revenue_l 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 1)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) 1 revenue_l)
  ** (intArray.undef_seg revenue_pre 1 (n_pre + 1))
) \/
(
forall (n_pre : Int) (revenue_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (price_l)) = (n_pre + 1))) (PreH6 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) ,
  (((revenue_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = 1) ” &&
  “ (RodCutRevenueTable price_l revenue_l 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < 1)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.seg revenue_pre (0 : Int) 1 revenue_l)
)


private noncomputable def legacy_rod_cutting_entail_wit_2 : Prop :=

  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j 1 (0 : Int)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000)))) ” &&
  “ (RodCutScanBest price_l revenue_l_2 j 1 (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ”
  &&  emp
)


private noncomputable def legacy_rod_cutting_entail_wit_4_1 : Prop :=

  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((0 : Int) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))) <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ”
  &&  emp
)


private noncomputable def legacy_rod_cutting_entail_wit_4_2 : Prop :=

  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ ((Zlength (revenue_l)) = j) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j (i + 1) best) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) j revenue_l)
  ** (intArray.undef_seg revenue_pre j (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : ((0 : Int) <= (j - i))) (PreH3 : ((j - i) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1))) (PreH12 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1))) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= (j * 1000000))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1) best) ”
  &&  emp
)


private noncomputable def legacy_rod_cutting_entail_wit_5 : Prop :=

  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) (j + 1) (revenue_l_2 ++ (best :: (@List.nil Int))))
  ** (intArray.undef_seg revenue_pre (j + 1) (n_pre + 1))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (revenue_l)) = (j + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (j + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (j + 1))) -> (((0 : Int) <= (Znth k_2 revenue_l (0 : Int))) ∧ ((Znth k_2 revenue_l (0 : Int)) <= (k_2 * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg revenue_pre (0 : Int) (j + 1) revenue_l)
  ** (intArray.undef_seg revenue_pre (j + 1) (n_pre + 1))
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 price_l (0 : Int))) ∧ ((Znth k_3 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1))) (PreH11 : ((0 : Int) <= best)) (PreH12 : (best <= (j * 1000000))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH16 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < j)) -> (((0 : Int) <= (Znth k_4 revenue_l_2 (0 : Int))) ∧ ((Znth k_4 revenue_l_2 (0 : Int)) <= (k_4 * 1000000))))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (j + 1))) -> (((0 : Int) <= (Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int))) ∧ ((Znth k_2 (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int)) <= (k_2 * 1000000)))) ” &&
  “ (RodCutRevenueTable price_l (revenue_l_2 ++ (best :: (@List.nil Int))) (j + 1)) ” &&
  “ ((Zlength ((revenue_l_2 ++ (best :: (@List.nil Int))))) = (j + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k <= n_pre)) -> (((0 : Int) <= (Znth k price_l (0 : Int))) ∧ ((Znth k price_l (0 : Int)) <= 1000000))) ”
  &&  emp
)


private noncomputable def legacy_rod_cutting_return_wit_1 : Prop :=

  (
forall (n_pre : Int) (revenue_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 price_l (0 : Int))) ∧ ((Znth k_2 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < j)) -> (((0 : Int) <= (Znth k_3 revenue_l_2 (0 : Int))) ∧ ((Znth k_3 revenue_l_2 (0 : Int)) <= (k_3 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ ((Zlength (revenue_l)) = (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (n_pre + 1)) ” &&
  “ ((Znth (n_pre - (0 : Int)) revenue_l_2 (0 : Int)) = (Znth n_pre revenue_l (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre + 1))) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.full revenue_pre (n_pre + 1) revenue_l)
) \/
(
forall (n_pre : Int) (revenue_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1))) (PreH5 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 price_l (0 : Int))) ∧ ((Znth k_2 price_l (0 : Int)) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH11 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < j)) -> (((0 : Int) <= (Znth k_3 revenue_l_2 (0 : Int))) ∧ ((Znth k_3 revenue_l_2 (0 : Int)) <= (k_3 * 1000000))))) ,
  (intArray.seg revenue_pre (0 : Int) j revenue_l_2)
|--
  EX revenue_l : (List Int),
  “ ((Zlength (revenue_l)) = (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (n_pre + 1)) ” &&
  “ ((Znth (n_pre - (0 : Int)) revenue_l_2 (0 : Int)) = (Znth n_pre revenue_l (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (n_pre + 1))) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full revenue_pre (n_pre + 1) revenue_l)
)


theorem legacy_proof_of_rod_cutting_entail_wit_2_split_goal_1 : legacy_rod_cutting_entail_wit_2_split_goal_1 := by
  unfold legacy_rod_cutting_entail_wit_2_split_goal_1
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH11

theorem legacy_proof_of_rod_cutting_entail_wit_2_split_goal_2 : legacy_rod_cutting_entail_wit_2_split_goal_2 := by
  unfold legacy_rod_cutting_entail_wit_2_split_goal_2
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact Or.inr ⟨fun piece hp => False.elim (by omega), rfl⟩

theorem legacy_proof_of_rod_cutting_entail_wit_2_split_goal_3 : legacy_rod_cutting_entail_wit_2_split_goal_3 := by
  unfold legacy_rod_cutting_entail_wit_2_split_goal_3
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH6

theorem legacy_proof_of_rod_cutting_entail_wit_4_1_split_goal_1 : legacy_rod_cutting_entail_wit_4_1_split_goal_1 := by
  unfold legacy_rod_cutting_entail_wit_4_1_split_goal_1
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [Int.sub_zero] at PreH1 ⊢
  apply rod_cut_scan_best_step__scan_transitions _ i best _ PreH16 PreH22
  left
  exact ⟨by omega, rfl⟩

theorem legacy_proof_of_rod_cutting_entail_wit_4_2_split_goal_1 : legacy_rod_cutting_entail_wit_4_2_split_goal_1 := by
  unfold legacy_rod_cutting_entail_wit_4_2_split_goal_1
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  simp only [Int.sub_zero] at PreH1 ⊢
  apply rod_cut_scan_best_step__scan_transitions _ i best _ PreH16 PreH22
  right
  exact ⟨by omega, rfl⟩

theorem legacy_proof_of_rod_cutting_entail_wit_5_split_goal_1 : legacy_rod_cutting_entail_wit_5_split_goal_1 := by
  unfold legacy_rod_cutting_entail_wit_5_split_goal_1
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro k hk
  by_cases hlt : k < j
  · have hn : Znth k (revenue_l_2 ++ [best]) 0 = Znth k revenue_l_2 0 :=
      ListLib.app_Znth1 0 revenue_l_2 [best] k ⟨hk.1, by change k < Zlength revenue_l_2; omega⟩
    rw [hn]
    exact PreH16 k ⟨hk.1, hlt⟩
  · have he : k = j := by omega
    subst k
    rw [app_Znth2 0 revenue_l_2 [best] j (by omega), PreH13, Int.sub_self]
    exact ⟨PreH11, PreH12⟩

theorem legacy_proof_of_rod_cutting_entail_wit_5_split_goal_2 : legacy_rod_cutting_entail_wit_5_split_goal_2 := by
  unfold legacy_rod_cutting_entail_wit_5_split_goal_2
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he : i = j + 1 := by omega
  subst i
  exact rod_cut_revenue_table_snoc__table_extension price_l revenue_l_2 j best
    PreH7 PreH13 (PreH6 j (by omega)).1 PreH14 PreH15

theorem legacy_proof_of_rod_cutting_entail_wit_5_split_goal_3 : legacy_rod_cutting_entail_wit_5_split_goal_3 := by
  unfold legacy_rod_cutting_entail_wit_5_split_goal_3
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  rw [Zlength_app, Zlength_cons, Zlength_nil, PreH13]
  omega

theorem legacy_proof_of_rod_cutting_entail_wit_5_split_goal_4 : legacy_rod_cutting_entail_wit_5_split_goal_4 := by
  unfold legacy_rod_cutting_entail_wit_5_split_goal_4
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH6

theorem legacy_proof_of_rod_cutting_entail_wit_1 : legacy_rod_cutting_entail_wit_1 := by
  unfold legacy_rod_cutting_entail_wit_1
  right
  intro n_pre revenue_pre price_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([0] : List Int) ?_
  split_pure_spatial
  · exact intArray.seg_single revenue_pre 0 (0 : Int)
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | rfl | omega
    · intro n hn
      have he : n = 0 := by omega
      subst n
      decide
    · intro k hk
      have he : k = 0 := by omega
      subst k
      exact rod_cut_optimal_revenue_zero__boundary_states price_l

theorem legacy_proof_of_rod_cutting_entail_wit_2 : legacy_rod_cutting_entail_wit_2 := by
  unfold legacy_rod_cutting_entail_wit_2
  right
  intro n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact legacy_proof_of_rod_cutting_entail_wit_2_split_goal_1 n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact legacy_proof_of_rod_cutting_entail_wit_2_split_goal_2 n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact legacy_proof_of_rod_cutting_entail_wit_2_split_goal_3 n_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem legacy_proof_of_rod_cutting_entail_wit_4_1 : legacy_rod_cutting_entail_wit_4_1 := by
  unfold legacy_rod_cutting_entail_wit_4_1
  right
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact legacy_proof_of_rod_cutting_entail_wit_4_1_split_goal_1 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem legacy_proof_of_rod_cutting_entail_wit_4_2 : legacy_rod_cutting_entail_wit_4_2 := by
  unfold legacy_rod_cutting_entail_wit_4_2
  right
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact legacy_proof_of_rod_cutting_entail_wit_4_2_split_goal_1 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem legacy_proof_of_rod_cutting_entail_wit_5 : legacy_rod_cutting_entail_wit_5 := by
  unfold legacy_rod_cutting_entail_wit_5
  right
  intro n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact legacy_proof_of_rod_cutting_entail_wit_5_split_goal_1 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact legacy_proof_of_rod_cutting_entail_wit_5_split_goal_2 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact legacy_proof_of_rod_cutting_entail_wit_5_split_goal_3 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      | exact legacy_proof_of_rod_cutting_entail_wit_5_split_goal_4 n_pre price_l revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem legacy_proof_of_rod_cutting_return_wit_1 : legacy_rod_cutting_return_wit_1 := by
  unfold legacy_rod_cutting_return_wit_1
  right
  intro n_pre revenue_pre price_l revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : j = n_pre + 1 := by omega
  rw [he] at PreH9 PreH10 PreH11 ⊢
  refine Automation.exp_right_rule (CRules := naive_C_Rules) revenue_l_2 ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using
      intArray.seg_to_full revenue_pre 0 (n_pre + 1) revenue_l_2
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | simpa only [Int.sub_zero]
private theorem forall_read (P : Int → Prop) (l : List Int) (i : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) := by
  have hin : i.toNat < l.length := by
    change 0 ≤ i ∧ i < Int.ofNat l.length at hi
    exact (Int.toNat_lt hi.1).mpr hi.2
  have hp := h.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using hp

theorem proof_of_rod_cutting_safety_wit_6 : rod_cutting_safety_wit_6 := by
  unfold rod_cutting_safety_wit_6
  left
  intro price_l price_pre n_pre revenue_l best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  prop_apply (intArray.full_Zlength price_pre (n_pre+1) price_l)
  Intros_p hprice_len
  have hplo := forall_read _ price_l i PreH3 (by omega)
  have hphi := forall_read _ price_l i PreH4 (by omega)
  have hrest := PreH13 (j-i) (by omega)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN, Int.sub_zero] <;> omega

theorem proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1 := by
  unfold rod_cutting_entail_wit_1
  right
  intro price_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([0] : List Int) ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero] using intArray.seg_single (&( "revenue" )) 0 (0 : Int)
  · split_pures <;> dump_pre_spatial
    all_goals try first | assumption | omega | rfl
    · intro k hk
      have he : k = 0 := by omega
      subst k
      decide
    · intro k hk
      have he : k = 0 := by omega
      subst k
      exact rod_cut_optimal_revenue_zero__boundary_states price_l

theorem proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2 := by
  unfold rod_cutting_entail_wit_2
  right
  intro price_l n_pre revenue_l_2 j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hs : RodCutScanBest price_l revenue_l_2 j 1 0 := Or.inr ⟨fun piece hp => False.elim (by omega), rfl⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact PreH8 | exact hs

theorem proof_of_rod_cutting_entail_wit_3_1 : rod_cutting_entail_wit_3_1 := by
  unfold rod_cutting_entail_wit_3_1
  left
  intro price_l price_pre n_pre revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  prop_apply (intArray.full_Zlength price_pre (n_pre+1) price_l)
  Intros_p hprice_len
  simp only [Int.sub_zero] at *
  have hprice := forall_read _ price_l i PreH5 (by omega)
  have hrest := PreH14 (j-i) (by omega)
  have hscan : RodCutScanBest price_l revenue_l_2 j (i+1) (Znth i price_l 0 + Znth ((j-i)-0) revenue_l_2 0) := by
    simp only [Int.sub_zero] at PreH1 ⊢
    apply rod_cut_scan_best_step__scan_transitions _ i best _ PreH8 PreH13
    exact Or.inl ⟨by omega, rfl⟩
  Exists revenue_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (simpa only [Int.sub_zero] using hscan) | omega

theorem proof_of_rod_cutting_entail_wit_3_2 : rod_cutting_entail_wit_3_2 := by
  unfold rod_cutting_entail_wit_3_2
  right
  intro price_l n_pre revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hscan : RodCutScanBest price_l revenue_l_2 j (i+1) best := by
    simp only [Int.sub_zero] at PreH1 ⊢
    apply rod_cut_scan_best_step__scan_transitions _ i best _ PreH8 PreH13
    exact Or.inr ⟨by omega, rfl⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact hscan

theorem proof_of_rod_cutting_entail_wit_4 : rod_cutting_entail_wit_4 := by
  unfold rod_cutting_entail_wit_4
  left
  intro price_l price_pre n_pre revenue_l_2 best i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  prop_apply (intArray.seg_Zlength (&( "revenue" )) 0 (j+1) (revenue_l_2 ++ [best]))
  Intros_p happ_len
  prop_apply (intArray.full_Zlength price_pre (n_pre+1) price_l)
  Intros_p hprice_len
  have hlen : Zlength revenue_l_2 = j := by
    simp only [Zlength_app, Zlength_cons, Zlength_nil] at happ_len
    omega
  have he : i = j+1 := by omega
  subst i
  have hprice := forall_read _ price_l j PreH3 (by omega)
  have htable := rod_cut_revenue_table_snoc__table_extension price_l revenue_l_2 j best PreH5 hlen hprice PreH11 PreH12
  have hbounds : ∀ k, (0 ≤ k ∧ k < j+1) → 0 ≤ Znth k (revenue_l_2 ++ [best]) 0 ∧ Znth k (revenue_l_2 ++ [best]) 0 ≤ k*1000000 := by
    intro k hk
    by_cases hlt : k < j
    · have hread : Znth k (revenue_l_2 ++ [best]) 0 = Znth k revenue_l_2 0 :=
        ListLib.app_Znth1 0 revenue_l_2 [best] k ⟨hk.1, by change k < Zlength revenue_l_2; omega⟩
      rw [hread]
      exact PreH13 k (by omega)
    · have he : k = j := by omega
      subst k
      rw [app_Znth2 0 revenue_l_2 [best] j (by omega), hlen, Int.sub_self]
      exact ⟨PreH9,PreH10⟩
  Exists (revenue_l_2 ++ [best])
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact htable | exact hbounds | omega

theorem proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5 := by
  unfold rod_cutting_entail_wit_5
  right
  intro price_l n_pre revenue_l j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hopt := PreH7 n_pre (by omega)
  split_pure_spatial
  · sep_apply_l_atomic (intArray.seg_to_undef_seg (&( "revenue" )) 0 j revenue_l)
    sep_apply_l_atomic (intArray.undef_seg_merge_to_undef_full (&( "revenue" )) 0 j 1001 (by omega))
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    simpa only [Int.sub_zero] using hopt


end SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_proof_manual
