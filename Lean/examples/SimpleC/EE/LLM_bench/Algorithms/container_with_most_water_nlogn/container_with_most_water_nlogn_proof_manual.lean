import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_goal
import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open container_with_most_water_nlogn_goal container_with_most_water_nlogn_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre)) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left_pre middle_pre right_pre left_pre middle_pre left_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  apply merge_prefix_init__merge_core <;> assumption


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre (i + 1) j (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1))) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hstate := PreH19
  have he : output = left_pre+(i-left_pre)+(j-middle_pre) := by omega
  rw [he] at hstate
  apply merge_prefix_take_left__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j (left_pre+(i-left_pre)+(j-middle_pre))
  all_goals first | assumption | omega | (right; omega) | (left; omega)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)))) = count_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)))) = count_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre i (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1))) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hstate := PreH19
  have he : output = left_pre+(i-left_pre)+(j-middle_pre) := by omega
  rw [he] at hstate
  apply merge_prefix_take_right__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j (left_pre+(i-left_pre)+(j-middle_pre))
  all_goals first | assumption | omega | (right; omega) | (left; omega)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre middle_pre (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1))) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hstate := PreH18
  have he : output = left_pre+(i-left_pre)+(j-middle_pre) := by omega
  rw [he] at hstate
  have hei : i = middle_pre := by omega
  rw [hei] at hstate ⊢
  apply merge_prefix_take_right__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre middle_pre j (left_pre+(middle_pre-left_pre)+(j-middle_pre))
  all_goals first | assumption | omega | (right; omega) | (left; omega)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [Zlength_replace_Znth]
  first | assumption | rfl | omega | ((repeat' constructor) <;> nlinarith)


theorem container_aux_mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre)) := by
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hi : i = middle_pre := by omega
  have hj : j = right_pre := by omega
  have hout : output = right_pre := by omega
  have hs := PreH18
  rw [hi,hj,hout] at hs
  apply merge_prefix_finish__merge_core <;> first | assumption | omega


theorem container_aux_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega


theorem container_aux_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((INT_MIN) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega


theorem container_aux_sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (HeightIndexRangeSortResultNLogN work0_h work0_i work0_h work0_i left_pre right_pre)) := by
  intro right_pre left_pre count_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine ⟨by omega,by omega,by omega,by omega,by omega,⟨rfl,rfl,fun _ _ _ => ⟨rfl,rfl⟩⟩,List.Perm.refl _,by omega,by omega,by omega,?_⟩
  intro p q hp hpq hq
  have he : p=q := by omega
  rw [he]


theorem container_aux_sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (work0_i : (List Int)) (work0_h : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k)) ,
  (HeightIndexRangeSortResultNLogN work0_h work0_i work_h1 work_i1 left_pre right_pre)) := by
  intro right_pre left_pre count_pre work0_i work0_h buffer0_h buffer0_i k buffer_i_2 buffer_h_2 work_i1 work_h1 work_i_2 work_h_2 work_mid_i work_mid_h middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hks : k = right_pre := by omega
  have hc := PreH20
  rw [hks] at hc
  have hs := PreH17
  dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at hs
  apply sort_range_after_merge_copy__sort_copy work0_h work0_i work_mid_h work_mid_i work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 work_h1 work_i1 left_pre middle right_pre
  all_goals first | assumption | omega


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : ((right_pre - left_pre) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : ((right_pre - left_pre) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_h)) = count_pre) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength workHeight_pre count_pre work_h)
  Intros_p hlen
  dump_pre_spatial
  exact hlen


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_i)) = count_pre) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength workIndex_pre count_pre work_i)
  Intros_p hlen
  dump_pre_spatial
  exact hlen


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (buffer_h)) = count_pre) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength bufferHeight_pre count_pre buffer_h)
  Intros_p hlen
  dump_pre_spatial
  exact hlen


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (buffer_i)) = count_pre) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength bufferIndex_pre count_pre buffer_i)
  Intros_p hlen
  dump_pre_spatial
  exact hlen


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 : (forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ”) := by
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  try dsimp only [HeightIndexRangeSortResultNLogN,SameHeightIndexOutsideNLogN] at *
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  try rw [hq]
  dump_pre_spatial
  try simp only [INT_MAX,INT_MIN]
  omega


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_1 : ((
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (destinationIndex_pre : Int) (destinationHeight_pre : Int) (sourceIndex_pre : Int) (sourceHeight_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre)) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest0_h)
  ** (intArray.full destinationIndex_pre count_pre dest0_i)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= left_pre) ” &&
  “ (left_pre <= middle_pre) ” &&
  “ (middle_pre <= middle_pre) ” &&
  “ (middle_pre <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (left_pre = ((left_pre + (left_pre - left_pre)) + (middle_pre - middle_pre))) ” &&
  “ (left_pre <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre left_pre middle_pre left_pre) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre)) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre)) ,
  TT && emp
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left_pre middle_pre right_pre left_pre middle_pre left_pre) ”
  &&  emp
)) := by
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1 : ((
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (destinationIndex_pre : Int) (destinationHeight_pre : Int) (sourceIndex_pre : Int) (sourceHeight_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (i + 1)) ” &&
  “ ((i + 1) <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + ((i + 1) - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1) j (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre (i + 1) j (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1)) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)))) = count_pre) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)))) = count_pre) ”
  &&  emp
)) := by
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2 : ((
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (destinationIndex_pre : Int) (destinationHeight_pre : Int) (sourceIndex_pre : Int) (sourceHeight_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= (j + 1)) ” &&
  “ ((j + 1) <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + (i - left_pre)) + ((j + 1) - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i (j + 1) (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre i (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1)) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre) ”
  &&  emp
)) := by
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_4 : (forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (destinationIndex_pre : Int) (destinationHeight_pre : Int) (sourceIndex_pre : Int) (sourceHeight_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (i : Int) (j : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  (EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((i + 1) = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (i + 1)) ” &&
  “ ((i + 1) <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + ((i + 1) - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1) j (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i))
  ||
  (EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (i + 1)) ” &&
  “ ((i + 1) <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + ((i + 1) - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1) j (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i))) := by
  intro right_pre middle_pre left_pre count_pre destinationIndex_pre destinationHeight_pre sourceIndex_pre sourceHeight_pre dest0_i dest0_h source_i source_h output i j dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hnext : MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth output (Znth i source_h 0) dest_h_2) (replace_Znth output (Znth i source_i 0) dest_i_2) left_pre middle_pre right_pre (i+1) j (output+1) := by
    apply merge_prefix_take_left__merge_core source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output
    all_goals first | assumption | omega | (left; exact PreH8)
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth output (Znth i source_i 0) dest_i_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth output (Znth i source_h 0) dest_h_2) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | rfl | omega | nlinarith


theorem container_aux_mergeHeightIndexRunsNLogN_entail_wit_6 : ((
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (destinationIndex_pre : Int) (destinationHeight_pre : Int) (sourceIndex_pre : Int) (sourceHeight_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= (j + 1)) ” &&
  “ ((j + 1) <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + (i - left_pre)) + ((j + 1) - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i (j + 1) (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre middle_pre (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1)) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre) ”
  &&  emp
)) := by
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
      | exact (container_aux_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)


theorem container_aux_mergeHeightIndexRunsNLogN_return_wit_1 : ((
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (destinationIndex_pre : Int) (destinationHeight_pre : Int) (sourceIndex_pre : Int) (sourceHeight_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h_2)
  ** (intArray.full destinationIndex_pre count_pre dest_i_2)
|--
  EX dest_h : (List Int), EX dest_i : (List Int),
  “ (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (right_pre : Int) (middle_pre : Int) (left_pre : Int) (count_pre : Int) (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp
|--
  “ (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre) ”
  &&  emp
)) := by
  right
  intro right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 right_pre middle_pre left_pre count_pre dest0_i dest0_h source_i source_h output j i dest_i_2 dest_h_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)


theorem container_aux_sortHeightIndexRangeNLogN_safety_wit_3 : ((
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”
)) := by
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact (container_aux_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | exact (container_aux_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)


theorem container_aux_sortHeightIndexRangeNLogN_return_wit_1 : ((
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_h : (List Int), EX work_i : (List Int),
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre right_pre) ”
  &&  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
) \/
(
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  TT && emp
|--
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work0_h work0_i left_pre right_pre) ”
  &&  emp
)) := by
  right
  intro right_pre left_pre count_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 right_pre left_pre count_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)


theorem container_aux_sortHeightIndexRangeNLogN_return_wit_2 : ((
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (work0_i : (List Int)) (work0_h : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferHeight_pre count_pre buffer_h_2)
  ** (intArray.full bufferIndex_pre count_pre buffer_i_2)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_h : (List Int), EX work_i : (List Int),
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre right_pre) ”
  &&  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
) \/
(
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (work0_i : (List Int)) (work0_h : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k)) ,
  TT && emp
|--
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h1 work_i1 left_pre right_pre) ”
  &&  emp
)) := by
  right
  intro right_pre left_pre count_pre work0_i work0_h buffer0_h buffer0_i k buffer_i_2 buffer_h_2 work_i1 work_h1 work_i_2 work_h_2 work_mid_i work_mid_h middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (container_aux_sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 right_pre left_pre count_pre work0_i work0_h buffer0_h buffer0_i k buffer_i_2 buffer_h_2 work_i1 work_h1 work_i_2 work_h_2 work_mid_i work_mid_h middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : ((
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((Zlength (work0_h)) = count_pre) ” &&
  “ ((Zlength (work0_i)) = count_pre) ” &&
  “ ((Zlength (buffer0_h)) = count_pre) ” &&
  “ ((Zlength (buffer0_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ” &&
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : ((right_pre - left_pre) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ”
)) := by
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures
  all_goals first
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)


theorem container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : ((
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH2 : ((right_pre - left_pre) > 1)) (PreH3 : ((Zlength (work0_h)) = count_pre)) (PreH4 : ((Zlength (work0_i)) = count_pre)) (PreH5 : ((Zlength (buffer0_h)) = count_pre)) (PreH6 : ((Zlength (buffer0_i)) = count_pre)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre <= count_pre)) (PreH10 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (right_pre <= count_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ” &&
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ”
) \/
(
forall (right_pre : Int) (left_pre : Int) (count_pre : Int) (bufferIndex_pre : Int) (bufferHeight_pre : Int) (workIndex_pre : Int) (workHeight_pre : Int) (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ”
)) := by
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  all_goals first
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | exact (container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)


theorem proof_of_maxAreaNLogN_entail_wit_9_1 : maxAreaNLogN_entail_wit_9_1 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have hs := PreH48
  have he := PreH49
  have ho := PreH50
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH25 PreH26 PreH27 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH25] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMaximum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMaximum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex index := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_2 : maxAreaNLogN_entail_wit_9_2 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have hs := PreH48
  have he := PreH49
  have ho := PreH50
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH25 PreH26 PreH27 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH25] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMinimum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMinimum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex index := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_3 : maxAreaNLogN_entail_wit_9_3 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hs := PreH50
  have he := PreH51
  have ho := PreH52
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH27 PreH28 PreH29 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH27] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex index := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_4 : maxAreaNLogN_entail_wit_9_4 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hs := PreH50
  have he := PreH51
  have ho := PreH52
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH27 PreH28 PreH29 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH27] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex index := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_5 : maxAreaNLogN_entail_wit_9_5 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have hs := PreH48
  have he := PreH49
  have ho := PreH50
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH25 PreH26 PreH27 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH25] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMaximum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMaximum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) index maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_6 : maxAreaNLogN_entail_wit_9_6 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have hs := PreH48
  have he := PreH49
  have ho := PreH50
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH25 PreH26 PreH27 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH25] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMinimum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMinimum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) index maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_7 : maxAreaNLogN_entail_wit_9_7 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hs := PreH50
  have he := PreH51
  have ho := PreH52
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH27 PreH28 PreH29 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH27] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) index maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_8 : maxAreaNLogN_entail_wit_9_8 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hs := PreH50
  have he := PreH51
  have ho := PreH52
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH27 PreH28 PreH29 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH27] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) index maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_9 : maxAreaNLogN_entail_wit_9_9 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMaximum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMaximum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_10 : maxAreaNLogN_entail_wit_9_10 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMinimum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMinimum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_11 : maxAreaNLogN_entail_wit_9_11 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMaximum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMaximum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_12 : maxAreaNLogN_entail_wit_9_12 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMinimum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMinimum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_13 : maxAreaNLogN_entail_wit_9_13 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMaximum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMaximum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_14 : maxAreaNLogN_entail_wit_9_14 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMinimum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMinimum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_15 : maxAreaNLogN_entail_wit_9_15 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMaximum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMaximum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_16 : maxAreaNLogN_entail_wit_9_16 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) (distanceToMinimum * currentHeight) := by
    have hgt : maximumArea ≤ width*currentHeight := by omega
    rw [max_eq_right hgt] at hm
    have hw : (distanceToMinimum * currentHeight) = width*currentHeight := by congr 1 <;> omega
    rw [hw]; exact hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_17 : maxAreaNLogN_entail_wit_9_17 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_18 : maxAreaNLogN_entail_wit_9_18 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_19 : maxAreaNLogN_entail_wit_9_19 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_20 : maxAreaNLogN_entail_wit_9_20 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_21 : maxAreaNLogN_entail_wit_9_21 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_22 : maxAreaNLogN_entail_wit_9_22 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_23 : maxAreaNLogN_entail_wit_9_23 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_9_24 : maxAreaNLogN_entail_wit_9_24 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hs := PreH32
  have he := PreH33
  have ho := PreH34
  have hwidth : width = |minimumIndex-index| ∨ width = |maximumIndex-index| := by
    first
    | left; rw [abs_of_nonneg (by omega : 0 ≤ minimumIndex-index)]; omega
    | left; rw [abs_of_nonpos (by omega : minimumIndex-index ≤ 0)]; omega
    | right; rw [abs_of_nonneg (by omega : 0 ≤ maximumIndex-index)]; omega
    | right; rw [abs_of_nonpos (by omega : maximumIndex-index ≤ 0)]; omega
  have hbound : ∀ x, minimumIndex ≤ x ∧ x ≤ maximumIndex → |x-index| ≤ width := by
    intro x hx
    apply abs_le.mpr
    constructor <;> omega
  have hm := processed_max_extend__max_endpoint_b l sorted_h_2 sorted_i_2 k index currentHeight minimumIndex maximumIndex maximumArea width (by omega) (by omega) hs he ho PreH9 PreH10 PreH11 (by omega) (by omega) hbound hwidth
  have hend := processed_endpoints_extend__max_endpoint_b sorted_i_2 k minimumIndex maximumIndex (by omega) he
  rw [← PreH9] at hend
  have hp : ProcessedContainerMaximumNLogN l sorted_i_2 (k+1) maximumArea := by
    simpa only [max_eq_left (by omega : width*currentHeight ≤ maximumArea)] using hm
  have hep : ProcessedIndexEndpointsNLogN sorted_i_2 (k+1) minimumIndex maximumIndex := by
    convert hend using 1 <;> (first | rfl | (simp only [min_def,max_def]; split <;> omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_mergeHeightIndexRunsNLogN_return_wit_1 : mergeHeightIndexRunsNLogN_return_wit_1 := container_aux_mergeHeightIndexRunsNLogN_return_wit_1

theorem proof_of_sortHeightIndexRangeNLogN_safety_wit_3 : sortHeightIndexRangeNLogN_safety_wit_3 := container_aux_sortHeightIndexRangeNLogN_safety_wit_3

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure := container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure

theorem proof_of_sortHeightIndexRangeNLogN_return_wit_1 : sortHeightIndexRangeNLogN_return_wit_1 := container_aux_sortHeightIndexRangeNLogN_return_wit_1

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_6 : mergeHeightIndexRunsNLogN_entail_wit_6 := container_aux_mergeHeightIndexRunsNLogN_entail_wit_6

theorem proof_of_sortHeightIndexRangeNLogN_return_wit_2 : sortHeightIndexRangeNLogN_return_wit_2 := container_aux_sortHeightIndexRangeNLogN_return_wit_2

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1 := container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_1

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2 := container_aux_mergeHeightIndexRunsNLogN_entail_wit_2_2

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure := container_aux_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_4 : mergeHeightIndexRunsNLogN_entail_wit_4 := container_aux_mergeHeightIndexRunsNLogN_entail_wit_4

theorem proof_of_mergeHeightIndexRunsNLogN_entail_wit_1 : mergeHeightIndexRunsNLogN_entail_wit_1 := container_aux_mergeHeightIndexRunsNLogN_entail_wit_1

theorem proof_of_sortHeightIndexRangeNLogN_entail_wit_2 : sortHeightIndexRangeNLogN_entail_wit_2 := by
  right
  intro right_pre left_pre count_pre work0_i work0_h buffer0_h_2 buffer0_i_2 k buffer_i_2 buffer_h_2 work_i1_2 work_h1_2 work_i_2 work_h_2 work_mid_i_2 work_mid_h_2 middle PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hkh : 0 ≤ k ∧ k < Zlength work_h1_2 := ⟨by omega,by omega⟩
  have hki : 0 ≤ k ∧ k < Zlength work_i1_2 := ⟨by omega,by omega⟩
  have hc : CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 (replace_Znth k (Znth k buffer_h_2 0) work_h1_2) (replace_Znth k (Znth k buffer_i_2 0) work_i1_2) left_pre right_pre (k+1) := by
    constructor
    · intro p hp
      by_cases he : p=k
      · rw [he,Znth_replace_Znth_Same 0 work_h1_2 k _ hkh,Znth_replace_Znth_Same 0 work_i1_2 k _ hki]
        exact ⟨rfl,rfl⟩
      · rw [Znth_replace_Znth_Diff 0 work_h1_2 k p _ hkh ⟨by omega,by omega⟩ (Ne.symm he),Znth_replace_Znth_Diff 0 work_i1_2 k p _ hki ⟨by omega,by omega⟩ (Ne.symm he)]
        exact PreH20.1 p ⟨hp.1,by omega⟩
    · intro p hp hout
      have hne : k ≠ p := by rcases hout with h | h <;> omega
      rw [Znth_replace_Znth_Diff 0 work_h1_2 k p _ hkh ⟨hp.1,by omega⟩ hne,Znth_replace_Znth_Diff 0 work_i1_2 k p _ hki ⟨hp.1,by omega⟩ hne]
      apply PreH20.2 p hp
      rcases hout with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer0_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer0_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_mid_h_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try rw [Zlength_replace_Znth]
    all_goals first | assumption | omega

theorem proof_of_sortHeightIndexRangeNLogN_entail_wit_1 : sortHeightIndexRangeNLogN_entail_wit_1 := by
  left
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i_2 buffer0_h_2 work0_i work0_h work_h_2 work_i_2 buffer_i_2 buffer_h_2 work_h_3 work_i_3 dest_h dest_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  prop_apply (intArray.full_Zlength bufferHeight_pre count_pre dest_h)
  Intros_p len_dest_h
  change Zlength dest_h = count_pre at len_dest_h
  prop_apply (intArray.full_Zlength bufferIndex_pre count_pre dest_i)
  Intros_p len_dest_i
  change Zlength dest_i = count_pre at len_dest_i
  have hs1 := PreH2
  have hs2 := PreH3
  dsimp only [HeightIndexRangeSortResultNLogN, SameHeightIndexOutsideNLogN] at hs1 hs2
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hc : CopyHeightIndexPrefixNLogN dest_h dest_i work_h_3 work_i_3 work_h_3 work_i_3 left_pre right_pre left_pre := by
    constructor
    · intro p hp; omega
    · intro p hp hout; exact ⟨rfl,rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dest_i ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dest_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_3 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_3 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_3 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_3 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (rw [hq]; omega)

theorem proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure := by
  right
  intro right_pre left_pre count_pre bufferIndex_pre bufferHeight_pre workIndex_pre workHeight_pre buffer0_i buffer0_h work0_i work0_h work_h_2 work_i_2 buffer_i buffer_h work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  prop_apply (intArray.full_Zlength workHeight_pre count_pre work_h)
  Intros_p len_work_h
  change Zlength work_h = count_pre at len_work_h
  prop_apply (intArray.full_Zlength workIndex_pre count_pre work_i)
  Intros_p len_work_i
  change Zlength work_i = count_pre at len_work_i
  prop_apply (intArray.full_Zlength bufferHeight_pre count_pre buffer_h)
  Intros_p len_buffer_h
  change Zlength buffer_h = count_pre at len_buffer_h
  prop_apply (intArray.full_Zlength bufferIndex_pre count_pre buffer_i)
  Intros_p len_buffer_i
  change Zlength buffer_i = count_pre at len_buffer_i
  have hq : Z.quot (right_pre-left_pre) 2 = (right_pre-left_pre)/2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hd := range_sort_left_desc__sort_recursion work0_h work0_i work_h_2 work_i_2 work_h work_i left_pre (left_pre+Z.quot (right_pre-left_pre) 2) right_pre PreH10 PreH9
  have hr := PreH9.2.2.2.2.2.2.2
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega | (rw [hq]; omega)

private theorem nth_property (l : List Int) (P : Int → Prop) (h : Forall P l) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) := by
  have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
  apply h.mem
  change l.getD i.toNat 0 ∈ l
  rw [List.getD_eq_getElem l 0 hn]
  exact List.getElem_mem hn

theorem proof_of_maxAreaNLogN_safety_wit_12 : maxAreaNLogN_safety_wit_12 := by
  right
  intro heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH12 ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX,INT_MIN]; omega

theorem proof_of_maxAreaNLogN_safety_wit_13 : maxAreaNLogN_safety_wit_13 := by
  right
  intro heightSize_pre height_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH12 ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX,INT_MIN]; omega

theorem proof_of_maxAreaNLogN_entail_wit_6_1 : maxAreaNLogN_entail_wit_6_1 := by
  right
  intro heightSize_pre l sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hn := nth_property l (fun x => 0 ≤ x) PreH18 (Znth k sorted_i 0) hl.1
  have hu := nth_property l (fun x => x ≤ 10000) PreH19 (Znth k sorted_i 0) hl.1
  have hnn : 0 ≤ Znth k sorted_h 0 := by rw [hl.2]; exact hn
  have huu : Znth k sorted_h 0 ≤ 10000 := by rw [hl.2]; exact hu
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hl.2 | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_2 : maxAreaNLogN_entail_wit_6_2 := by
  unfold maxAreaNLogN_entail_wit_6_2
  intro heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hn := nth_property l (fun x => 0 ≤ x) PreH18 (Znth k sorted_i 0) hl.1
  have hu := nth_property l (fun x => x ≤ 10000) PreH19 (Znth k sorted_i 0) hl.1
  have hnn : 0 ≤ Znth k sorted_h 0 := by rw [hl.2]; exact hn
  have huu : Znth k sorted_h 0 ≤ 10000 := by rw [hl.2]; exact hu
  first
  | solve
    | Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_3 : maxAreaNLogN_entail_wit_6_3 := by
  unfold maxAreaNLogN_entail_wit_6_3
  intro heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hn := nth_property l (fun x => 0 ≤ x) PreH18 (Znth k sorted_i 0) hl.1
  have hu := nth_property l (fun x => x ≤ 10000) PreH19 (Znth k sorted_i 0) hl.1
  have hnn : 0 ≤ Znth k sorted_h 0 := by rw [hl.2]; exact hn
  have huu : Znth k sorted_h 0 ≤ 10000 := by rw [hl.2]; exact hu
  first
  | solve
    | Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_4 : maxAreaNLogN_entail_wit_6_4 := by
  unfold maxAreaNLogN_entail_wit_6_4
  intro heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hn := nth_property l (fun x => 0 ≤ x) PreH18 (Znth k sorted_i 0) hl.1
  have hu := nth_property l (fun x => x ≤ 10000) PreH19 (Znth k sorted_i 0) hl.1
  have hnn : 0 ≤ Znth k sorted_h 0 := by rw [hl.2]; exact hn
  have huu : Znth k sorted_h 0 ≤ 10000 := by rw [hl.2]; exact hu
  first
  | solve
    | Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega

theorem proof_of_maxAreaNLogN_entail_wit_6_5 : maxAreaNLogN_entail_wit_6_5 := by
  unfold maxAreaNLogN_entail_wit_6_5
  intro heightSize_pre height_pre l buffer_i_2 buffer_h_2 sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl := sorted_workspace_lookup__max_loop_setup l sorted_h sorted_i k PreH15 ⟨by omega,by omega⟩
  have hn := nth_property l (fun x => 0 ≤ x) PreH18 (Znth k sorted_i 0) hl.1
  have hu := nth_property l (fun x => x ≤ 10000) PreH19 (Znth k sorted_i 0) hl.1
  have hnn : 0 ≤ Znth k sorted_h 0 := by rw [hl.2]; exact hn
  have huu : Znth k sorted_h 0 ≤ 10000 := by rw [hl.2]; exact hu
  first
  | solve
    | Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Right
      Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Right
      Right
      Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Right
      Right
      Right
      Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Right
      Right
      Right
      Right
      Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Right
      Right
      Right
      Right
      Right
      Left
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega
  | solve
    | Right
      Right
      Right
      Right
      Right
      Right
      Right
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_h ?_
      refine Automation.exp_right_rule (CRules := naive_C_Rules) sorted_i ?_
      split_pure_spatial
      · cancel
      · split_pures <;> dump_pre_spatial
        all_goals first | assumption | exact hl.2 | rfl | omega

theorem proof_of_maxAreaNLogN_entail_wit_7_1 : maxAreaNLogN_entail_wit_7_1 := by
  unfold maxAreaNLogN_entail_wit_7_1
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35
  have hprod0 : 0 ≤ width*currentHeight := mul_nonneg (by omega) (by omega)
  have hprod1 : width*currentHeight ≤ 999990000 := by nlinarith

  have hd : distanceToMaximum = width := by omega
  rw [hd]
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_2 : maxAreaNLogN_entail_wit_7_2 := by
  unfold maxAreaNLogN_entail_wit_7_2
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35
  have hprod0 : 0 ≤ width_2*currentHeight_2 := mul_nonneg (by omega) (by omega)
  have hprod1 : width_2*currentHeight_2 ≤ 999990000 := by nlinarith

  have hd : width_2 = distanceToMaximum_2 := by omega
  rw [hd]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_3 : maxAreaNLogN_entail_wit_7_3 := by
  unfold maxAreaNLogN_entail_wit_7_3
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35
  have hprod0 : 0 ≤ width*currentHeight := mul_nonneg (by omega) (by omega)
  have hprod1 : width*currentHeight ≤ 999990000 := by nlinarith

  have hd : distanceToMaximum = width := by omega
  rw [hd]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_7_4 : maxAreaNLogN_entail_wit_7_4 := by
  unfold maxAreaNLogN_entail_wit_7_4
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35
  have hprod0 : 0 ≤ width_2*currentHeight_2 := mul_nonneg (by omega) (by omega)
  have hprod1 : width_2*currentHeight_2 ≤ 999990000 := by nlinarith

  have hd : width_2 = distanceToMaximum_2 := by omega
  rw [hd]
  Right
  Right
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_1 : maxAreaNLogN_entail_wit_8_1 := by
  unfold maxAreaNLogN_entail_wit_8_1
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36
  have hprod0 : 0 ≤ width*currentHeight := mul_nonneg (by omega) (by omega)
  have hprod1 : width*currentHeight ≤ 999990000 := by nlinarith

  have hd : width = distanceToMinimum := by omega
  rw [hd]
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_2 : maxAreaNLogN_entail_wit_8_2 := by
  unfold maxAreaNLogN_entail_wit_8_2
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36
  have hprod0 : 0 ≤ width_2*currentHeight_2 := mul_nonneg (by omega) (by omega)
  have hprod1 : width_2*currentHeight_2 ≤ 999990000 := by nlinarith

  have hw : width_2 = distanceToMinimum_2 := by omega
  rw [hw]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_3 : maxAreaNLogN_entail_wit_8_3 := by
  unfold maxAreaNLogN_entail_wit_8_3
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k index currentHeight minimumIndex maximumIndex distanceToMinimum distanceToMaximum width maximumArea NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36
  have hprod0 : 0 ≤ width*currentHeight := mul_nonneg (by omega) (by omega)
  have hprod1 : width*currentHeight ≤ 999990000 := by nlinarith

  have hd : width = distanceToMinimum := by omega
  rw [hd]
  Right
  Left
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

theorem proof_of_maxAreaNLogN_entail_wit_8_4 : maxAreaNLogN_entail_wit_8_4 := by
  unfold maxAreaNLogN_entail_wit_8_4
  intro heightSize_pre height_pre l sorted_h sorted_i buffer_h buffer_i k_2 index_2 currentHeight_2 minimumIndex_2 maximumIndex_2 distanceToMinimum_2 distanceToMaximum_2 width_2 maximumArea_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36
  have hprod0 : 0 ≤ width_2*currentHeight_2 := mul_nonneg (by omega) (by omega)
  have hprod1 : width_2*currentHeight_2 ≤ 999990000 := by nlinarith

  have hw : width_2 = distanceToMinimum_2 := by omega
  rw [hw]
  Right
  Right
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN]
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | rfl | omega | nlinarith

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg

private theorem scratch_cleanup (a len total : Int) (l : List Int) (hc : 0 ≤ len ∧ len ≤ total) :
    intArray.full a len l ** intArray.undef_seg a len total |-- intArray.undef_full a total := by
  refine naive_C_Rules.toContext.derivable1_trans _ (intArray.undef_seg a 0 len ** intArray.undef_seg a len total) _ ?_ ?_
  · apply naive_C_Rules.toContext.derivable1_sepcon_mono
    · exact naive_C_Rules.toContext.derivable1_trans _ _ _ (intArray.full_to_seg a len l) (intArray.seg_to_undef_seg a 0 len l)
    · exact naive_C_Rules.toContext.derivable1_refl _
  · simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.undef_seg_merge_to_undef_full a 0 len total hc

theorem proof_of_maxAreaNLogN_entail_wit_1 : maxAreaNLogN_entail_wit_1 := by
  right
  intro heightSize_pre l PreH1 PreH2 PreH3 PreH4 PreH5
  have hp : WorkspacePrefixNLogN l [] [] 0 := by constructor <;> intro p hp <;> omega
  split_pure_spatial
  · sep_apply (intArray.undef_full_split_to_undef_seg (&("workHeight")) heightSize_pre 100000 (by omega))
    sep_apply (intArray.undef_full_split_to_undef_seg (&("workIndex")) heightSize_pre 100000 (by omega))
    sep_apply (intArray.undef_full_split_to_undef_seg (&("bufferHeight")) heightSize_pre 100000 (by omega))
    sep_apply (intArray.undef_full_split_to_undef_seg (&("bufferIndex")) heightSize_pre 100000 (by omega))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hp | rfl

theorem proof_of_maxAreaNLogN_entail_wit_2 : maxAreaNLogN_entail_wit_2 := by
  right
  intro heightSize_pre l buffer_i_2 buffer_h_2 work_i_2 work_h_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hw := workspace_prefix_snoc__max_init l work_h_2 work_i_2 k PreH7 PreH8 PreH11 (by omega)
  have hb := workspace_prefix_snoc__max_init l buffer_h_2 buffer_i_2 k PreH9 PreH10 PreH12 (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hw.2.2 | exact hb.2.2 | assumption | (simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega)

theorem proof_of_maxAreaNLogN_entail_wit_3 : maxAreaNLogN_entail_wit_3 := by
  right
  intro heightSize_pre l buffer_i buffer_h work_i work_h k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hk : k=heightSize_pre := by omega
  rw [hk] at PreH11 PreH12 ⊢
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h ?_
  split_pure_spatial
  · simp only [Int.zero_mul,Int.add_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_4 : maxAreaNLogN_entail_wit_4 := by
  right
  intro heightSize_pre l work0_h work0_i buffer0_h buffer0_i buffer_i_2 buffer_h_2 work_h work_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hs := full_sort_workspace__max_loop_setup l work0_h work0_i work_h work_i heightSize_pre PreH4 PreH5 PreH6 PreH9 PreH1
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) buffer_h_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_h ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) work_i ?_
  split_pure_spatial
  · simp only [Int.zero_mul,Int.add_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_maxAreaNLogN_entail_wit_5 : maxAreaNLogN_entail_wit_5 := by
  right
  intro heightSize_pre l sorted_h_2 sorted_i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hb := sorted_index_bounds__max_init l sorted_h_2 sorted_i 0 PreH4 ⟨by omega,by omega⟩
  have hl := PreH4.1.2.1
  have hm := processed_maximum_initial__max_loop_setup l sorted_i (by omega)
  have he : ProcessedIndexEndpointsNLogN sorted_i 1 (Znth 0 sorted_i 0) (Znth 0 sorted_i 0) := by
    refine ⟨⟨0,⟨by omega,by omega⟩,rfl⟩,⟨0,⟨by omega,by omega⟩,rfl⟩,?_⟩
    intro p hp
    have hp0 : p=0 := by omega
    subst p; exact ⟨le_refl _,le_refl _⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maxAreaNLogN_entail_wit_10 : maxAreaNLogN_entail_wit_10 := by
  right
  intro heightSize_pre l buffer_i buffer_h sorted_h sorted_i maximumArea maximumIndex minimumIndex k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hk : k=Zlength l := by omega
  rw [hk] at PreH14
  have hm := processed_full_prefix_maximum__max_final_result l sorted_h sorted_i maximumArea (by omega) PreH12.1 PreH14 (fun i hi => nth_property l (fun x => 0 ≤ x) PreH15 i hi)
  split_pure_spatial
  · sep_apply (scratch_cleanup (&("workHeight")) heightSize_pre 100000 sorted_h (by omega))
    sep_apply (scratch_cleanup (&("workIndex")) heightSize_pre 100000 sorted_i (by omega))
    sep_apply (scratch_cleanup (&("bufferHeight")) heightSize_pre 100000 buffer_h (by omega))
    sep_apply (scratch_cleanup (&("bufferIndex")) heightSize_pre 100000 buffer_i (by omega))
    cancel
  · split_pures; dump_pre_spatial; exact hm

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_proof_manual
