import SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance uint_arrayStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem uint_array_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy1
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.full_split_to_missing_i p i n l 0 (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy6
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy7
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_split_to_missing_i p x i y l 0 (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy8
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_merge_to_seg p x y z l1 l2 (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy9
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  rename_i l1 l2 hlen
  prop_apply (naive_C_Rules.UIntArray.seg_Zlength p x z (l1 ++ l2))
  pureIntros
  sep_apply (naive_C_Rules.UIntArray.seg_split_to_seg p x y z (l1 ++ l2) (by omega))
  have hleft : sublist 0 (y-x) (l1 ++ l2) = l1 := by rw [← hlen, sublist_app_exact1]
  have hright : sublist (y-x) (z-x) (l1 ++ l2) = l2 := by
    rw [sublist_split_app_r (y-x) (z-x) (y-x) l1 l2 hlen (by omega)]
    simp only [Int.sub_self]
    apply sublist_self
    simp only [Zlength_app] at *
    omega
  rw [hleft, hright]
  exact fun _ h => h

theorem uint_array_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy10
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  exact fun h hs => (naive_C_Rules.UIntArray.seg_empty _ _ _).2 h ⟨rfl, hs⟩

theorem uint_array_strategy13_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy13 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy13
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)
  exact fun h hs => (naive_C_Rules.UIntArray.full_empty _ 0).2 h ⟨rfl, hs⟩

theorem uint_array_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy14
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  rename_i v p n
  sep_apply (naive_C_Rules.UIntArray.seg_single p n v)
  sep_apply (naive_C_Rules.UIntArray.seg_to_full p n (n+1) [v])
  prop_apply (naive_C_Rules.UIntArray.full_Zlength p n x)
  pureIntros
  have := Zlength_nonneg x
  sep_apply (naive_C_Rules.UIntArray.full_merge_to_full p n (n+1) x [v] (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem uint_array_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy2
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_full p i n (Znth i l 0) l (by omega))
  simp only [replace_Znth_Znth]
  exact fun _ h => h

theorem uint_array_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy11
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_seg p x i y (Znth (i-x) l 0) l (by omega))
  simp only [replace_Znth_Znth]
  exact fun _ h => h

theorem uint_array_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_full p i n v l (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem uint_array_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy12
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_seg p x i y v l (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

end SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_proof
