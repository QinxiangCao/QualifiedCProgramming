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

theorem uint_array_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

theorem uint_array_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

theorem uint_array_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy6
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

theorem uint_array_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy7
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_split_to_missing_i p x i y l 0 (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

theorem uint_array_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy8
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_merge_to_seg p x y z l1 l2 (by omega))
  exact fun _ h => h

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
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  exact fun h hs => (naive_C_Rules.UIntArray.full_empty _ 0).2 h ⟨rfl, hs⟩

theorem uint_array_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy14
  pre_process_default
  pureIntros
  subst_vars
  prop_apply (naive_C_Rules.UIntArray.full_Zlength p n l)
  pureIntros
  have := Zlength_nonneg l
  sep_apply (naive_C_Rules.UIntArray.full_to_seg p n l)
  sep_apply (naive_C_Rules.UIntArray.seg_single p n v)
  sep_apply (naive_C_Rules.UIntArray.seg_merge_to_full p 0 n (n + 1) l [v] (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  exact fun _ h => h

theorem uint_array_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy15
  pre_process_default
  pureIntros
  subst_vars
  prop_apply (naive_C_Rules.UIntArray.seg_valid p x y l)
  pureIntros
  sep_apply (naive_C_Rules.UIntArray.seg_single p y v)
  sep_apply (naive_C_Rules.UIntArray.seg_merge_to_seg p x y (y + 1) l [v] (by omega))
  exact fun _ h => h

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

theorem uint_array_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy16
  pre_process_default
  pureIntros
  subst_vars
  prop_apply (naive_C_Rules.UIntArray.full_Zlength (p + i * sizeof(UINT)) n l)
  pureIntros
  have := Zlength_nonneg l
  sep_apply (naive_C_Rules.UIntArray.seg_single p (i - 1) v)
  sep_apply (naive_C_Rules.UIntArray.seg_to_full p (i - 1) (i - 1 + 1) [v])
  simp only [show i - 1 + 1 - (i - 1) = 1 by omega]
  have hmerge := naive_C_Rules.UIntArray.full_merge_to_full
    (p + (i - 1) * sizeof(UINT)) 1 (n + 1) [v] l (by omega)
  have haddr : (p + (i - 1) * sizeof(UINT)) + naive_C_Rules.UIntArray.elementStore.sizeA =
      p + i * sizeof(UINT) := by
    change (p + (i - 1) * sizeof(UINT)) + sizeof(UINT) = p + i * sizeof(UINT)
    ring
  simp only [Int.one_mul, Int.add_sub_cancel, haddr] at hmerge
  sep_apply hmerge
  exact fun _ h => h

theorem uint_array_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy17
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

theorem uint_array_strategy31_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy31 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy31
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_full p i n (Znth i l 0) l (by omega))
  simp only [replace_Znth_Znth]
  exact fun _ h => h

theorem uint_array_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_full p i n v l (by omega))
  exact fun _ h => h

theorem uint_array_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy12
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.missing_i_merge_to_seg p x i y v l (by omega))
  exact fun _ h => h

theorem uint_array_strategy101_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy101 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy101
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.UIntArray.full_Zlength p n l); entailer!)

theorem uint_array_strategy102_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy102 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy102
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.UIntArray.seg_Zlength p x y l); entailer!)

theorem uint_array_strategy103_correctness : SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy103 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_goal.uint_array_strategy103
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.UIntArray.missing_i_Zlength p i x y l); entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.uint_array_strategy_proof
