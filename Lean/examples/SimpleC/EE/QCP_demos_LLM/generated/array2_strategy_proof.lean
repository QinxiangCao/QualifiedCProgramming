import SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance array2StrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem array2_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy1
  pre_process_default
  pureIntros
  subst_vars
  prop_apply (naive_C_Rules.IntArray2.full_Zlength p n m rows)
  pureIntros
  have hz := Znth_indep rows i [] __default_app1_Z (by omega)
  sep_apply (naive_C_Rules.IntArray2.full_split_to_missing_i p i n m rows (by omega))
  rw [hz]
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- _
  sep_apply (naive_C_Rules.IntArray.full_split_to_missing_i (p+i*m*sizeof(INT)) j m (Znth i rows __default_app1_Z) 0 (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy6
  pre_process_default
  pureIntros
  subst_vars
  have haddr : p+(i*m+j)*sizeof(INT) = p+i*m*sizeof(INT)+j*sizeof(INT) := by ring
  rw [haddr]
  prop_apply (naive_C_Rules.IntArray2.full_Zlength p n m rows)
  pureIntros
  have hz := Znth_indep rows i [] __default_app1_Z (by omega)
  sep_apply (naive_C_Rules.IntArray2.full_split_to_missing_i p i n m rows (by omega))
  rw [hz]
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- _
  sep_apply (naive_C_Rules.IntArray.full_split_to_missing_i (p+i*m*sizeof(INT)) j m (Znth i rows __default_app1_Z) 0 (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy7
  pre_process_default
  pureIntros
  subst_vars
  have haddr : p+i*(sizeof(INT)*m) = p+i*m*sizeof(INT) := by ring
  rw [haddr]
  prop_apply (naive_C_Rules.IntArray2.full_Zlength p n m rows)
  pureIntros
  have hz := Znth_indep rows i [] __default_app1_Z (by omega)
  sep_apply (naive_C_Rules.IntArray2.full_split_to_missing_i p i n m rows (by omega))
  rw [hz]
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- _
  sep_apply (naive_C_Rules.IntArray.full_split_to_missing_i (p+i*m*sizeof(INT)) j m (Znth i rows __default_app1_Z) 0 (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem array2_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem array2_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy2
  pre_process_default
  pureIntros
  subst_vars
  have hmerge := naive_C_Rules.IntArray2.missing_i_merge_to_full p i n m rows (Znth i rows __default_app1_Z) (by omega)
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- naive_C_Rules.IntArray2.full p n m (replace_Znth i (Znth i rows __default_app1_Z) rows) at hmerge
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hmerge ⊢
  sep_apply hmerge
  all_goals (try simp only [replace_Znth_Znth]; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy8
  pre_process_default
  pureIntros
  subst_vars
  have hmerge := naive_C_Rules.IntArray2.missing_i_merge_to_full p i n m rows (Znth i rows __default_app1_Z) (by omega)
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- naive_C_Rules.IntArray2.full p n m (replace_Znth i (Znth i rows __default_app1_Z) rows) at hmerge
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hmerge ⊢
  sep_apply hmerge
  all_goals (try simp only [replace_Znth_Znth]; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy9
  pre_process_default
  pureIntros
  subst_vars
  have hmerge := naive_C_Rules.IntArray2.missing_i_merge_to_full p i n m rows (Znth i rows __default_app1_Z) (by omega)
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- naive_C_Rules.IntArray2.full p n m (replace_Znth i (Znth i rows __default_app1_Z) rows) at hmerge
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hmerge ⊢
  sep_apply hmerge
  all_goals (try simp only [replace_Znth_Znth]; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy10
  pre_process_default
  pureIntros
  subst_vars
  have hmerge := naive_C_Rules.IntArray2.missing_i_merge_to_full p i n m rows row (by omega)
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m row ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- naive_C_Rules.IntArray2.full p n m (replace_Znth i row rows) at hmerge
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hmerge ⊢
  sep_apply hmerge
  all_goals (try simp only [replace_Znth_Znth]; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy11
  pre_process_default
  pureIntros
  subst_vars
  have hmerge := naive_C_Rules.IntArray2.missing_i_merge_to_full p i n m rows row (by omega)
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m row ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- naive_C_Rules.IntArray2.full p n m (replace_Znth i row rows) at hmerge
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hmerge ⊢
  sep_apply hmerge
  all_goals (try simp only [replace_Znth_Znth]; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array2_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_goal.array2_strategy12
  pre_process_default
  pureIntros
  subst_vars
  have hmerge := naive_C_Rules.IntArray2.missing_i_merge_to_full p i n m rows row (by omega)
  change (naive_C_Rules.IntArray.full (p+i*m*sizeof(INT)) m row ** naive_C_Rules.IntArray2.missing_i p i 0 n m rows) |-- naive_C_Rules.IntArray2.full p n m (replace_Znth i row rows) at hmerge
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hmerge ⊢
  sep_apply hmerge
  all_goals (try simp only [replace_Znth_Znth]; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

end SimpleC.EE.QCP_demos_LLM.generated.array2_strategy_proof
