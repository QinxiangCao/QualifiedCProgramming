import SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance array3StrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem array3_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy1
  pre_process_default
  pureIntros
  subst am ak
  try subst ak2
  have haddr : p+i*((sizeof(INT)*k)*m) = p+i*m*k*sizeof(INT) := by ring
  simp only [haddr, Int.zero_mul, Int.add_zero]
  prop_apply (naive_C_Rules.IntArray3.full_Zlength p n m k cubes)
  pureIntros
  sep_apply (naive_C_Rules.IntArray3.full_split_to_missing_i p i n m k cubes (by omega))
  change (naive_C_Rules.IntArray2.full (p+i*m*k*sizeof(INT)) m k (Znth i cubes []) ** naive_C_Rules.IntArray3.missing_i p i 0 n m k cubes) |-- _
  cancel
  Intros_r plane d
  wand_elim
  pureIntros
  subst plane
  rw [Znth_indep cubes i [] d (by omega)]
  exact fun _ h => h

theorem array3_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy2
  pre_process_default
  pureIntros
  subst am ak
  try subst ak2
  have haddr : p+i*((sizeof(INT)*k)*m) = p+i*m*k*sizeof(INT) := by ring
  simp only [haddr, Int.zero_mul, Int.add_zero]
  prop_apply (naive_C_Rules.IntArray3.full_Zlength p n m k cubes)
  pureIntros
  sep_apply (naive_C_Rules.IntArray3.full_split_to_missing_i p i n m k cubes (by omega))
  change (naive_C_Rules.IntArray2.full (p+i*m*k*sizeof(INT)) m k (Znth i cubes []) ** naive_C_Rules.IntArray3.missing_i p i 0 n m k cubes) |-- _
  rw [Znth_indep cubes i [] __default_app1_app1_Z (by omega)]
  cancel
  wand_elim
  pureIntros
  entailer!

theorem array3_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy6
  pre_process_default
  pureIntros
  subst am ak
  try subst ak2
  have haddr : p+i*((sizeof(INT)*k)*m) = p+i*m*k*sizeof(INT) := by ring
  simp only [haddr, Int.zero_mul, Int.add_zero]
  prop_apply (naive_C_Rules.IntArray3.full_Zlength p n m k cubes)
  pureIntros
  sep_apply (naive_C_Rules.IntArray3.full_split_to_missing_i p i n m k cubes (by omega))
  change (naive_C_Rules.IntArray2.full (p+i*m*k*sizeof(INT)) m k (Znth i cubes []) ** naive_C_Rules.IntArray3.missing_i p i 0 n m k cubes) |-- _
  cancel
  Intros_r plane d
  wand_elim
  pureIntros
  subst plane
  rw [Znth_indep cubes i [] d (by omega)]
  exact fun _ h => h

theorem array3_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem array3_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem array3_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy3
  pre_process_default
  pureIntros
  subst am ak
  try subst ak2
  have haddr : p+i*((sizeof(INT)*k)*m) = p+i*m*k*sizeof(INT) := by ring
  simp only [haddr, Int.zero_mul, Int.add_zero]
  have hmerge := naive_C_Rules.IntArray3.missing_i_merge_to_full p i n m k cubes (Znth i cubes __default_app1_app1_Z) (by omega)
  change (naive_C_Rules.IntArray2.full (p+i*m*k*sizeof(INT)) m k (Znth i cubes __default_app1_app1_Z) ** naive_C_Rules.IntArray3.missing_i p i 0 n m k cubes) |-- naive_C_Rules.IntArray3.full p n m k (replace_Znth i (Znth i cubes __default_app1_app1_Z) cubes) at hmerge
  sep_apply hmerge
  simp only [replace_Znth_Znth]
  exact fun _ h => h

theorem array3_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_goal.array3_strategy7
  pre_process_default
  pureIntros
  subst am ak
  try subst ak2
  have haddr : p+i*((sizeof(INT)*k)*m) = p+i*m*k*sizeof(INT) := by ring
  simp only [haddr, Int.zero_mul, Int.add_zero]
  have hmerge := naive_C_Rules.IntArray3.missing_i_merge_to_full p i n m k cubes (Znth i cubes __default_app1_app1_Z) (by omega)
  change (naive_C_Rules.IntArray2.full (p+i*m*k*sizeof(INT)) m k (Znth i cubes __default_app1_app1_Z) ** naive_C_Rules.IntArray3.missing_i p i 0 n m k cubes) |-- naive_C_Rules.IntArray3.full p n m k (replace_Znth i (Znth i cubes __default_app1_app1_Z) cubes) at hmerge
  sep_apply hmerge
  simp only [replace_Znth_Znth]
  exact fun _ h => h

end SimpleC.EE.QCP_demos_LLM.generated.array3_strategy_proof
