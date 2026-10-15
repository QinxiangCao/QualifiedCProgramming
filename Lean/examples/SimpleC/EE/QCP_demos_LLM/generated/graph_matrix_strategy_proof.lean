import SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance graph_matrixStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem graph_matrix_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy2
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  subst size
  have haddr : p+(i*n+j)*sizeof(INT) = p+i*n*sizeof(INT)+j*sizeof(INT) := by ring
  rw [haddr]
  prop_apply (naive_C_Rules.IntArray2.full_Zlength p n n rows)
  pureIntros
  sep_apply (naive_C_Rules.IntArray2.full_split_to_missing_i p i n n rows (by omega))
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  change (naive_C_Rules.IntArray.full (p+i*n*sizeof(INT)) n (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 n n rows) |-- _
  sep_apply (naive_C_Rules.IntArray.full_split_to_missing_i (p+i*n*sizeof(INT)) j n (Znth i rows __default_app1_Z) 0 (by omega))
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy3
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem graph_matrix_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy4
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  subst w
  have haddr : p+i*(sizeof(INT)*size) = p+i*size*sizeof(INT) := by ring
  rw [haddr]
  prop_apply (naive_C_Rules.IntArray2.full_Zlength p size size rows)
  pureIntros
  sep_apply (naive_C_Rules.IntArray2.full_split_to_missing_i p i size size rows (by omega))
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  change (naive_C_Rules.IntArray.full (p+i*size*sizeof(INT)) size (Znth i rows __default_app1_Z) ** naive_C_Rules.IntArray2.missing_i p i 0 size size rows) |-- _
  sep_apply (naive_C_Rules.IntArray.full_split_to_missing_i (p+i*size*sizeof(INT)) j size (Znth i rows __default_app1_Z) 0 (by omega))
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy6
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem graph_matrix_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy7
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  prop_apply (naive_C_Rules.IntPtrArray2.full_Zlength p size rows)
  pureIntros
  sep_apply (naive_C_Rules.IntPtrArray2.full_split_to_missing_i p i size rows (by omega))
  Intros row_ptr
  Exists row_ptr
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy8
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  subst read_ptr
  prop_apply (GraphMatrixPtr.missing_i_rows_Zlength p size i row_ptr rows)
  pureIntros
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  sep_apply (naive_C_Rules.IntArray.full_split_to_missing_i row_ptr j (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z) 0 (by omega))
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy9
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  prop_apply (GraphMatrixPtr.missing_i_rows_Zlength p size i row_ptr rows)
  pureIntros
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy10
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  prop_apply (GraphMatrixPtr.missing_i_rows_Zlength p size i row_ptr rows)
  pureIntros
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy11
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  pureIntros
  sep_apply (naive_C_Rules.IntPtrArray2.missing_i_merge_to_full p i size row_ptr rows (Znth i rows []) (by omega))
  simp only [replace_Znth_Znth]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem graph_matrix_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal.graph_matrix_strategy1
  simp only [GraphMatrixFlat.store_graph, GraphMatrixPtr.store_graph, GraphMatrixPtr.row_rep]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_proof
