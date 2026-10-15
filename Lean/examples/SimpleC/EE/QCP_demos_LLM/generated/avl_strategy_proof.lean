import SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance avlStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem avl_strategy0_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy0 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy0
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem avl_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy9
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem avl_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy12
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem avl_strategy25_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy25 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy25
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem avl_strategy26_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy26 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy26
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem avl_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy7
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy8
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy1
  pre_process_default
  cases tr with
  | empty =>
      simp only [store_tree.eq_1, NULL]
      pureIntros
      contradiction
  | make_tree tr1 tr2 =>
      simp only [store_tree.eq_2]
      Intros l r k v h
      Exists k v h l r tr1 tr2
      simp only [single_tree_node]
      entailer!
      all_goals (try cancel; try wand_elim; pureIntros; try cancel; try entailer!)

theorem avl_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy2
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try (Exists _ _ _ _ _; entailer!))
  all_goals (try exact fun _ h => h; try assumption)
  Intros_r tr tr1 tr2 l v h k r
  wand_elim
  pureIntros
  subst tr
  simp only [store_tree.eq_2]
  Exists l r k v h
  entailer!

theorem avl_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy3
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  cases tr <;> simp only [store_tree.eq_1, store_tree.eq_2, NULL]
  all_goals (pureIntros; try contradiction; try entailer!)
  all_goals (try (Intros l r k v h; try contradiction))
  all_goals (try exact fun _ h => h; try assumption)
  all_goals exact fun _ h => ⟨by assumption, trivial, h⟩

theorem avl_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy4
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)
  Intros_r tr
  wand_elim
  pureIntros
  subst tr
  simp only [store_tree.eq_1, NULL]
  entailer!

theorem avl_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy10
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (simp only [store_tree_shape]; Intros tr; Exists tr; try cancel; try entailer!; try wand_elim; try cancel)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy11
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (simp only [store_tree_shape]; Exists tr; cancel)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy13_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy13 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy13
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy15
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)
  wand_elim
  entailer!

theorem avl_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy16
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try (Exists _ _ _ _ _; entailer!))
  all_goals (try exact fun _ h => h; try assumption)
  Intros_r tr tr1 tr2 l v h k r
  wand_elim
  pureIntros
  subst tr
  simp only [store_tree.eq_2]
  Exists l r k v h
  entailer!

theorem avl_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy17
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy5
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem avl_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal.avl_strategy6
  try simp only [single_tree_node, store_non_empty_tree]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [store_tree.eq_1, store_tree.eq_2, NULL]; pureIntros; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

end SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_proof
