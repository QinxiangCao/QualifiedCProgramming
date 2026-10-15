import SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sllStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem sll_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy3
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy4
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy5
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy6
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  Intros q
  subst_vars
  Exists q
  entailer!

theorem sll_strategy21_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy21 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy21
  intro p l
  cases l
  all_goals try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  all_goals pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  Intros q
  Exists head q tail
  entailer!

theorem sll_strategy22_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy22 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy22
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  Exists (d :: l0)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2]
  Exists q
  entailer!
  all_goals exact Or.elim (by assumption : p ≠ 0 ∨ 0 ≠ p) id Ne.symm

theorem sll_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy14
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy15
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy16
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy17
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy18
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy19
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy20_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy20 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy20
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  exact Or.elim (by assumption : p = 0 ∨ 0 = p) id Eq.symm

theorem sll_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy7
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy10
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  Intros q
  Exists q
  entailer!

theorem sll_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy11
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)

theorem sll_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy8
  intro p l
  cases l
  all_goals try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  all_goals pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  Intros q
  Exists head tail q
  entailer!
  all_goals (try cancel; try wand_elim; try cancel; try entailer!)

theorem sll_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_goal.sll_strategy9
  try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, NULL]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllbseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  all_goals (try (Intros; pureIntros; subst_vars; try cancel; try entailer!))
  all_goals (try exact fun _ h => ⟨_, by assumption, by assumption, by assumption, h⟩)
  Intros q
  subst_vars
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2]
  Exists q
  entailer!

end SimpleC.EE.QCP_demos_LLM.generated.sll_strategy_proof
