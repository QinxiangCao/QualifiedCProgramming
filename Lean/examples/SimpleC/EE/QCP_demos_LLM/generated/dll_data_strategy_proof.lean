import SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance dll_dataStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem dll_data_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy1
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dll_zero 0 prev l rfl)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy2
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem dll_data_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy3
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  exact Or.elim (by assumption : p=0 ∨ 0=p) id Eq.symm

theorem dll_data_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy4
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dll_zero p prev l (Or.elim (by assumption : p=0 ∨ 0=p) id Eq.symm))
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy12
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem dll_data_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy7
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; pureIntros; subst_vars)
  trace_state
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg_dlistrep p s _ r l1 _)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy13_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy13 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy13
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  rename_i tail v p q y hd hn hp
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg_len1 s y m v (by assumption))
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg_dllseg p s m q y s tail [v])
  exact fun _ h => h

theorem dll_data_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy14
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg_head_neq_destruct_tail p m q s l (Ne.symm (by assumption)))
  Intros y tail v
  Exists v y tail
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy15
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; pureIntros; subst_vars)
  trace_state
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg_dlistrep p s _ r l1 _)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy16
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg_head_neq_destruct_tail' p m q s l (Ne.symm (by assumption)))
  Intros y tail v
  Exists v y tail
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy8
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem dll_data_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy11
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem dll_data_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy5
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dll_not_zero p prev l (Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm))
  Intros y v tail
  Exists v y tail
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem dll_data_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_goal.dll_data_strategy6
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dlistrep.eq_2, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_1, SimpleC.EE.QCP_demos_LLM.dll_queue_lib.dllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  exact fun _ h => ⟨_, Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm, by assumption, by assumption, by assumption, h⟩

end SimpleC.EE.QCP_demos_LLM.generated.dll_data_strategy_proof
