import SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_dataStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem sll_data_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sll_zero 0 l rfl)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem sll_data_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  exact Or.elim (by assumption : p=0 ∨ 0=p) id Eq.symm

theorem sll_data_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy14
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem sll_data_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy15
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  intro heap h
  rcases h with h | h
  · exact Or.inl ⟨h.1, trivial, h.2⟩
  · exact Or.inr ⟨h.1, trivial, h.2⟩

theorem sll_data_strategy25_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy25 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy25
  pre_process_default
  pureIntros
  subst_vars
  Exists (l1 ++ l2)
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg_sll q q l1 l2)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy23_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy23 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy23
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem sll_data_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy6
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sll_zero p l (Or.elim (by assumption : p=0 ∨ 0=p) id Eq.symm))
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy10
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; pureIntros; subst_vars)
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg_sll p q l1 _)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy16
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  rename_i v hv
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg_len1 q v z (Or.elim (by assumption : q≠0 ∨ 0≠q) id Ne.symm))
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg_sllseg p q z l1 [v])
  exact fun _ h => h

theorem sll_data_strategy21_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy21 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy21
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; pureIntros; subst_vars)
  exact SimpleC.EE.QCP_demos_LLM.sll_lib.sll_sllseg_0 p _
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy11
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  Split
  · Left
    pureIntros
    refine coq_prop_andp_right SacContext.rules _ _ _ ?_ (by assumption)
    cancel
    Intros_r l v tail y
    wand_elim
    pureIntros
    subst l
    simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2]
    Exists y
    entailer!
    exact Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm
  · Right
    pureIntros
    refine coq_prop_andp_right SacContext.rules _ _ _ ?_ (by assumption)
    cancel
    Intros_r l v tail y
    wand_elim
    pureIntros
    subst l
    simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2]
    Exists y
    entailer!
    exact Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm

theorem sll_data_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy17
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  exact fun _ h => ⟨_, Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm, by assumption, by assumption, h⟩

theorem sll_data_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy18
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; pureIntros; subst_vars)
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg_sllseg p q _ l1 _)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy19
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem sll_data_strategy20_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy20 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy20
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem sll_data_strategy24_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy24 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy24
  pre_process_default
  pureIntros
  subst_vars
  cases l <;> simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, NULL]
  all_goals (try (Intros z); pureIntros; subst_vars; try contradiction; try cancel; try entailer!)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy7
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem sll_data_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy8
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sll_not_zero p l (Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm))
  Intros y v l0
  Exists v y l0
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_data_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy9
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  exact fun _ h => ⟨_, Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm, by assumption, by assumption, h⟩

theorem sll_data_strategy22_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy22 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_goal.sll_data_strategy22
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try simp only [NULL] at *)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  sep_apply (SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg_unfold_head p q l (Or.elim (by assumption : p≠q ∨ q≠p) id Ne.symm))
  Intros v z tail
  Exists v z tail
  entailer!
  all_goals (try cancel; try wand_elim; pureIntros; try cancel; try entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.sll_data_strategy_proof
