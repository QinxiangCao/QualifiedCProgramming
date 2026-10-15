import SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_proof

open SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal
open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_shapeStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem sll_shape_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (listrep_zero 0 rfl)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy4
  pre_process_default
  pureIntros
  subst_vars
  unfold listrep
  Exists ([] : List Int)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, NULL]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy5
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros)
  unfold listrep
  Exists ([] : List Int)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sll.eq_1, NULL]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)
  exact Or.elim (by assumption : p=0 ∨ 0=p) id Eq.symm

theorem sll_shape_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy14
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros)
  unfold lseg
  Exists ([] : List Int)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy15
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros)
  unfold lseg
  Split
  · Left
    Exists ([] : List Int)
    simp only [sll_lib.sllseg.eq_1]
    entailer!
  · Right
    Exists ([] : List Int)
    simp only [sll_lib.sllseg.eq_1]
    entailer!

theorem sll_shape_strategy23_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy23 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy23
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros)
  unfold lseg
  Exists ([] : List Int)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy25_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy25 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy25
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (lseg_listrep q q)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy6
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (listrep_zero p (Or.elim (by assumption : p=0 ∨ 0=p) id Eq.symm))
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy10
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (lseg_listrep p q)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy16
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  Intros_r v
  wand_elim
  pureIntros
  sep_apply (lseg_len1 q v z (Or.elim (by assumption : q≠0 ∨ 0≠q) id Ne.symm))
  sep_apply (lseg_lseg p q z)
  cancel

theorem sll_shape_strategy21_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy21 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy21
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  unfold listrep lseg
  Intros l
  Exists l
  exact sll_lib.sll_sllseg_0 p l

theorem sll_shape_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy11
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  Split
  · Left
    pureIntros
    refine coq_prop_andp_right SacContext.rules _ _ _ ?_ (by assumption)
    cancel
    Intros_r v y
    wand_elim
    pureIntros
    unfold listrep
    Intros tail
    Exists (v :: tail)
    simp only [sll_lib.sll.eq_2]
    Exists y
    entailer!
    exact Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm
  · Right
    pureIntros
    refine coq_prop_andp_right SacContext.rules _ _ _ ?_ (by assumption)
    cancel
    Intros_r v y
    wand_elim
    pureIntros
    unfold listrep
    Intros tail
    Exists (v :: tail)
    simp only [sll_lib.sll.eq_2]
    Exists y
    entailer!
    exact Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm


theorem sll_shape_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy17
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  Intros_r v y z
  wand_elim
  pureIntros
  sep_apply (lseg_len1 p v y (Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm))
  sep_apply (lseg_lseg p y z)
  cancel

theorem sll_shape_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy18
  pre_process_default
  pureIntros
  subst_vars
  rename_i z
  sep_apply (lseg_lseg p q z)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy19
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros)
  unfold lseg
  Exists ([] : List Int)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy20_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy20 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy20
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros)
  unfold lseg
  Exists ([] : List Int)
  simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1]
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy24_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy24 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy24
  pre_process_default
  pureIntros
  subst_vars
  unfold lseg
  Intros l
  cases l <;> simp only [SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.sll_lib.sllseg.eq_2, NULL]
  all_goals (try (Intros z); pureIntros; subst_vars; try contradiction; try cancel; try entailer!)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy7
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem sll_shape_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy8
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (listrep_nonzero p (Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm))
  Intros y v
  Exists v y
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

theorem sll_shape_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy9
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  Intros_r v y
  wand_elim
  pureIntros
  unfold listrep
  Intros tail
  Exists (v :: tail)
  simp only [sll_lib.sll.eq_2]
  Exists y
  entailer!
  exact Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm

theorem sll_shape_strategy22_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy22 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal.sll_shape_strategy22
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (lseg_unfold_head p q (Or.elim (by assumption : p≠q ∨ q≠p) id Ne.symm))
  Intros v z
  Exists v z
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h; try assumption)

end SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_proof
