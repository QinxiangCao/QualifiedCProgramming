import SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance poly_sllStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem poly_sll_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy1
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy2
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy4
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll_zero storeA 0 l rfl)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem poly_sll_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy16
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy17
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg_self_with_sll storeA p l l0)
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)

theorem poly_sll_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy18
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy19
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy7
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)

theorem poly_sll_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy10
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  Intros h y
  Exists y h
  entailer!
  all_goals (try cancel; try wand_elim; pureIntros; try cancel; try entailer!)

theorem poly_sll_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy11
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  rename_i p h v storeA tail y hd hy
  Exists h y
  entailer!
  all_goals (try exact Or.elim (by assumption : _ ≠ 0 ∨ 0 ≠ _) id Ne.symm)

theorem poly_sll_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy12
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  sep_apply (SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg_sll storeA p q l0 _)
  try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.append]
  exact fun _ h => h

theorem poly_sll_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy8
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll_not_zero storeA p l (Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm))
  Intros h y v tail
  Exists v tail
  simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2]
  Exists h y
  all_goals (try cancel; try entailer!; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try assumption; try exact fun _ h => h)
  exact Or.elim (by assumption : p≠0 ∨ 0≠p) id Ne.symm

theorem poly_sll_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_goal.poly_sll_strategy9
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (wand_elim; pureIntros; subst_vars; try simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_1, SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sllseg.eq_2]; pureIntros; try entailer!; try cancel)
  all_goals (try first | exact fun _ h => h | exact fun _ h => ⟨by assumption, h⟩ | assumption | omega)
  Intros h y
  subst_vars
  simp only [SimpleC.EE.QCP_demos_LLM.poly_sll_lib.sll.eq_2]
  Exists h y
  entailer!

end SimpleC.EE.QCP_demos_LLM.generated.poly_sll_strategy_proof
