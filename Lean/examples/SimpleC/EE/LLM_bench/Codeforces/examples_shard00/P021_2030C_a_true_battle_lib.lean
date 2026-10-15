import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib
open AUXLib

def HasAdjacentOnes (values : List Int) : Prop :=
  ∃ i : Int, 0 ≤ i ∧ i + 1 < Zlength values ∧
    Znth i values 0 = 49 ∧ Znth (i + 1) values 0 = 49

def NoAdjacentOnesBefore (values : List Int) (upto : Int) : Prop :=
  ∀ i : Int, (0 ≤ i ∧ i < upto) → Znth i values 0 ≠ 49 ∨ Znth (i + 1) values 0 ≠ 49

def WinningCriterion (values : List Int) : Prop :=
  Znth 0 values 0 = 49 ∨ Znth (Zlength values - 1) values 0 = 49 ∨ HasAdjacentOnes values

def Pre (values : List Int) : Prop :=
  (2 ≤ Zlength values ∧ Zlength values ≤ 200000) ∧ Forall (fun c => c = 48 ∨ c = 49) values

def Spec (values : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ WinningCriterion values)


theorem no_adjacent_ones_before_succ__loop_transition (values : List Int) (i : Int)
    (hi : 0 ≤ i) (ho : NoAdjacentOnesBefore values i)
    (hn : Znth i values 0 ≠ 49 ∨ Znth (i + 1) values 0 ≠ 49) :
    NoAdjacentOnesBefore values (i + 1) := by
  intro k hk
  by_cases h : k < i
  · exact ho k ⟨hk.1, h⟩
  · have he : k = i := by omega
    simpa only [he] using hn

theorem spec_zero_from_completed_scan__final_results (values : List Int) (n i : Int)
    (hn : n = Zlength values) (hi0 : 0 ≤ i) (hi1 : i ≤ n - 1) (hi2 : i + 1 ≥ n)
    (hf : Znth 0 values 0 ≠ 49) (hl : Znth (Zlength values - 1) values 0 ≠ 49)
    (hs : NoAdjacentOnesBefore values i) : Spec values 0 := by
  refine ⟨Or.inl rfl, ⟨by intro h; omega, ?_⟩⟩
  rintro (hw | hw | ⟨j, hj0, hjn, hj, hj1⟩)
  · exact False.elim (hf hw)
  · exact False.elim (hl hw)
  · rcases hs j ⟨hj0, by omega⟩ with hh | hh
    · exact False.elim (hh hj)
    · exact False.elim (hh hj1)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib
