import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic


set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib

def OnBorder (r c i j : Int) : Prop :=
  i = 0 ∨ i = r - 1 ∨ j = 0 ∨ j = c - 1

def BeautifulFlat (r c : Int) (s : List Int) : Prop :=
  1 ≤ r ∧ 1 ≤ c ∧ AUXLib.Zlength s = r * c ∧
  ∀ i j : Int, (0 ≤ i ∧ i < r) → (0 ≤ j ∧ j < c) →
    (OnBorder r c i j ∧ AUXLib.Znth (i * c + j) s 0 = 49) ∨
    (¬ OnBorder r c i j ∧ AUXLib.Znth (i * c + j) s 0 = 48)

def Pre (s : List Int) : Prop := ∃ r c, BeautifulFlat r c s

def Spec (s : List Int) (out : Int) : Prop :=
  (out = 1 ∧ ∃ q, BeautifulFlat q q s) ∨ (out = 0 ∧ ¬ ∃ q, BeautifulFlat q q s)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib
