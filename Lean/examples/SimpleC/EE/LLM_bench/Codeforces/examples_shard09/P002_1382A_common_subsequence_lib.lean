import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.IndexedElements
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib

abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none

def Pre (a b : List Int) : Prop := True

def CommonNonempty (a b c : List Int) : Prop :=
  c ≠ [] ∧ ListLib.is_subsequence c a ∧ ListLib.is_subsequence c b

def Spec (a b : List Int) (out : Option (List Int)) : Prop :=
  (out = none ∧ ¬ ∃ c, CommonNonempty a b c) ∨
    ∃ c, out = some c ∧ MaxMinLib.min_object_of_subset (· ≤ ·) (CommonNonempty a b)
      (fun ys => AUXLib.Zlength ys) c

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib
