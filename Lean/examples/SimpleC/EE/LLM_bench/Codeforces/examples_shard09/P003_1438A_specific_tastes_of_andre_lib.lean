import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib

def Pre (n : Int) : Prop := True

def Perfect (n : Int) (a : List Int) : Prop :=
  AUXLib.Zlength a = n ∧ AUXLib.Forall (fun x => 1 ≤ x ∧ x ≤ 100) a ∧
    ∀ l r : Int, ((0 ≤ l ∧ l < r) ∧ r ≤ n) →
      Z.divide (r - l) ((AUXLib.sublist l r a).foldr (· + ·) 0)

def Spec (n : Int) (out : List Int) : Prop := Perfect n out

def VerdictCode (answer : Bool) (code : Int) : Prop :=
  (answer = true ∧ code = 1) ∨ (answer = false ∧ code = 0)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib
