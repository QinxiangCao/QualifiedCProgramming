import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib

def Pre (n m : Int) : Prop := True

def Spec (n m out : Int) : Prop :=
  out > 0 ∧ (∀ d : Int, (1 ≤ d ∧ d ≤ out) → n + Z.div (d - 1) m - (d - 1) > 0) ∧
    n + Z.div out m - out = 0

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib
