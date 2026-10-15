import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_lib

def Pre (x1 y1 x2 y2 x y : Int) : Prop := True

def AbsDiff (a b : Int) : Int := if a < b then b - a else a - b

def Reachable (x1 y1 x2 y2 x y : Int) : Prop :=
  Z.rem (AbsDiff x1 x2) x = 0 ∧ Z.rem (AbsDiff y1 y2) y = 0 ∧
    Z.rem (Z.quot (AbsDiff x1 x2) x) 2 = Z.rem (Z.quot (AbsDiff y1 y2) y) 2

def Spec (x1 y1 x2 y2 x y out : Int) : Prop :=
  (Reachable x1 y1 x2 y2 x y ∧ out = 1) ∨
  (¬ Reachable x1 y1 x2 y2 x y ∧ out = 0)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_lib
