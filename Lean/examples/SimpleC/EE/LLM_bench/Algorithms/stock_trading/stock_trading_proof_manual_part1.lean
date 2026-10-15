import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part1
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open stock_trading_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2

local macro "finish_entail" : tactic => `(tactic| (
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto))

private theorem product_bounds (x p : Int) (hx : 0 ≤ x ∧ x ≤ 990)
    (hp : 0 ≤ p ∧ p ≤ 1000) : 0 ≤ x*p ∧ x*p ≤ 990000 :=
  ⟨Int.mul_nonneg hx.1 hp.1, Int.mul_le_mul hx.2 hp.2 hp.1 (by omega)⟩

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part1
