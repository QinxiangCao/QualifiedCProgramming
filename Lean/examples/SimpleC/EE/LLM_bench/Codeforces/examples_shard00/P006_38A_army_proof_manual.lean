import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem next_year_bounds (years : List Int) (a b i : Int)
    (hb : b ≤ Zlength years + 1) (ha : 1 ≤ a) (hai : a ≤ i) (hib : i < b)
    (hyears : ∀ idx : Int, 0 ≤ idx ∧ idx < Zlength years →
      1 ≤ Znth idx years 0 ∧ Znth idx years 0 ≤ 100) :
    1 ≤ Znth i (0 :: years) 0 ∧ Znth i (0 :: years) 0 ≤ 100 := by
  rw [Znth_cons 0 i 0 years (by omega)]
  exact hyears (i - 1) ⟨by omega, by omega⟩

theorem proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1 := by
  intro b a d years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hnext := next_year_bounds years a b i hb ha hai hib hy
  have hbound : ans + Znth i (0 :: years) 0 ≤ INT_MAX := by
    change ans + Znth i (0 :: years) 0 ≤ (2147483647 : Int)
    omega
  entailer!

theorem proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2 := by
  intro b a d years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hnext := next_year_bounds years a b i hb ha hai hib hy
  have hbound : INT_MIN ≤ ans + Znth i (0 :: years) 0 := by
    change (-2147483648 : Int) ≤ ans + Znth i (0 :: years) 0
    omega
  entailer!

theorem proof_of_solver_safety_wit_3 : solver_safety_wit_3 := by
  left
  intro b a d years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hnext := next_year_bounds years a b i hb ha hai hib hy
  have hupper : ans + Znth i (0 :: years) 0 ≤ INT_MAX := by
    change ans + Znth i (0 :: years) 0 ≤ (2147483647 : Int)
    omega
  have hlower : INT_MIN ≤ ans + Znth i (0 :: years) 0 := by
    change (-2147483648 : Int) ≤ ans + Znth i (0 :: years) 0
    omega
  entailer!

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro b a years hn hnmax hy ha hab hb
  unfold Spec
  rw [Zsublist_nil years (a - 1) (a - 1) (by omega)]
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro b a years hn hnmax hy ha hab hb
  exact hy

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro b a years hn hnmax hy ha hab hb
  have hspec := proof_of_solver_entail_wit_1_split_goal_1 b a years hn hnmax hy ha hab hb
  entailer!

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  exact Spec_succ__loop_step _ years a i ans ha hai (by omega) hs

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hnext := next_year_bounds years a b i hb ha hai hib hy
  omega

theorem proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3 := by
  intro b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hnext := next_year_bounds years a b i hb ha hai hib hy
  omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hspec := proof_of_solver_entail_wit_2_split_goal_1 b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hupper := proof_of_solver_entail_wit_2_split_goal_2 b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hlower := proof_of_solver_entail_wit_2_split_goal_3 b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  entailer!

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hi : i = b := by omega
  simpa [hi] using hs

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  have hspec := proof_of_solver_return_wit_1_split_goal_1 b a years ans i hib hn hnmax hy ha hai hib' hb hans hansmax hs
  entailer!

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual
