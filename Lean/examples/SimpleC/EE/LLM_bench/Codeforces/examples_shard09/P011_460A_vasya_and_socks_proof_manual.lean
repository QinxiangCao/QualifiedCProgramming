import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_goal
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- C division and Coq's specification division agree for these nonnegative operands.
private theorem quot_eq_div (d m : Int) (hd : 0 ≤ d) (hm : 0 ≤ m) :
    Z.quot d m = Z.div d m :=
  (Int.fdiv_eq_tdiv_of_nonneg hd hm).symm

private theorem quot_step_zero (d m : Int) (hd : 0 ≤ d) (hm : 2 ≤ m)
    (hr : Z.rem (d + 1) m = 0) :
    Z.quot (d + 1) m = Z.quot d m + 1 := by
  have hnext := Z.quot_rem (d + 1) m (by omega)
  rw [hr] at hnext
  have hlo := Z.quot_le_lower_bound d m (Z.quot (d + 1) m - 1) (by omega)
    (by nlinarith)
  have hhi := Z.quot_lt_upper_bound d m (Z.quot (d + 1) m) hd (by omega)
    (by nlinarith)
  omega

private theorem quot_step_nonzero (d m : Int) (hd : 0 ≤ d) (hm : 2 ≤ m)
    (hr : Z.rem (d + 1) m ≠ 0) :
    Z.quot (d + 1) m = Z.quot d m := by
  have hnext := Z.quot_rem (d + 1) m (by omega)
  have hbounds := Z.rem_bound_pos_pos (d + 1) m (by omega) (by omega)
  have hlo := Z.quot_le_lower_bound d m (Z.quot (d + 1) m) (by omega)
    (by omega)
  have hhi := Z.quot_lt_upper_bound d m (Z.quot (d + 1) m + 1) hd (by omega)
    (by nlinarith)
  omega

private theorem days_bound (m n₀ n d : Int) (hm : 2 ≤ m) (hn₀ : n₀ ≤ 100)
    (hn : 0 < n) (hd : 0 ≤ d) (heq : n = n₀ + Z.quot d m - d) : d + 1 ≤ 200 := by
  have hq := Z.quot_pos d m hd (by omega)
  have hr := Z.rem_bound_pos_pos d m (by omega) hd
  have hdecomp := Z.quot_rem d m (by omega)
  have hmul := Int.mul_nonneg (show 0 ≤ m - 2 by omega) hq
  nlinarith

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  unfold solver_entail_wit_1_split_goal_1
  intros
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro m n hn hnmax hm hmmax
  rw [Z.quot_0_l m (by omega)]
  omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro m n hn hnmax hm hmmax
  have h1 := proof_of_solver_entail_wit_1_split_goal_1 m n hn hnmax hm hmmax
  have h2 := proof_of_solver_entail_wit_1_split_goal_2 m n hn hnmax hm hmmax
  entailer!

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have hstep := quot_step_zero d m hd hm hr
  omega

theorem proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2 := by
  intro m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  exact days_bound m n₀ n d hm hn₀max hn hd heq

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have h1 := proof_of_solver_entail_wit_2_1_split_goal_1 m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have h2 := proof_of_solver_entail_wit_2_1_split_goal_2 m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  entailer!

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have hstep := quot_step_nonzero d m hd hm hr
  omega

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  exact days_bound m n₀ n d hm hn₀max hn hd heq

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have h1 := proof_of_solver_entail_wit_2_2_split_goal_1 m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have h2 := proof_of_solver_entail_wit_2_2_split_goal_2 m n₀ n d hr hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  entailer!

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro m n₀ n days hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have hq := Z.quot_pos days m hd (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · intro d hbound
    rw [← quot_eq_div (d - 1) m (by omega) (by omega)]
    exact hprev d hbound
  · rw [← quot_eq_div days m hd (by omega)]
    omega

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro m n₀ n days hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  have hs := proof_of_solver_return_wit_1_split_goal_1 m n₀ n days hn hn₀ hn₀max hm hmmax hd hdmax hn0 hnmax heq hprev
  entailer!

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_proof_manual
