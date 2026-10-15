import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P011_765A_neverending_competitions_goal P011_765A_neverending_competitions_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem land_one (n : Int) : Z.land n 1 = Z.modulo n 2 := by
  exact Z.land_ones n 1 (by decide)

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n rows flights home default h1 h2 h3 h4 h5 h6 h7 h8 h9
  rcases h6 with ⟨_, _, hf, current, hit⟩
  have hf' : Forall (fun f => (f.1 = home ∧ f.2 ≠ home) ∨
      (f.1 ≠ home ∧ f.2 = home)) flights := by
    apply Forall.iff_forall_mem.mpr
    intro f hm
    exact (hf.mem hm).2.2
  have he := itinerary_endpoint_parity__return_parity home flights current hf' hit
  rw [h7, land_one] at h1
  exact Or.inr ⟨rfl, current, (fun hc => h1 (he.mp hc)), hit⟩

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n rows flights home default h1 h2 h3 h4 h5 h6 h7 h8 h9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 n rows flights home default h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro n rows flights home default h1 h2 h3 h4 h5 h6 h7 h8 h9
  rcases h6 with ⟨_, _, hf, current, hit⟩
  have hf' : Forall (fun f => (f.1 = home ∧ f.2 ≠ home) ∨
      (f.1 ≠ home ∧ f.2 = home)) flights := by
    apply Forall.iff_forall_mem.mpr
    intro f hm
    exact (hf.mem hm).2.2
  have he := itinerary_endpoint_parity__return_parity home flights current hf' hit
  rw [h7, land_one] at h1
  have hc := he.mpr h1
  exact Or.inl ⟨rfl, hc ▸ hit⟩

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro n rows flights home default h1 h2 h3 h4 h5 h6 h7 h8 h9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_2_split_goal_1 n rows flights home default h1 h2 h3 h4 h5 h6 h7 h8 h9

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_proof_manual
