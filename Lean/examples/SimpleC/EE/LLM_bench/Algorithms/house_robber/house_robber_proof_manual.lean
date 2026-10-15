import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open house_robber_goal house_robber_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem bounded_values (l : List Int)
    (hl : Forall (fun x : Int => 0 ≤ x) l) (hu : Forall (fun x : Int => x ≤ 10000) l) :
    ∀ k, 0 ≤ k ∧ k < Zlength l → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 10000 := by
  intro k hk
  have hi : k.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hk; omega
  have hm := List.getElem_mem (l := l) hi
  have h1 := hl.mem hm
  have h2 := hu.mem hm
  simpa only [Znth, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some] using And.intro h1 h2

theorem proof_of_rob_safety_wit_4 : rob_safety_wit_4 := by
  unfold rob_safety_wit_4
  right
  intro n nums l prev2 prev1 i hi hn hlen hl hu hi0 hin hs
  have hr : ∀ k, 0 ≤ k ∧ k < n → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 10000 := by
    simpa only [hlen] using bounded_values l hl hu
  have upper := house_robber_take_value_bound l n i prev2 prev1 hlen hn hr hi0 hi hs
  have nonneg : 0 ≤ prev2 := by
    rcases hs.2.2 with hz | hp
    · omega
    · exact (rob_prefix_opt_bound_by_len l (i-1) prev2 n (by omega) hr hp.2).1
  have elem := (hr i ⟨hi0,hi⟩).1
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega

theorem proof_of_rob_entail_wit_1_split_goal_1 : rob_entail_wit_1_split_goal_1 := by
  intro n l hn _ hlen _ _
  exact ⟨by omega, RobPrefixOpt_zero l, Or.inl ⟨rfl,rfl⟩⟩

theorem proof_of_rob_entail_wit_1 : rob_entail_wit_1 := by
  unfold rob_entail_wit_1
  right
  intro n l hn hbound hlen hl hu
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_rob_entail_wit_1_split_goal_1 n l hn hbound hlen hl hu

theorem proof_of_rob_entail_wit_2_1_split_goal_1 : rob_entail_wit_2_1_split_goal_1 := by
  intro n l prev2 prev1 i ht hi _ hlen _ _ hi0 _ hs
  exact house_robber_dp_step_take l n i prev2 prev1 hlen hi0 hi hs ht

theorem proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1 := by
  unfold rob_entail_wit_2_1
  right
  intro n l prev2 prev1 i ht hi hn hlen hl hu hi0 hin hs
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_rob_entail_wit_2_1_split_goal_1 n l prev2 prev1 i ht hi hn hlen hl hu hi0 hin hs

theorem proof_of_rob_entail_wit_2_2_split_goal_1 : rob_entail_wit_2_2_split_goal_1 := by
  intro n l prev2 prev1 i ht hi _ hlen _ _ _ _ hs
  exact HouseRobberDPState_skip_step l i prev2 prev1 hs ht (by omega)

theorem proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2 := by
  unfold rob_entail_wit_2_2
  right
  intro n l prev2 prev1 i ht hi hn hlen hl hu hi0 hin hs
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_rob_entail_wit_2_2_split_goal_1 n l prev2 prev1 i ht hi hn hlen hl hu hi0 hin hs

theorem proof_of_rob_return_wit_1_split_goal_1 : rob_return_wit_1_split_goal_1 := by
  intro n l prev2 prev1 i hi _ hlen _ _ _ hin hs
  have he : i = Zlength l := by omega
  change RobPrefixOpt l (Zlength l) prev1
  simpa only [he] using hs.2.1

theorem proof_of_rob_return_wit_1 : rob_return_wit_1 := by
  unfold rob_return_wit_1
  right
  intro n l prev2 prev1 i hi hn hlen hl hu hi0 hin hs
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_rob_return_wit_1_split_goal_1 n l prev2 prev1 i hi hn hlen hl hu hi0 hin hs

end SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual
