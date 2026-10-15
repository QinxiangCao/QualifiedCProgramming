import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_proof_auto
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_proof_manual

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P003_1438A_specific_tastes_of_andre_goal P003_1438A_specific_tastes_of_andre_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem ones_of_nth (xs : List Int)
    (h : ∀ k, 0 ≤ k ∧ k < Zlength xs → Znth k xs 0 = 1) :
    Forall (fun x => x = 1) xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    have hx : x = 1 := by
      have hh := h 0 ⟨by omega, by simp only [Zlength_cons]; have := Zlength_nonneg xs; omega⟩
      simpa using hh
    refine .cons hx (ih ?_)
    intro k hk
    have hh := h (k + 1) ⟨by omega, by simp only [Zlength_cons]; omega⟩
    rw [Znth_cons 0 (k + 1) x xs (by omega)] at hh
    simpa using hh

private theorem sum_ones (xs : List Int) (h : Forall (fun x => x = 1) xs) :
    xs.foldr (· + ·) 0 = Zlength xs := by
  induction h with
  | nil => rfl
  | @cons x xs hx hxs ih => simp only [List.foldr_cons, Zlength_cons, hx, ih]; omega

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n hn hn' k hk
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n hn hn'
  rfl

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n hn hn'
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_solver_entail_wit_1_split_goal_1 n hn hn'
    · exact proof_of_solver_entail_wit_1_split_goal_2 n hn hn'

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro n written i hi hn hn' hi0 hin hlen hall
  simp only [Zlength_app, Zlength_cons, Zlength_nil, hlen, Int.zero_add]

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro n written i hi hn hn' hi0 hin hlen hall
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_split_goal_1 n written i hi hn hn' hi0 hin hlen hall

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro out n written i hi hn hn' hi0 hin hlen hall
  have heq : i = n := by omega
  rw [heq] at hlen hall ⊢
  have hones : Forall (fun x => x = 1) written :=
    ones_of_nth written (by simpa only [hlen] using hall)
  have hspec : Spec n written := by
    refine ⟨hlen, ?_, ?_⟩
    · apply Forall.iff_forall_mem.mpr
      intro x hx
      have hh := hones.mem hx
      omega
    · intro l r hrange
      have hsub : Forall (fun x => x = 1) (sublist l r written) := by
        apply Forall.iff_forall_mem.mpr
        intro x hx
        exact hones.mem (List.mem_of_mem_take (List.mem_of_mem_drop hx))
      refine ⟨1, ?_⟩
      have hsubLen : Zlength (sublist l r written) = r - l :=
        ListLib.Zlength_sublist l r written ⟨hrange.1.1, by omega⟩
          (by change r ≤ Zlength written; omega)
      rw [sum_ones _ hsub, hsubLen]
      omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) written ?_
  split_pure_spatial
  · simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using intArray.seg_to_full out 0 n written
  · dump_pre_spatial
    exact hspec

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_proof_manual
