import SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_goal
import SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_proof_auto

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open majority_element_goal majority_element_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Coq's proof-local `grab H pat` copies a hypothesis matching the given type.
scoped syntax (name := grab) "grab " ident term : tactic
macro_rules
  | `(tactic| grab $id:ident $pat:term) => `(tactic| have $id : $pat := by assumption)

-- The spatial branch retains the array-length invariant used by the Coq proof.
theorem proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1 := by
  unfold majorityElement_entail_wit_1
  left
  intro n p l x hmajor hlo hhi hlen
  Exists x ([] : List Int) l
  grab hmajorCopy (IsMajorityElement x l)
  have hm := majority_on_reduced_init x 0 l hmajorCopy
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | simp [Zlength]

theorem proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1 := by
  unfold majorityElement_entail_wit_2_1
  left
  intro n p l candidate x vote i l1 l2 hv hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlt : i < Zlength (l1 ++ l2) := by rw [← hl, hlen]; exact hi
  obtain ⟨a, rest, hl2, hz⟩ := app_Znth_suffix_cons l1 l2 i 0 hlen1 hlt
  have hzl : Znth i l 0 = a := by rw [hl]; exact hz
  have hred : MajorityOnReduced x (Znth i l 0) (vote + 1) rest := by
    rw [hzl, hv]
    apply majority_on_reduced_reset x candidate a rest
    simpa only [hl2, hv] using hreduced.2
  Exists x (l1 ++ [a]) rest
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp [hl, hl2, List.append_assoc])
      | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2 := by
  unfold majorityElement_entail_wit_2_2
  left
  intro n p l candidate x vote i l1 l2 heq hv hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlt : i < Zlength (l1 ++ l2) := by rw [← hl, hlen]; exact hi
  obtain ⟨a, rest, hl2, hz⟩ := app_Znth_suffix_cons l1 l2 i 0 hlen1 hlt
  have hac : a = candidate := by rw [hl, hz] at heq; exact heq
  have hred : MajorityOnReduced x candidate (vote + 1) rest := by
    apply majority_on_reduced_same x candidate vote rest hv0
    simpa only [hl2, hac] using hreduced.2
  Exists x (l1 ++ [a]) rest
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp [hl, hl2, List.append_assoc])
      | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3 := by
  unfold majorityElement_entail_wit_2_3
  left
  intro n p l candidate x vote i l1 l2 hne hv hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlt : i < Zlength (l1 ++ l2) := by rw [← hl, hlen]; exact hi
  obtain ⟨a, rest, hl2, hz⟩ := app_Znth_suffix_cons l1 l2 i 0 hlen1 hlt
  have hac : a ≠ candidate := by rw [hl, hz] at hne; exact hne
  have hred : MajorityOnReduced x candidate (vote + (-1)) rest := by
    apply majority_on_reduced_cancel x candidate a vote rest (by omega) hac
    simpa only [hl2] using hreduced.2
  Exists x (l1 ++ [a]) rest
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | (solve | simp [hl, hl2, List.append_assoc])
      | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1 := by
  unfold majorityElement_return_wit_1
  left
  intro n p l candidate x vote i l1 l2 hi hl hlen1 hi0 hin hn0 hnmax hv0 hvi hmajor hreduced
  prop_apply naive_C_Rules.IntArray.full_Zlength
  Intros_p hlen
  have hlen2 : Zlength l2 = 0 := by
    rw [hl, Zlength_app] at hlen
    omega
  have hl2 : l2 = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [Zlength, Int.ofNat_eq_coe] at hlen2
    omega
  have hxc : x = candidate := by
    apply majority_of_repeated_eq x candidate vote hv0
    simpa only [hl2, List.append_nil] using hreduced.2
  have hresult : IsMajorityElement candidate l := by rw [← hxc]; exact hmajor
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hresult

end SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_proof_manual
