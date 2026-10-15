import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_consumer
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib
namespace P090_WalkCallBudget

theorem walk_budget_split_head_tail (m current head tail : Int) :
    0 ≤ head → 0 ≤ tail → WalkBudget m current (head+tail) →
    WalkBudget m current head ∧ WalkBudget m (current+head) tail := by
  unfold WalkBudget
  omega

theorem incoming_walk_suffix_zero_head_tail_budget (m : Int) (pr pe : List Int) (x i d before : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → WalkBudget m before (WalkSuffix pr pe x i d) →
    WalkSuffix pr pe x i d = WalkSuffix pr pe x (i+1) d+WalkExpSuffix pr pe x i 1 d ∧
    WalkBudget m before (WalkSuffix pr pe x (i+1) d) ∧
    WalkBudget m (before+WalkSuffix pr pe x (i+1) d) (WalkExpSuffix pr pe x i 1 d) := by
  intro hv hi hw
  have hs := walk_suffix_head_zero m pr pe x i d hv hi
  refine ⟨hs,walk_budget_split_head_tail _ _ _ _ (walk_suffix_nonnegative _ _ _ _ _)
    (walk_exp_suffix_nonnegative _ _ _ _ _ _ (fun _ => walk_suffix_nonnegative _ _ _ _ _)) ?_⟩
  rwa [← hs]

theorem incoming_walk_suffix_zero_call_budget (m : Int) (pr pe : List Int) (x i d before : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → WalkBudget m before (WalkSuffix pr pe x i d) →
    WalkBudget m before (WalkSuffix pr pe x (i+1) d) := by
  intro hv hi hw
  exact (incoming_walk_suffix_zero_head_tail_budget m pr pe x i d before hv hi hw).2.1

theorem incoming_walk_suffix_zero_return_continuation (m : Int) (pr pe : List Int) (x i d before returned : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → WalkBudget m before (WalkSuffix pr pe x i d) →
    returned = before+WalkSuffix pr pe x (i+1) d → WalkPendingState pr pe m x i d before returned 1 :=
  walk_pending_after_zero m pr pe x i d before returned

theorem incoming_walk_suffix_zero_call_and_continuation (m : Int) (pr pe : List Int) (x i d before : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → WalkBudget m before (WalkSuffix pr pe x i d) →
    WalkBudget m before (WalkSuffix pr pe x (i+1) d) ∧
      ∀ returned, returned = before+WalkSuffix pr pe x (i+1) d → WalkPendingState pr pe m x i d before returned 1 := by
  intro hv hi hw
  exact ⟨incoming_walk_suffix_zero_call_budget m pr pe x i d before hv hi hw,
    fun returned => incoming_walk_suffix_zero_return_continuation m pr pe x i d before returned hv hi hw⟩

theorem walk_pending_head_tail_budget (pr pe : List Int) (m x i d before current exponent : Int) :
    (0 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkPendingState pr pe m x i d before current exponent →
    WalkExpSuffix pr pe x i exponent d = WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent)+
      WalkExpSuffix pr pe x i (exponent+1) d ∧
    WalkBudget m current (WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent)) ∧
    WalkBudget m (current+WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent))
      (WalkExpSuffix pr pe x i (exponent+1) d) := by
  intro he h
  have hs := walk_exp_suffix_head_tail pr pe x i exponent d he
  refine ⟨hs,walk_budget_split_head_tail _ _ _ _ (walk_suffix_nonnegative _ _ _ _ _)
    (walk_exp_suffix_nonnegative _ _ _ _ _ _ (fun _ => walk_suffix_nonnegative _ _ _ _ _)) ?_⟩
  rw [← hs]
  exact h.2

theorem walk_pending_recursive_call_budget (pr pe : List Int) (m x i d before current exponent : Int) :
    (0 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkPendingState pr pe m x i d before current exponent →
    WalkBudget m current (WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent)) := by
  intro he h
  exact (walk_pending_head_tail_budget pr pe m x i d before current exponent he h).2.1

theorem walk_pending_post_return_tail_budget (pr pe : List Int) (m x i d before current exponent returned : Int) :
    (0 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkPendingState pr pe m x i d before current exponent →
    returned = current+WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent) →
    WalkBudget m returned (WalkExpSuffix pr pe x i (exponent+1) d) := by
  intro he h hr
  subst returned
  exact (walk_pending_head_tail_budget pr pe m x i d before current exponent he h).2.2

theorem walk_pending_recursive_call_and_return (pr pe : List Int) (m x i d before current exponent : Int) :
    (0 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkPendingState pr pe m x i d before current exponent →
    WalkBudget m current (WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent)) ∧
    ∀ returned, returned = current+WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent) →
      WalkPendingState pr pe m x i d before returned (exponent+1) := by
  intro he h
  exact ⟨walk_pending_recursive_call_budget pr pe m x i d before current exponent he h,
    fun returned => walk_recursive_return_continuation pr pe m x i d before current exponent returned he h⟩
end P090_WalkCallBudget
export P090_WalkCallBudget (walk_budget_split_head_tail incoming_walk_suffix_zero_head_tail_budget
  incoming_walk_suffix_zero_call_budget incoming_walk_suffix_zero_return_continuation incoming_walk_suffix_zero_call_and_continuation
  walk_pending_head_tail_budget walk_pending_recursive_call_budget walk_pending_post_return_tail_budget walk_pending_recursive_call_and_return)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
