import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_order_consumer
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_factor_machine_bounds
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
namespace P090_WalkConsumer

theorem valid_table_exponent_positive (m : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → 1 ≤ Znth i pe 0 := by
  intro h hi
  exact (h.2.2.2.1 i hi).2

theorem valid_table_initial_prefix_choice (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → PrefixChoice pr pe x 0 1 1 1 := by
  intro h
  refine ⟨h.1,⟨le_refl _,Zlength_nonneg _⟩,prefix_selected_zero,by omega,by omega,by omega,?_,?_,?_⟩
  · rfl
  · simp [Ord]
  · simp [Z.gcd]

theorem prefix_choice_zero_extend (m : Int) (pr pe : List Int) (x i d phi ord : Int) :
    ValidFactorTable m pr pe → PrefixChoice pr pe x i d phi ord → i < Zlength pr →
    PrefixChoice pr pe x (i+1) d phi ord := by
  intro hv h hi
  obtain ⟨hl,hindex,hselected,hd,hphi,hord,hpv,hov,hg⟩ := h
  have he := valid_table_exponent_positive m pr pe i hv ⟨hindex.1,hi⟩
  have hs := prefix_selected_step_product pr pe i d 0 hselected ⟨hindex.1,hi⟩ ⟨by omega,by omega⟩
  have hselected' : PrefixSelected pr pe (i+1) d := by simpa [Z.pow] using hs
  exact ⟨hl,by omega,hselected',hd,hphi,hord,hpv,hov,hg⟩

theorem walk_suffix_at_terminal (pr pe : List Int) (x i d : Int) :
    Zlength pr = Zlength pe → i = Zlength pr → WalkSuffix pr pe x i d = CycleTerm x d := by
  intro hl hi
  subst i
  have hlen : pr.length = pe.length := by simpa [Zlength] using hl
  simp [WalkSuffix,Zlength,hlen,walk_suffix_lists]

theorem prefix_choice_leaf_cycle_term (pr pe : List Int) (x i d phi ord : Int) :
    PrefixChoice pr pe x i d phi ord → d ≠ 1 → CycleTerm x d = phi /ᶻ ord := by
  rintro ⟨hl,hi,hs,hd,hp,ho,hpv,hov,hg⟩ hn
  have hfalse : (d == 1) = false := by simp [hn]
  unfold CycleTerm
  dsimp only
  rw [hfalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ord_reduced_base x d (by omega),← hpv,← hov]

theorem prefix_choice_terminal_walk_value (pr pe : List Int) (x i d phi ord : Int) :
    PrefixChoice pr pe x i d phi ord → i = Zlength pr → d ≠ 1 → WalkSuffix pr pe x i d = phi /ᶻ ord := by
  intro h hi hd
  rw [walk_suffix_at_terminal pr pe x i d h.1 hi]
  exact prefix_choice_leaf_cycle_term pr pe x i d phi ord h hd

theorem skipn_nth_cons_nat {A : Type} (values : List A) (index : Nat) (default : A) :
    index < values.length → values.drop index = values.getD index default :: values.drop (Nat.succ index) := by
  induction index generalizing values with
  | zero => cases values <;> simp
  | succ index ih =>
    cases values with
    | nil => simp
    | cons v vs => simpa using ih vs

theorem skipn_Znth_cons {A : Type} (values : List A) (index : Int) (default : A) :
    (0 ≤ index ∧ index < Zlength values) →
    values.drop index.toNat = Znth index values default :: values.drop (index+1).toNat := by
  intro hi
  have hn : index.toNat < values.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hsucc : Nat.succ index.toNat = (index+1).toNat := by omega
  simpa only [Znth,hsucc] using skipn_nth_cons_nat values index.toNat default hn

theorem walk_suffix_as_exp_suffix_zero (m : Int) (pr pe : List Int) (x i d : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) →
    WalkSuffix pr pe x i d = WalkExpSuffix pr pe x i 0 d := by
  intro hv hi
  have hipe : 0 ≤ i ∧ i < Zlength pe := by rw [← hv.1]; exact hi
  have he := valid_table_exponent_positive m pr pe i hv hi
  unfold WalkSuffix WalkExpSuffix
  rw [skipn_Znth_cons pr i 0 hi,skipn_Znth_cons pe i 0 hipe]
  simp only [walk_suffix_lists,sub_zero]
  have hn : (Znth i pe 0+1).toNat = Nat.succ (Znth i pe 0).toNat := by omega
  rw [hn]
  rfl

theorem walk_suffix_head_zero (m : Int) (pr pe : List Int) (x i d : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) →
    WalkSuffix pr pe x i d = WalkSuffix pr pe x (i+1) d + WalkExpSuffix pr pe x i 1 d := by
  intro hv hi
  have he := valid_table_exponent_positive m pr pe i hv hi
  rw [walk_suffix_as_exp_suffix_zero m pr pe x i d hv hi]
  simpa [Z.pow] using walk_exp_suffix_head_tail pr pe x i 0 d ⟨by omega,by omega⟩

theorem walk_pending_after_zero (m : Int) (pr pe : List Int) (x i d before current : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) →
    WalkBudget m before (WalkSuffix pr pe x i d) → current = before+WalkSuffix pr pe x (i+1) d →
    WalkPendingState pr pe m x i d before current 1 := by
  intro hv hi hb hc
  have hs := walk_suffix_head_zero m pr pe x i d hv hi
  have hh := walk_suffix_nonnegative pr pe x (i+1) d
  have ht := walk_exp_suffix_nonnegative pr pe x i 1 d (fun e => walk_suffix_nonnegative _ _ _ _ _)
  unfold WalkBudget at hb
  unfold WalkPendingState WalkLoopState WalkBudget
  omega

theorem walk_pending_consume_head (pr pe : List Int) (m x i d before current next_e current' : Int) :
    (0 ≤ next_e ∧ next_e ≤ Znth i pe 0) → WalkPendingState pr pe m x i d before current next_e →
    current' = current+WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) next_e) →
    WalkPendingState pr pe m x i d before current' (next_e+1) := by
  intro he h hc
  have hs := walk_exp_suffix_head_tail pr pe x i next_e d he
  have hh := walk_suffix_nonnegative pr pe x (i+1) (d*Z.pow (Znth i pr 0) next_e)
  have ht := walk_exp_suffix_nonnegative pr pe x i (next_e+1) d (fun e => walk_suffix_nonnegative _ _ _ _ _)
  unfold WalkPendingState WalkLoopState WalkBudget at *
  omega

theorem walk_pending_finish (pr pe : List Int) (m x i d before current : Int) :
    WalkPendingState pr pe m x i d before current (Znth i pe 0+1) →
    current = before+WalkSuffix pr pe x i d ∧ (0 ≤ current ∧ current ≤ m) := by
  intro h
  unfold WalkPendingState WalkLoopState WalkBudget at h
  rw [walk_exp_suffix_exact_exhaustion] at h
  omega

theorem walk_recursive_return_continuation (pr pe : List Int) (m x i d before current exponent returned : Int) :
    (0 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkPendingState pr pe m x i d before current exponent →
    returned = current+WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) exponent) →
    WalkPendingState pr pe m x i d before returned (exponent+1) :=
  walk_pending_consume_head pr pe m x i d before current exponent returned
end P090_WalkConsumer
export P090_WalkConsumer (valid_table_exponent_positive valid_table_initial_prefix_choice prefix_choice_zero_extend
  walk_suffix_at_terminal prefix_choice_leaf_cycle_term prefix_choice_terminal_walk_value skipn_nth_cons_nat skipn_Znth_cons
  walk_suffix_as_exp_suffix_zero walk_suffix_head_zero walk_pending_after_zero walk_pending_consume_head walk_pending_finish
  walk_recursive_return_continuation)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
