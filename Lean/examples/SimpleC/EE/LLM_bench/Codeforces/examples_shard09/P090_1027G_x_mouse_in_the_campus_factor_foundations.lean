import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_factor_table

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

theorem coq_pow_mono (a e f : Int) (ha : 1 ≤ a) (he : 0 ≤ e) (hef : e ≤ f) :
    Z.pow a e ≤ Z.pow a f := by
  rw [coq_pow_nat a e he, coq_pow_nat a f (by omega)]
  exact pow_le_pow_right₀ ha (by omega)

namespace P090_FactorFoundations

theorem factor_entries_of_strict_prefix (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → FactorEntriesAtLeastTwo pr pe := by
  intro h k hk
  have he := h.1.2.2.2.2.2.1 k hk
  have hp := he.1.1
  exact ⟨by omega, he.2.1⟩

theorem factor_product_lower_bound (pr pe : List Int) :
    Zlength pr = Zlength pe → FactorEntriesAtLeastTwo pr pe →
    Z.pow 2 (Zlength pr) ≤ factor_product pr pe := by
  induction pr generalizing pe with
  | nil =>
    intro hl he
    cases pe with
    | nil => decide
    | cons e pe => simp [Zlength] at hl; omega
  | cons p pr ih =>
    intro hl he
    cases pe with
    | nil => simp [Zlength] at hl; omega
    | cons e pe =>
      have hhead : 2 ≤ p ∧ 1 ≤ e := he 0 (by simp [Zlength])
      have htail : FactorEntriesAtLeastTwo pr pe := by
        intro k hk
        have hk' : 0 ≤ k+1 ∧ k+1 < Zlength (p::pr) := by rw [Zlength_cons]; omega
        have hh := he (k+1) hk'
        rw [Znth_cons 0 (k+1) p pr (by omega), Znth_cons 0 (k+1) e pe (by omega)] at hh
        simpa using hh
      have hlen : Zlength pr = Zlength pe := by rw [Zlength_cons, Zlength_cons] at hl; omega
      have hih := ih pe hlen htail
      have hpowhead : 2 ≤ Z.pow p e := by
        have hm := coq_pow_mono p 1 e (by omega) (by omega) hhead.2
        have hp1 : Z.pow p 1 = p := by simp [Z.pow]
        rw [hp1] at hm
        omega
      have hp : 0 < Z.pow 2 (Zlength pr) := coq_pow_pos 2 _ (by omega) (Zlength_nonneg pr)
      rw [Zlength_cons, coq_pow_add 2 (Zlength pr) 1 (Zlength_nonneg pr) (by omega)]
      change Z.pow 2 (Zlength pr) * 2 ≤ Z.pow p e * factor_product pr pe
      nlinarith

theorem strict_factor_prefix_product_lower_bound (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → Z.pow 2 (Zlength pr) ≤ factor_product pr pe := by
  intro h
  exact factor_product_lower_bound pr pe h.1.1 (factor_entries_of_strict_prefix m candidate remainder pr pe h)

theorem strict_factor_prefix_power_bounded_by_m (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → Z.pow 2 (Zlength pr) ≤ m := by
  intro h
  have hlo := strict_factor_prefix_product_lower_bound m candidate remainder pr pe h
  have hrem := h.1.2.2.2.1
  have heq := h.1.2.2.2.2.1
  have hp := coq_pow_pos 2 (Zlength pr) (by omega) (Zlength_nonneg pr)
  nlinarith

theorem strict_factor_prefix_length_lt_47 (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → m ≤ 100000000000000 → Zlength pr < 47 := by
  intro h hm
  have hb := strict_factor_prefix_power_bounded_by_m m candidate remainder pr pe h
  by_contra hn
  have hmono := coq_pow_mono 2 47 (Zlength pr) (by omega) (by omega) (by omega)
  have hnumeral : 100000000000000 < Z.pow 2 47 := by decide
  omega

theorem strict_factor_prefix_has_free_slot (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → m ≤ 100000000000000 → Zlength pr < 64 := by
  intro h hm
  have := strict_factor_prefix_length_lt_47 m candidate remainder pr pe h hm
  omega

theorem standard_prime_is_case_prime (p : Int) : prime p → IsPrime p := (order_ex_is_prime_iff_std p).mpr

theorem standard_prime_divisor_exists (n : Int) : 1 < n → ∃ p, prime p ∧ Z.divide p n := order_ex_std_prime_factor_exists n

theorem case_prime_divisor_exists (n : Int) : 1 < n → ∃ p, IsPrime p ∧ Z.divide p n := order_ex_prime_factor_exists n

theorem no_small_prime_divisor_implies_prime (frontier remainder : Int) :
    2 ≤ frontier → 1 < remainder → remainder < frontier*frontier →
    (∀ p, IsPrime p → p < frontier → remainder mod p ≠ 0) → IsPrime remainder :=
  order_ex_residual_remainder_prime frontier remainder

theorem strict_factor_prefix_residual_prime (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → 1 < remainder → candidate*candidate > remainder → IsPrime remainder := by
  intro h hr hs
  exact no_small_prime_divisor_implies_prime candidate remainder h.1.2.2.1 hr hs h.1.2.2.2.2.2.2

theorem strict_factor_prefix_finalize_after_square_exit (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → m ≤ 100000000000000 → candidate*candidate > remainder →
    ∃ final_pr final_pe, ValidFactorTable m final_pr final_pe ∧
      ((remainder=1 ∧ final_pr=pr ∧ final_pe=pe) ∨
       (1<remainder ∧ final_pr=pr++[remainder] ∧ final_pe=pe++[1])) := by
  intro h hm hs
  have hr := h.1.2.2.2.1
  by_cases he : remainder=1
  · subst remainder
    exact ⟨pr, pe, strict_factor_prefix_finalize_one m candidate pr pe h, Or.inl ⟨rfl,rfl,rfl⟩⟩
  · have hp := strict_factor_prefix_residual_prime m candidate remainder pr pe h (by omega) hs
    have hc := strict_factor_prefix_has_free_slot m candidate remainder pr pe h hm
    exact ⟨pr++[remainder], pe++[1], strict_factor_prefix_finalize_prime_residual m candidate remainder pr pe h hp hc,
      Or.inr ⟨by omega,rfl,rfl⟩⟩

end P090_FactorFoundations
export P090_FactorFoundations (factor_entries_of_strict_prefix factor_product_lower_bound strict_factor_prefix_product_lower_bound strict_factor_prefix_power_bounded_by_m strict_factor_prefix_length_lt_47 strict_factor_prefix_has_free_slot standard_prime_is_case_prime standard_prime_divisor_exists case_prime_divisor_exists no_small_prime_divisor_implies_prime strict_factor_prefix_residual_prime strict_factor_prefix_finalize_after_square_exit)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
