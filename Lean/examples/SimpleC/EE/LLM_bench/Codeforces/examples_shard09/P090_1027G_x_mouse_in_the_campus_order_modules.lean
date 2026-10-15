import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_order_states

set_option linter.unusedVariables false
set_option linter.dupNamespace false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infixr:80 " ^ᶻ " => Z.pow
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_OrderExcess.P090_OrderExcess

theorem prime_positive (p : Int) : IsPrime p → 1 < p := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_prime_positive p

theorem no_prime_below_two (remainder : Int) : NoPrimeBelow 2 remainder := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_two remainder

theorem no_prime_below_divisor (candidate remainder remainder' : Int) :
    NoPrimeBelow candidate remainder → (remainder' ∣ᶻ remainder) → NoPrimeBelow candidate remainder' := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_divisor candidate remainder remainder'

theorem no_prime_below_advance (candidate remainder : Int) :
    NoPrimeBelow candidate remainder → remainder mod candidate ≠ 0 → NoPrimeBelow (candidate+1) remainder := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_no_prime_below_advance candidate remainder

theorem order_core_excess_divides_ord (x modulus phi ord excess p : Int) :
    OrderCore x modulus phi ord excess → (p ∣ᶻ excess) → (p ∣ᶻ ord) := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_excess_divides_ord x modulus phi ord excess p

theorem order_core_reduce (x modulus phi ord excess active ord' : Int) :
    OrderPowerLaw x modulus → OrderCore x modulus phi ord excess → IsPrime active →
    ord = active * ord' → Z.pow x ord' mod modulus = 1 →
    ∃ excess', excess = active * excess' ∧ OrderCore x modulus phi ord' excess' := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_reduce x modulus phi ord excess active ord'

theorem order_core_excess_irreducible_from_ord (x modulus phi ord excess active : Int) :
    OrderCore x modulus phi ord excess → ¬(active ∣ᶻ ord) → ¬(active ∣ᶻ excess) := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_irreducible_from_ord x modulus phi ord excess active

theorem order_core_excess_irreducible_from_pow_failure (x modulus phi ord excess active quotient : Int) :
    OrderPowerLaw x modulus → OrderCore x modulus phi ord excess → IsPrime active →
    ord = active*quotient → Z.pow x quotient mod modulus ≠ 1 → ¬(active ∣ᶻ excess) := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_irreducible_from_pow_failure x modulus phi ord excess active quotient

theorem order_trial_init (x modulus phi : Int) :
    OrderInput x modulus phi → OrderTrialStateEx x modulus phi 2 phi phi := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_init_ex x modulus phi

theorem order_trial_skip (x modulus phi candidate remainder ord : Int) :
    OrderTrialStateEx x modulus phi candidate remainder ord → remainder mod candidate ≠ 0 →
    OrderTrialStateEx x modulus phi (candidate+1) remainder ord := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_skip_ex x modulus phi candidate remainder ord

theorem order_trial_enter_factor (x modulus phi candidate remainder ord : Int) :
    SmallestRemainingDivisorPrimeLaw →
    2 ≤ candidate → OrderTrialStateEx x modulus phi candidate remainder ord → remainder mod candidate = 0 →
    OrderFactorStateEx x modulus phi candidate remainder ord := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_enter_factor_ex x modulus phi candidate remainder ord

theorem order_factor_step (x modulus phi active remainder remainder' ord : Int) :
    PrimeDivisorProductLaw → PrimeDivisorOfPrimeLaw →
    OrderFactorStateEx x modulus phi active remainder ord → remainder = active*remainder' →
    OrderFactorStateEx x modulus phi active remainder' ord := by
  intro _ _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_factor_step_ex x modulus phi active remainder remainder' ord

theorem order_factor_completed (x modulus phi active remainder ord : Int) :
    OrderFactorStateEx x modulus phi active remainder ord → remainder mod active ≠ 0 →
    OrderStripStateEx x modulus phi active remainder ord := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_factor_completed_ex x modulus phi active remainder ord

theorem order_strip_step (x modulus phi active remainder ord ord' : Int) :
    OrderPowerLaw x modulus →
    OrderStripStateEx x modulus phi active remainder ord → ord = active*ord' →
    Z.pow x ord' mod modulus = 1 → OrderStripStateEx x modulus phi active remainder ord' := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_step_ex x modulus phi active remainder ord ord'

theorem order_strip_exit_nodiv (x modulus phi active remainder ord : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ¬(active ∣ᶻ ord) →
    OrderTrialStateEx x modulus phi (active+1) remainder ord := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_exit_nodiv_ex x modulus phi active remainder ord

theorem order_strip_exit_pow_failure (x modulus phi active remainder ord quotient : Int) :
    OrderPowerLaw x modulus →
    OrderStripStateEx x modulus phi active remainder ord → ord = active*quotient →
    Z.pow x quotient mod modulus ≠ 1 → OrderTrialStateEx x modulus phi (active+1) remainder ord := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_strip_exit_pow_failure_ex x modulus phi active remainder ord quotient

theorem order_core_unit_result (x modulus phi ord : Int) :
    OrderCore x modulus phi ord 1 → OrderResult x modulus ord := by
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_core_unit_result x modulus phi ord

theorem support_empty_is_unit (excess : Int) :
    PrimeFactorExistsLaw →
    0 < excess → PrimeSupport excess 1 → excess = 1 := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_support_empty_is_unit excess

theorem order_trial_exit_exhausted (x modulus phi candidate ord : Int) :
    PrimeFactorExistsLaw →
    OrderTrialStateEx x modulus phi candidate 1 ord → OrderResult x modulus ord := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_exit_exhausted_ex x modulus phi candidate ord

theorem order_trial_enter_final (x modulus phi candidate remainder ord : Int) :
    ResidualRemainderPrimeLaw → PrimeDivisorOfPrimeLaw →
    2 ≤ candidate → 1 < remainder → candidate*candidate > remainder →
    OrderTrialStateEx x modulus phi candidate remainder ord → OrderFinalStateEx x modulus phi remainder ord := by
  intro _ _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_trial_enter_final_ex x modulus phi candidate remainder ord

theorem order_final_step (x modulus phi active ord ord' : Int) :
    OrderPowerLaw x modulus →
    OrderFinalStateEx x modulus phi active ord → ord = active*ord' →
    Z.pow x ord' mod modulus = 1 → OrderFinalStateEx x modulus phi active ord' := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_step_ex x modulus phi active ord ord'

theorem support_only_irreducible_is_unit (excess active : Int) :
    PrimeFactorExistsLaw →
    0 < excess → (∀ p, IsPrime p → (p ∣ᶻ excess) → p = active) → ¬(active ∣ᶻ excess) → excess = 1 := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_support_only_irreducible_is_unit excess active

theorem order_final_exit_nodiv (x modulus phi active ord : Int) :
    PrimeFactorExistsLaw →
    OrderFinalStateEx x modulus phi active ord → ¬(active ∣ᶻ ord) → OrderResult x modulus ord := by
  intro _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_exit_nodiv_ex x modulus phi active ord

theorem order_final_exit_pow_failure (x modulus phi active ord quotient : Int) :
    PrimeFactorExistsLaw → OrderPowerLaw x modulus →
    OrderFinalStateEx x modulus phi active ord → ord = active*quotient →
    Z.pow x quotient mod modulus ≠ 1 → OrderResult x modulus ord := by
  intro _ _
  exact SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_final_exit_pow_failure_ex x modulus phi active ord quotient

theorem order_core_order_divides (x modulus phi ord excess : Int) :
    OrderCore x modulus phi ord excess → (Ord x modulus ∣ᶻ ord) := by
  intro h
  exact ⟨excess, by have := h.2.2.2.2.2.1; nlinarith⟩
end P090_OrderExcess.P090_OrderExcess

namespace P090_OrderFoundations.P090_OrderFoundations
open P090_OrderExcess.P090_OrderExcess

theorem order_power_law_0_2_counterexample :
    Z.pow 0 1 mod 2 ≠ 1 ∧ (Ord 0 2 ∣ᶻ 1) := by
  refine ⟨by decide, 1, ?_⟩
  decide

theorem order_power_law_falsified : ¬OrderPowerLaw 0 2 := by
  intro h
  exact order_power_law_0_2_counterexample.1 ((h 1 (by omega)).mpr order_power_law_0_2_counterexample.2)

theorem is_prime_iff_std (p : Int) : IsPrime p ↔ prime p := order_ex_is_prime_iff_std p

theorem std_prime_factor_exists : ∀ n, 1 < n → ∃ p, prime p ∧ (p ∣ᶻ n) := order_ex_std_prime_factor_exists

theorem prime_factor_exists_law : PrimeFactorExistsLaw := order_ex_prime_factor_exists

theorem prime_divisor_product_law : PrimeDivisorProductLaw := order_ex_prime_divisor_product

theorem prime_divisor_of_prime_law : PrimeDivisorOfPrimeLaw := order_ex_prime_divisor_of_prime

theorem no_prime_below_not_divides (candidate remainder p : Int) :
    NoPrimeBelow candidate remainder → IsPrime p → p < candidate → ¬(p ∣ᶻ remainder) :=
  order_ex_no_prime_below_not_divides candidate remainder p

theorem smallest_remaining_divisor_prime_law : SmallestRemainingDivisorPrimeLaw := order_ex_smallest_remaining_prime

theorem residual_remainder_prime_law : ResidualRemainderPrimeLaw := order_ex_residual_remainder_prime

end P090_OrderFoundations.P090_OrderFoundations

namespace P090_OrderExact.P090_OrderExact
open P090_OrderExcess.P090_OrderExcess

theorem pow_mod_base_nat (a modulus : Int) (n : Nat) :
    modulus ≠ 0 → Z.pow (a mod modulus) (Int.ofNat n) mod modulus =
      Z.pow a (Int.ofNat n) mod modulus := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_mod_base_nat a modulus n

theorem pow_mod_base (a modulus exponent : Int) :
    modulus ≠ 0 → 0 ≤ exponent →
    Z.pow (a mod modulus) exponent mod modulus = Z.pow a exponent mod modulus := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_mod_base a modulus exponent

theorem pow_add_mod_left_one (a modulus left right : Int) :
    1 < modulus → 0 ≤ left → 0 ≤ right → Z.pow a left mod modulus = 1 →
    Z.pow a (left+right) mod modulus = Z.pow a right mod modulus := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_add_mod_left_one a modulus left right

theorem pow_multiple_mod_one (a modulus period multiplier : Int) :
    1 < modulus → 0 ≤ period → 0 ≤ multiplier → Z.pow a period mod modulus = 1 →
    Z.pow a (period*multiplier) mod modulus = 1 := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_multiple_mod_one a modulus period multiplier

theorem pow_divmod_remainder (a modulus period exponent : Int) :
    1 < modulus → 0 < period → 0 ≤ exponent → Z.pow a period mod modulus = 1 →
    Z.pow a exponent mod modulus = Z.pow a (exponent mod period) mod modulus := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_pow_divmod_remainder a modulus period exponent

theorem order_search_minimal (base modulus start : Int) (fuel : Nat) (candidate : Int) :
    1 ≤ start → (start ≤ candidate ∧ candidate < order_search base modulus start fuel) →
    Z.pow base candidate mod modulus ≠ 1 := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_search_minimal base modulus start fuel candidate

theorem order_search_terminal_spec (base modulus start : Int) (fuel : Nat) :
    1 ≤ start → Z.pow base (start + Int.ofNat fuel) mod modulus = 1 →
    let result := order_search base modulus start (Nat.succ fuel)
    (start ≤ result ∧ result ≤ start + Int.ofNat fuel) ∧ Z.pow base result mod modulus = 1 := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_search_terminal_spec base modulus start fuel

theorem ord_search_exact (x modulus phi : Int) :
    OrderInput x modulus phi → (1 ≤ Ord x modulus ∧ Ord x modulus ≤ phi) ∧
    Z.pow x (Ord x modulus) mod modulus = 1 ∧
    (∀ candidate, (1 ≤ candidate ∧ candidate < Ord x modulus) → Z.pow x candidate mod modulus ≠ 1) := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_ord_search_exact x modulus phi

theorem minimal_success_divides (x modulus period exponent : Int) :
    1 < modulus → 0 < period → Z.pow x period mod modulus = 1 →
    (∀ candidate, (1 ≤ candidate ∧ candidate < period) → Z.pow x candidate mod modulus ≠ 1) →
    0 ≤ exponent → Z.pow x exponent mod modulus = 1 → (period ∣ᶻ exponent) := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_minimal_success_divides x modulus period exponent

theorem success_of_period_divides (x modulus period exponent : Int) :
    1 < modulus → 0 < period → Z.pow x period mod modulus = 1 →
    0 ≤ exponent → (period ∣ᶻ exponent) → Z.pow x exponent mod modulus = 1 := SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.order_ex_success_of_period_divides x modulus period exponent

theorem order_input_implies_order_power_law :
    ∀ x modulus phi, OrderInput x modulus phi → OrderPowerLaw x modulus := order_input_power_law
end P090_OrderExact.P090_OrderExact

namespace P090_OrbitQuotient.OrderExact
export P090_OrderExact.P090_OrderExact (pow_mod_base_nat pow_mod_base pow_add_mod_left_one pow_multiple_mod_one pow_divmod_remainder order_search_minimal order_search_terminal_spec ord_search_exact minimal_success_divides success_of_period_divides order_input_implies_order_power_law)
end P090_OrbitQuotient.OrderExact
namespace P090_GcdStratumTransport.OE
export P090_OrderExact.P090_OrderExact (pow_mod_base_nat pow_mod_base pow_add_mod_left_one pow_multiple_mod_one pow_divmod_remainder order_search_minimal order_search_terminal_spec ord_search_exact minimal_success_divides success_of_period_divides order_input_implies_order_power_law)
end P090_GcdStratumTransport.OE

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
