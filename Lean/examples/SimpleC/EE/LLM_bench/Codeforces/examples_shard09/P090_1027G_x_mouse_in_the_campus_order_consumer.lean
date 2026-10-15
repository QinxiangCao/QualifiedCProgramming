import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_order_input_bridge
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_OrderConsumer

theorem order_trial_init_from_coprime (x modulus : Int) :
    1 < modulus → Z.gcd x modulus = 1 →
    OrderTrialStateEx x modulus (EulerPhi modulus) 2 (EulerPhi modulus) (EulerPhi modulus) := by
  intro hm hg
  exact order_trial_init_ex x modulus (EulerPhi modulus) (coprime_implies_order_input x modulus hm hg)

theorem order_power_law_from_trial (x modulus phi candidate remainder ord : Int) :
    OrderTrialStateEx x modulus phi candidate remainder ord → OrderPowerLaw x modulus := by
  intro h
  exact order_input_power_law x modulus phi h.1

theorem order_power_law_from_factor (x modulus phi active remainder ord : Int) :
    OrderFactorStateEx x modulus phi active remainder ord → OrderPowerLaw x modulus := by
  intro h
  exact order_input_power_law x modulus phi h.1

theorem order_power_law_from_strip (x modulus phi active remainder ord : Int) :
    OrderStripStateEx x modulus phi active remainder ord → OrderPowerLaw x modulus := by
  intro h
  exact order_input_power_law x modulus phi h.1.1

theorem order_power_law_from_final (x modulus phi active ord : Int) :
    OrderFinalStateEx x modulus phi active ord → OrderPowerLaw x modulus := by
  intro h
  exact order_input_power_law x modulus phi h.1

theorem order_trial_enter_factor_closed (x modulus phi candidate remainder ord : Int) :
    2 ≤ candidate → OrderTrialStateEx x modulus phi candidate remainder ord → remainder mod candidate = 0 →
    OrderFactorStateEx x modulus phi candidate remainder ord :=
  order_trial_enter_factor_ex x modulus phi candidate remainder ord

theorem order_factor_step_closed (x modulus phi active remainder remainder' ord : Int) :
    OrderFactorStateEx x modulus phi active remainder ord → remainder = active*remainder' →
    OrderFactorStateEx x modulus phi active remainder' ord :=
  order_factor_step_ex x modulus phi active remainder remainder' ord

theorem order_strip_step_closed (x modulus phi active remainder ord ord' : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord = active*ord' →
    Z.pow x ord' mod modulus = 1 → OrderStripStateEx x modulus phi active remainder ord' :=
  order_strip_step_ex x modulus phi active remainder ord ord'

theorem order_strip_exit_pow_failure_closed (x modulus phi active remainder ord quotient : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord = active*quotient →
    Z.pow x quotient mod modulus ≠ 1 → OrderTrialStateEx x modulus phi (active+1) remainder ord :=
  order_strip_exit_pow_failure_ex x modulus phi active remainder ord quotient

theorem order_trial_exit_exhausted_closed (x modulus phi candidate ord : Int) :
    OrderTrialStateEx x modulus phi candidate 1 ord → OrderResult x modulus ord :=
  order_trial_exit_exhausted_ex x modulus phi candidate ord

theorem order_trial_enter_final_closed (x modulus phi candidate remainder ord : Int) :
    2 ≤ candidate → 1 < remainder → candidate*candidate > remainder →
    OrderTrialStateEx x modulus phi candidate remainder ord → OrderFinalStateEx x modulus phi remainder ord :=
  order_trial_enter_final_ex x modulus phi candidate remainder ord

theorem order_final_step_closed (x modulus phi active ord ord' : Int) :
    OrderFinalStateEx x modulus phi active ord → ord = active*ord' →
    Z.pow x ord' mod modulus = 1 → OrderFinalStateEx x modulus phi active ord' :=
  order_final_step_ex x modulus phi active ord ord'

theorem order_final_exit_nodiv_closed (x modulus phi active ord : Int) :
    OrderFinalStateEx x modulus phi active ord → ¬(active ∣ᶻ ord) → OrderResult x modulus ord :=
  order_final_exit_nodiv_ex x modulus phi active ord

theorem order_final_exit_pow_failure_closed (x modulus phi active ord quotient : Int) :
    OrderFinalStateEx x modulus phi active ord → ord = active*quotient →
    Z.pow x quotient mod modulus ≠ 1 → OrderResult x modulus ord :=
  order_final_exit_pow_failure_ex x modulus phi active ord quotient

end P090_OrderConsumer
export P090_OrderConsumer (order_trial_init_from_coprime order_power_law_from_trial order_power_law_from_factor order_power_law_from_strip order_power_law_from_final order_trial_enter_factor_closed order_factor_step_closed order_strip_step_closed order_strip_exit_pow_failure_closed order_trial_exit_exhausted_closed order_trial_enter_final_closed order_final_step_closed order_final_exit_nodiv_closed order_final_exit_pow_failure_closed)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
