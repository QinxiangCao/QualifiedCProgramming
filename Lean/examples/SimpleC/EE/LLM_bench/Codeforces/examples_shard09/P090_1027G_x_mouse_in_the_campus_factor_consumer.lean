import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_divisor_completeness
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_FactorConsumer

theorem strict_trial_init (m : Int) : 0 < m → StrictTrialState m 2 m [] [] := strict_factor_prefix_base m

theorem strict_trial_skip (m candidate remainder : Int) (pr pe : List Int) :
    StrictTrialState m candidate remainder pr pe → remainder mod candidate ≠ 0 →
    StrictTrialState m (candidate+1) remainder pr pe := by
  rintro ⟨⟨hl,hcap,hc,hr,hp,he,hn⟩,ho⟩ hmod
  refine ⟨⟨hl,hcap,by omega,hr,hp,?_,?_⟩,ho⟩
  · intro k hk
    obtain ⟨hp,he,hb⟩ := he k hk
    exact ⟨hp,he,by omega⟩
  · intro p hp hbelow
    by_cases hlt : p < candidate
    · exact hn p hp hlt
    · have : p = candidate := by omega
      simpa [this] using hmod

theorem strict_trial_enter_factor (m candidate remainder : Int) (pr pe : List Int) :
    2 ≤ candidate → StrictTrialState m candidate remainder pr pe → remainder mod candidate = 0 →
    StrictFactorAtPrime m candidate remainder remainder 0 pr pe := by
  intro hc h hm
  have hp := order_ex_smallest_remaining_prime candidate remainder hc h.1.2.2.2.1.1 h.1.2.2.2.2.2.2 hm
  exact ⟨h,hp,hm,by omega,by simp [Z.pow],⟨h.1.2.2.2.1.1,le_refl _⟩⟩

theorem strict_factor_at_prime_forgets_order (m candidate original remainder exponent : Int) (pr pe : List Int) :
    StrictFactorAtPrime m candidate original remainder exponent pr pe →
    FactorAtPrime m candidate original remainder exponent pr pe := by
  rintro ⟨h,hp,hm,he,hprod,hb⟩
  exact ⟨h.1,hp,hm,he,hprod,hb⟩

theorem strict_factor_divide_step (m candidate original remainder remainder' exponent : Int) (pr pe : List Int) :
    StrictFactorAtPrime m candidate original remainder exponent pr pe → remainder = candidate*remainder' →
    StrictFactorAtPrime m candidate original remainder' (exponent+1) pr pe := by
  rintro ⟨hs,hp,hm,he,hprod,hb⟩ hd
  have hc := hp.1
  have hr : 0 < remainder' := by nlinarith
  refine ⟨hs,hp,hm,by omega,?_,⟨hr,by nlinarith⟩⟩
  rw [hprod, hd, coq_pow_add candidate exponent 1 he (by omega)]
  simp only [show Z.pow candidate 1 = candidate by simp [Z.pow]]
  ring

theorem strict_factor_positive_exponent_at_exit (m candidate original remainder exponent : Int) (pr pe : List Int) :
    StrictFactorAtPrime m candidate original remainder exponent pr pe → remainder mod candidate ≠ 0 →
    1 ≤ exponent := by
  intro h hn
  exact factor_at_prime_exit_positive m candidate original remainder exponent pr pe
    (strict_factor_at_prime_forgets_order m candidate original remainder exponent pr pe h) hn

theorem strict_factor_finish_prime (m candidate original remainder exponent : Int) (pr pe : List Int) :
    StrictFactorAtPrime m candidate original remainder exponent pr pe → remainder mod candidate ≠ 0 → Zlength pr < 64 →
    StrictTrialState m (candidate+1) remainder (pr++[candidate]) (pe++[exponent]) := by
  intro h hn hc
  exact strict_factor_prefix_append_completed_prime m candidate original remainder exponent pr pe h.1 h.2.1
    (strict_factor_positive_exponent_at_exit m candidate original remainder exponent pr pe h hn)
    h.2.2.2.2.1 h.2.2.2.2.2.1 hn hc

theorem strict_trial_finalize_after_square_exit (m candidate remainder : Int) (pr pe : List Int) :
    StrictTrialState m candidate remainder pr pe → m ≤ 100000000000000 → candidate*candidate > remainder →
    ∃ final_pr final_pe, ValidFactorTable m final_pr final_pe ∧
      ((remainder = 1 ∧ final_pr = pr ∧ final_pe = pe) ∨
       (1 < remainder ∧ final_pr = pr++[remainder] ∧ final_pe = pe++[1])) :=
  strict_factor_prefix_finalize_after_square_exit m candidate remainder pr pe

theorem strict_trial_finalize_from_failed_guard (m candidate remainder : Int) (pr pe : List Int) :
    StrictTrialState m candidate remainder pr pe → m ≤ 100000000000000 → ¬candidate*candidate ≤ remainder →
    ∃ final_pr final_pe, ValidFactorTable m final_pr final_pe := by
  intro h hm hg
  obtain ⟨pr',pe',hv,_⟩ := strict_trial_finalize_after_square_exit m candidate remainder pr pe h hm (by omega)
  exact ⟨pr',pe',hv⟩
end P090_FactorConsumer
export P090_FactorConsumer (strict_trial_init strict_trial_skip strict_trial_enter_factor
  strict_factor_at_prime_forgets_order strict_factor_divide_step strict_factor_positive_exponent_at_exit
  strict_factor_finish_prime strict_trial_finalize_after_square_exit strict_trial_finalize_from_failed_guard)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
