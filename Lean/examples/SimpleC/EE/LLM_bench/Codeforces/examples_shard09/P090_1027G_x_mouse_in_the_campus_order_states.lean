import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_foundations

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infixr:80 " ^ᶻ " => Z.pow
local infix:50 " ∣ᶻ " => Z.divide

theorem order_ex_no_prime_below_two (remainder : Int) : NoPrimeBelow 2 remainder := by
  intro p hp hl
  have := hp.1
  omega

theorem order_ex_no_prime_below_divisor (candidate remainder remainder' : Int) :
    NoPrimeBelow candidate remainder → (remainder' ∣ᶻ remainder) → NoPrimeBelow candidate remainder' := by
  intro hn hd p hp hl hm
  exact hn p hp hl ((Int.dvd_iff_fmod_eq_zero).mp
    (dvd_trans ((Int.dvd_iff_fmod_eq_zero).mpr hm) ((Z.divide_iff_dvd _ _).mp hd)))

theorem order_ex_no_prime_below_advance (candidate remainder : Int) :
    NoPrimeBelow candidate remainder → remainder mod candidate ≠ 0 → NoPrimeBelow (candidate+1) remainder := by
  intro hn hc p hp hl
  by_cases hlt : p < candidate
  · exact hn p hp hlt
  · have he : p = candidate := by omega
    simpa [he] using hc

theorem order_ex_core_excess_divides_ord (x modulus phi ord excess p : Int) :
    OrderCore x modulus phi ord excess → (p ∣ᶻ excess) → (p ∣ᶻ ord) := by
  rintro ⟨_, _, _, _, _, he, _⟩ ⟨k, hk⟩
  exact ⟨Ord x modulus * k, by rw [he, hk]; ring⟩

theorem order_ex_core_reduce (x modulus phi ord excess active ord' : Int) :
    OrderPowerLaw x modulus → OrderCore x modulus phi ord excess → IsPrime active →
    ord = active * ord' → Z.pow x ord' mod modulus = 1 →
    ∃ excess', excess = active * excess' ∧ OrderCore x modulus phi ord' excess' := by
  rintro hl ⟨hi, hop, hob, hod, hep, he, hpow⟩ ha ho hpow'
  have hap := ha.1
  have hop' : 0 < ord' := by nlinarith
  have hOp := hi.2.2.2.2.1
  obtain ⟨e', he'⟩ := (hl ord' (by omega)).mp hpow'
  have hep' : 0 < e' := by nlinarith
  have hex : excess = active*e' := by nlinarith
  have hd : ord' ∣ phi := dvd_trans ⟨active, by nlinarith⟩ ((Z.divide_iff_dvd _ _).mp hod)
  have hphi := hi.2.2.2.1.1
  exact ⟨e', hex, hi, hop', Int.le_of_dvd hphi hd, (Z.divide_iff_dvd _ _).mpr hd, hep', by nlinarith, hpow'⟩

theorem order_ex_core_irreducible_from_ord (x modulus phi ord excess active : Int) :
    OrderCore x modulus phi ord excess → ¬(active ∣ᶻ ord) → ¬(active ∣ᶻ excess) := by
  intro hc hn hd
  exact hn (order_ex_core_excess_divides_ord x modulus phi ord excess active hc hd)

theorem order_ex_core_irreducible_from_pow_failure (x modulus phi ord excess active quotient : Int) :
    OrderPowerLaw x modulus → OrderCore x modulus phi ord excess → IsPrime active →
    ord = active*quotient → Z.pow x quotient mod modulus ≠ 1 → ¬(active ∣ᶻ excess) := by
  rintro hl ⟨hi, hop, hob, hod, hep, he, hpow⟩ ha ho hfail ⟨k, hk⟩
  have hap := ha.1
  have hOp := hi.2.2.2.2.1
  have hq : quotient = Ord x modulus*k := by nlinarith
  apply hfail
  exact (hl quotient (by nlinarith)).mpr ⟨k, by nlinarith⟩

theorem order_trial_init_ex (x modulus phi : Int) :
    OrderInput x modulus phi → OrderTrialStateEx x modulus phi 2 phi phi := by
  intro hi
  have hpb := hi.2.2.2.1
  have hop := hi.2.2.2.2.1
  obtain ⟨e, he⟩ := hi.2.2.2.2.2.1
  have hep : 0 < e := by nlinarith
  refine ⟨hi, hpb.1, le_refl _, ⟨1, by ring⟩, order_ex_no_prime_below_two phi, e, ?_, ?_⟩
  · exact ⟨hi, hpb.1, le_refl _, ⟨1, by ring⟩, hep, by nlinarith, hi.2.2.2.2.2.2⟩
  · rintro p hp ⟨k, hk⟩
    exact ⟨Ord x modulus*k, by rw [he, hk]; ring⟩

theorem order_trial_skip_ex (x modulus phi candidate remainder ord : Int) :
    OrderTrialStateEx x modulus phi candidate remainder ord → remainder mod candidate ≠ 0 →
    OrderTrialStateEx x modulus phi (candidate+1) remainder ord := by
  rintro ⟨hi, hp, hb, hd, hn, he⟩ hm
  exact ⟨hi, hp, hb, hd, order_ex_no_prime_below_advance candidate remainder hn hm, he⟩

theorem order_trial_enter_factor_ex (x modulus phi candidate remainder ord : Int) :
    2 ≤ candidate → OrderTrialStateEx x modulus phi candidate remainder ord → remainder mod candidate = 0 →
    OrderFactorStateEx x modulus phi candidate remainder ord := by
  rintro hc ⟨hi, hp, hb, hd, hn, e, he, hs⟩ hm
  refine ⟨hi, order_ex_smallest_remaining_prime candidate remainder hc hp hn hm, hp, hb, hd, hn, e, he, ?_⟩
  intro p hprime hdiv
  exact Or.inr (hs p hprime hdiv)

theorem order_factor_step_ex (x modulus phi active remainder remainder' ord : Int) :
    OrderFactorStateEx x modulus phi active remainder ord → remainder = active*remainder' →
    OrderFactorStateEx x modulus phi active remainder' ord := by
  rintro ⟨hi, ha, hrp, hrb, hrd, hn, e, he, hs⟩ hr
  have hap := ha.1
  have hrp' : 0 < remainder' := by nlinarith
  have hdd : remainder' ∣ᶻ remainder := ⟨active, hr⟩
  have hd : remainder' ∣ᶻ phi := (Z.divide_iff_dvd _ _).mpr
    (dvd_trans ((Z.divide_iff_dvd _ _).mp hdd) ((Z.divide_iff_dvd _ _).mp hrd))
  have hphi := hi.2.2.2.1.1
  refine ⟨hi, ha, hrp', Int.le_of_dvd hphi ((Z.divide_iff_dvd _ _).mp hd), hd,
    order_ex_no_prime_below_divisor active remainder remainder' hn hdd, e, he, ?_⟩
  intro p hp hpd
  rcases hs p hp hpd with h | h
  · exact Or.inl h
  · rw [hr] at h
    rcases order_ex_prime_divisor_product p active remainder' hp h with hpa | hpr
    · exact Or.inl (order_ex_prime_divisor_of_prime p active hp ha hpa)
    · exact Or.inr hpr

theorem order_factor_completed_ex (x modulus phi active remainder ord : Int) :
    OrderFactorStateEx x modulus phi active remainder ord → remainder mod active ≠ 0 →
    OrderStripStateEx x modulus phi active remainder ord := fun hs hm => ⟨hs, hm⟩

theorem order_strip_step_ex (x modulus phi active remainder ord ord' : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord = active*ord' →
    Z.pow x ord' mod modulus = 1 → OrderStripStateEx x modulus phi active remainder ord' := by
  rintro ⟨⟨hi, ha, hrp, hrb, hrd, hn, e, he, hs⟩, hm⟩ ho hp
  obtain ⟨e', hex, he'⟩ := order_ex_core_reduce x modulus phi ord e active ord'
    (order_input_power_law x modulus phi hi) he ha ho hp
  refine ⟨⟨hi, ha, hrp, hrb, hrd, hn, e', he', ?_⟩, hm⟩
  rintro p hprime ⟨k, hk⟩
  exact hs p hprime ⟨active*k, by rw [hex, hk]; ring⟩

theorem order_strip_exit_nodiv_ex (x modulus phi active remainder ord : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ¬(active ∣ᶻ ord) →
    OrderTrialStateEx x modulus phi (active+1) remainder ord := by
  rintro ⟨⟨hi, ha, hrp, hrb, hrd, hn, e, he, hs⟩, hm⟩ ho
  have hex := order_ex_core_irreducible_from_ord x modulus phi ord e active he ho
  refine ⟨hi, hrp, hrb, hrd, order_ex_no_prime_below_advance active remainder hn hm, e, he, ?_⟩
  intro p hp hd
  rcases hs p hp hd with h | h
  · exact False.elim (hex (h ▸ hd))
  · exact h

theorem order_strip_exit_pow_failure_ex (x modulus phi active remainder ord quotient : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord = active*quotient →
    Z.pow x quotient mod modulus ≠ 1 → OrderTrialStateEx x modulus phi (active+1) remainder ord := by
  rintro ⟨⟨hi, ha, hrp, hrb, hrd, hn, e, he, hs⟩, hm⟩ ho hf
  have hex := order_ex_core_irreducible_from_pow_failure x modulus phi ord e active quotient
    (order_input_power_law x modulus phi hi) he ha ho hf
  refine ⟨hi, hrp, hrb, hrd, order_ex_no_prime_below_advance active remainder hn hm, e, he, ?_⟩
  intro p hp hd
  rcases hs p hp hd with h | h
  · exact False.elim (hex (h ▸ hd))
  · exact h

theorem order_ex_core_unit_result (x modulus phi ord : Int) :
    OrderCore x modulus phi ord 1 → OrderResult x modulus ord := by
  rintro ⟨hi, hop, hob, hod, hep, he, hp⟩
  refine ⟨by simpa using he, hop, ?_, hp⟩
  rw [← hi.2.1]
  exact hod

theorem order_ex_support_empty_is_unit (excess : Int) :
    0 < excess → PrimeSupport excess 1 → excess = 1 := by
  intro he hs
  by_contra hne
  obtain ⟨p, hp, hd⟩ := order_ex_prime_factor_exists excess (by omega)
  have hpd := hs p hp hd
  have hle := Int.le_of_dvd (by decide : (0:Int)<1) ((Z.divide_iff_dvd _ _).mp hpd)
  have := hp.1
  omega

theorem order_trial_exit_exhausted_ex (x modulus phi candidate ord : Int) :
    OrderTrialStateEx x modulus phi candidate 1 ord → OrderResult x modulus ord := by
  rintro ⟨hi, hp, hb, hd, hn, e, he, hs⟩
  have hex := order_ex_support_empty_is_unit e he.2.2.2.2.1 hs
  subst e
  exact order_ex_core_unit_result x modulus phi ord he

theorem order_trial_enter_final_ex (x modulus phi candidate remainder ord : Int) :
    2 ≤ candidate → 1 < remainder → candidate*candidate > remainder →
    OrderTrialStateEx x modulus phi candidate remainder ord → OrderFinalStateEx x modulus phi remainder ord := by
  rintro hc hr hg ⟨hi, hrp, hrb, hrd, hn, e, he, hs⟩
  have hp := order_ex_residual_remainder_prime candidate remainder hc hr hg hn
  refine ⟨hi, hp, e, he, ?_⟩
  intro p hprime hd
  exact order_ex_prime_divisor_of_prime p remainder hprime hp (hs p hprime hd)

theorem order_final_step_ex (x modulus phi active ord ord' : Int) :
    OrderFinalStateEx x modulus phi active ord → ord = active*ord' →
    Z.pow x ord' mod modulus = 1 → OrderFinalStateEx x modulus phi active ord' := by
  rintro ⟨hi, ha, e, he, hs⟩ ho hp
  obtain ⟨e', hex, he'⟩ := order_ex_core_reduce x modulus phi ord e active ord'
    (order_input_power_law x modulus phi hi) he ha ho hp
  refine ⟨hi, ha, e', he', ?_⟩
  rintro p hprime ⟨k, hk⟩
  exact hs p hprime ⟨active*k, by rw [hex, hk]; ring⟩

theorem order_ex_support_only_irreducible_is_unit (excess active : Int) :
    0 < excess → (∀ p, IsPrime p → (p ∣ᶻ excess) → p = active) → ¬(active ∣ᶻ excess) → excess = 1 := by
  intro he hs hn
  by_contra hne
  obtain ⟨p, hp, hd⟩ := order_ex_prime_factor_exists excess (by omega)
  exact hn ((hs p hp hd) ▸ hd)

theorem order_final_exit_nodiv_ex (x modulus phi active ord : Int) :
    OrderFinalStateEx x modulus phi active ord → ¬(active ∣ᶻ ord) → OrderResult x modulus ord := by
  rintro ⟨hi, ha, e, he, hs⟩ hn
  have hne := order_ex_core_irreducible_from_ord x modulus phi ord e active he hn
  have hex := order_ex_support_only_irreducible_is_unit e active he.2.2.2.2.1 hs hne
  subst e
  exact order_ex_core_unit_result x modulus phi ord he

theorem order_final_exit_pow_failure_ex (x modulus phi active ord quotient : Int) :
    OrderFinalStateEx x modulus phi active ord → ord = active*quotient →
    Z.pow x quotient mod modulus ≠ 1 → OrderResult x modulus ord := by
  rintro ⟨hi, ha, e, he, hs⟩ ho hf
  have hne := order_ex_core_irreducible_from_pow_failure x modulus phi ord e active quotient
    (order_input_power_law x modulus phi hi) he ha ho hf
  have hex := order_ex_support_only_irreducible_is_unit e active he.2.2.2.2.1 hs hne
  subst e
  exact order_ex_core_unit_result x modulus phi ord he

theorem coq_div_factor (a b : Int) (h : a mod b = 0) : a = b * (a /ᶻ b) := by
  have hd := Int.fmod_add_mul_fdiv a b
  change a.fmod b = 0 at h
  change a = b*a.fdiv b
  omega

theorem order_factor_step_div_ex (x modulus phi active remainder ord : Int) :
    OrderFactorStateEx x modulus phi active remainder ord → remainder mod active = 0 →
    OrderFactorStateEx x modulus phi active (remainder /ᶻ active) ord := by
  intro hs hm
  exact order_factor_step_ex x modulus phi active remainder _ ord hs (coq_div_factor remainder active hm)

theorem order_strip_step_div_ex (x modulus phi active remainder ord : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord mod active = 0 →
    Z.pow x (ord /ᶻ active) mod modulus = 1 → OrderStripStateEx x modulus phi active remainder (ord /ᶻ active) := by
  intro hs hm hp
  exact order_strip_step_ex x modulus phi active remainder ord _ hs (coq_div_factor ord active hm) hp

theorem order_strip_exit_mod_ex (x modulus phi active remainder ord : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord mod active ≠ 0 →
    OrderTrialStateEx x modulus phi (active+1) remainder ord := by
  intro hs hm
  apply order_strip_exit_nodiv_ex x modulus phi active remainder ord hs
  intro hd
  exact hm ((Int.dvd_iff_fmod_eq_zero).mp ((Z.divide_iff_dvd _ _).mp hd))

theorem order_strip_exit_power_ex (x modulus phi active remainder ord retval : Int) :
    OrderStripStateEx x modulus phi active remainder ord → ord mod active = 0 →
    retval = Z.pow x (ord /ᶻ active) mod modulus → retval ≠ 1 →
    OrderTrialStateEx x modulus phi (active+1) remainder ord := by
  intro hs hm hv hf
  exact order_strip_exit_pow_failure_ex x modulus phi active remainder ord _ hs
    (coq_div_factor ord active hm) (by simpa [← hv] using hf)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
