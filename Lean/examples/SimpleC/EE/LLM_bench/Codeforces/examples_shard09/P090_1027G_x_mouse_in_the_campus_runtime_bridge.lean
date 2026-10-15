import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_final_orbit_instantiation
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

theorem order_trial_exit_bounded_ex (x modulus phi candidate remainder ord : Int) :
    OrderTrialStateEx x modulus phi candidate remainder ord → 0 < remainder → remainder ≤ 1 → OrderResult x modulus ord := by
  intro h hp hu
  have he : remainder = 1 := by omega
  rw [he] at h
  exact order_trial_exit_exhausted_ex x modulus phi candidate ord h

theorem order_final_step_div_ex (x modulus phi active ord : Int) :
    OrderFinalStateEx x modulus phi active ord → ord mod active = 0 → Z.pow x (ord /ᶻ active) mod modulus = 1 →
    OrderFinalStateEx x modulus phi active (ord /ᶻ active) := by
  intro h hm hp
  exact order_final_step_ex x modulus phi active ord (ord /ᶻ active) h (coq_div_factor ord active hm) hp

theorem order_final_exit_mod_ex (x modulus phi active ord : Int) :
    OrderFinalStateEx x modulus phi active ord → ord mod active ≠ 0 → OrderResult x modulus ord := by
  intro h hm
  exact order_final_exit_nodiv_ex x modulus phi active ord h (fun hd => hm (Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).mp hd)))

theorem order_final_exit_power_guard_ex (x modulus phi active ord retval : Int) :
    OrderFinalStateEx x modulus phi active ord → ord mod active = 0 → retval = Z.pow x (ord /ᶻ active) mod modulus →
    retval ≠ 1 → OrderResult x modulus ord := by
  intro h hm hr hn
  exact order_final_exit_pow_failure_ex x modulus phi active ord (ord /ᶻ active) h (coq_div_factor ord active hm) (by omega)

theorem pow_mod_base__powmod_loop (x m n : Int) : m ≠ 0 → 0 ≤ n → Z.pow (x mod m) n mod m = Z.pow x n mod m :=
  order_ex_pow_mod_base x m n

theorem land_one_mod_two__powmod_loop (e : Int) : Z.land e 1 = e mod 2 := Z.land_ones e 1 (by omega)

private theorem shiftr_one_div_two (e : Int) : Z.shiftr e 1 = e /ᶻ 2 := by
  change e >>> 1 = e.fdiv 2
  rw [Int.shiftRight_eq_div_pow]
  simpa using (Int.fdiv_eq_ediv_of_nonneg e (by omega : (0:Int) ≤ 2)).symm

theorem pow_loop_odd_step__powmod_loop (original_base original_exponent m b e r : Int) :
    0 < m → 0 ≤ e → Z.land e 1 ≠ 0 → PowLoopState original_base original_exponent m b e r →
    PowLoopState original_base original_exponent m ((b*b) mod m) (Z.shiftr e 1) ((r*b) mod m) := by
  intro hm he ho hp
  rw [land_one_mod_two__powmod_loop] at ho
  have hnonneg := Int.fmod_nonneg_of_pos e (by omega : (0:Int) < 2)
  have hlt := Int.fmod_lt_of_pos e (by omega : (0:Int) < 2)
  have hodd : e mod 2 = 1 := by change e.fmod 2 ≠ 0 at ho; change e.fmod 2 = 1; omega
  rw [shiftr_one_div_two]
  exact SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.modular_power_progress_odd_step__loop_transitions
    original_base original_exponent m b e r hm he hodd hp

theorem pow_loop_even_step__powmod_loop (original_base original_exponent m b e r : Int) :
    0 < m → 0 ≤ e → Z.land e 1 = 0 → PowLoopState original_base original_exponent m b e r →
    PowLoopState original_base original_exponent m ((b*b) mod m) (Z.shiftr e 1) r := by
  intro hm he ho hp
  rw [land_one_mod_two__powmod_loop] at ho
  rw [shiftr_one_div_two]
  exact SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.modular_power_progress_even_step__loop_transitions
    original_base original_exponent m b e r hm he ho hp

private theorem tmod_nonpos_local (a b : Int) (ha : a ≤ 0) : a.tmod b ≤ 0 := by
  have hn := Int.tmod_nonneg b (by omega : 0 ≤ -a)
  rw [Int.neg_tmod] at hn
  omega

theorem rem_one_implies_mod_one__order_entry_and_factorization (a modulus : Int) :
    0 < modulus → Z.rem a modulus = 1 → a mod modulus = 1 := by
  intro hm hr
  have ha : 0 ≤ a := by
    by_contra hn
    have hh := tmod_nonpos_local a modulus (by omega)
    change a.tmod modulus = 1 at hr
    omega
  change a.fmod modulus = 1
  rw [Int.fmod_eq_tmod_of_nonneg ha (by omega)]
  exact hr

theorem rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits (a b : Int) :
    0 < b → 0 ≤ Z.rem a b → Z.rem a b = a mod b := by
  intro hb hr
  by_cases ha : 0 ≤ a
  · exact (Int.fmod_eq_tmod_of_nonneg ha (by omega)).symm
  · have hh := tmod_nonpos_local a b (by omega)
    have hz : a.tmod b = 0 := by change 0 ≤ a.tmod b at hr; omega
    have hmod := Int.fmod_eq_zero_of_dvd (Int.dvd_of_tmod_eq_zero hz)
    exact hz.trans hmod.symm
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
