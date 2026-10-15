import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_divisor_enumeration

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

theorem coq_prime_gcd_one (p d : Int) (hp : prime p) (hn : ¬(p ∣ᶻ d)) : Z.gcd d p=1 := by
  have hp2 := prime_ge_2 p hp
  have hgpos := Int.gcd_pos_of_ne_zero_right d (by omega : p≠0)
  have hgdiv := (Z.divide_iff_dvd _ _).mpr (Int.gcd_dvd_right d p)
  have hgleft := Int.gcd_dvd_left d p
  rcases prime_divisors p hp (Int.gcd d p) hgdiv with h | h | h | h
  · omega
  · exact h
  · exact False.elim (hn ((Z.divide_iff_dvd _ _).mpr (h ▸ hgleft)))
  · omega

theorem coq_gcd_one_not_divide (p d : Int) (hp : 1<p) (hg : Z.gcd d p=1) : ¬(p ∣ᶻ d) := by
  intro hd
  have hgn : Int.gcd d p=1 := by simpa [Z.gcd] using hg
  have hle := Int.le_of_dvd (by omega : (0:Int)<1)
    (Int.gcd_eq_one_iff.mp hgn p ((Z.divide_iff_dvd _ _).mp hd) (dvd_refl p))
  omega

theorem coq_pow_divides_pow (p e f : Int) (he : 0≤e) (hef : e≤f) : Z.pow p e ∣ᶻ Z.pow p f := by
  refine ⟨Z.pow p (f-e),?_⟩
  calc
    Z.pow p f = Z.pow p e*Z.pow p (f-e) := by
      rw [← coq_pow_add p e (f-e) he (by omega)]
      congr 1 <;> omega
    _ = _ := mul_comm _ _

namespace P090_DivisorCompleteness

theorem smaller_prime_not_divide_factor_product (p : Int) (pr pe : List Int) :
    prime p → Zlength pr=Zlength pe →
    (∀ k, (0≤k ∧ k<Zlength pr) → prime (Znth k pr 0) ∧ 1≤Znth k pe 0 ∧ p<Znth k pr 0) →
    ¬(p ∣ᶻ factor_product pr pe) := by
  intro hp
  have hp2 := prime_ge_2 p hp
  induction pr generalizing pe with
  | nil =>
    intro hl he hd
    cases pe with
    | nil =>
      have hle := Int.le_of_dvd (by decide : (0:Int)<1) ((Z.divide_iff_dvd _ _).mp hd)
      omega
    | cons e pe => simp [Zlength] at hl; omega
  | cons q pr ih =>
    intro hl he hd
    cases pe with
    | nil => simp [Zlength] at hl; omega
    | cons e pe =>
      have hhead : prime q ∧ 1≤e ∧ p<q := he 0 (by simp [Zlength])
      have hqp : Z.gcd p q=1 := smaller_distinct_primes_coprime p q
        ((order_ex_is_prime_iff_std p).mpr hp) ((order_ex_is_prime_iff_std q).mpr hhead.1) hhead.2.2
      have hpqpow : Z.gcd (Z.pow q e) p=1 := by
        have hg : Int.gcd q p=1 := by simpa [Z.gcd,Int.gcd_comm] using hqp
        rw [coq_pow_nat q e (by omega)]
        have h := Int.gcd_pow_left_of_gcd_eq_one (k:=e.toNat) hg
        simpa [Z.gcd] using congrArg Int.ofNat h
      rcases prime_mult p hp (Z.pow q e) (factor_product pr pe) hd with hpow | htail
      · exact coq_gcd_one_not_divide p (Z.pow q e) (by omega) hpqpow hpow
      · apply ih pe (by rw [Zlength_cons,Zlength_cons] at hl; omega) ?_ htail
        intro k hk
        have hh := he (k+1) (by rw [Zlength_cons]; omega)
        rw [Znth_cons 0 (k+1) q pr (by omega),Znth_cons 0 (k+1) e pe (by omega)] at hh
        simpa using hh

private theorem ordered_table_coprime_product (d : Int) (pr pe : List Int) :
    OrderedPrimeTable pr pe → CoprimeToTable d pr → Z.gcd d (factor_product pr pe)=1 := by
  intro ht
  induction ht with
  | ordered_prime_table_nil => intro hc; simp [factor_product,Z.gcd]
  | ordered_prime_table_cons p e pr pe hp he hl ht ih =>
    intro hc
    cases hc with
    | cons hg hct =>
      have hgpow := gcd_prime_power_one d p e (by omega) hg
      have htail := ih hct
      have hgn : Int.gcd d (Z.pow p e)=1 := by simpa [Z.gcd] using hgpow
      have htn : Int.gcd d (factor_product pr pe)=1 := by simpa [Z.gcd] using htail
      change Int.ofNat (Int.gcd d (Z.pow p e*factor_product pr pe))=1
      rw [Int.gcd_mul_right_right_of_gcd_eq_one hgn,htn]
      rfl

theorem valid_factor_table_canonical (m : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → CanonicalFactorTable pr pe := by
  intro hv
  have ht := valid_factor_table_ordered m pr pe hv
  clear hv
  induction ht with
  | ordered_prime_table_nil => exact .canonical_factor_table_nil
  | ordered_prime_table_cons p e pr pe hp he hl ht ih =>
    refine .canonical_factor_table_cons p pr e pe ((order_ex_is_prime_iff_std p).mp hp) he ih ?_
    have hc : CoprimeToTable p pr := by
      apply Forall.iff_forall_mem.mpr
      intro q hq
      exact smaller_distinct_primes_coprime p q hp ((ordered_prime_table_all_primes pr pe ht).mem hq) (hl.mem hq)
    have hg := ordered_table_coprime_product p pr pe ht hc
    apply coq_gcd_one_not_divide p (factor_product pr pe) hp.1
    simpa [Z.gcd,Int.gcd_comm] using hg

theorem extract_prime_power_from_divisor (p maximum rest divisor : Int) :
    prime p → 0≤maximum → 0<rest → ¬(p ∣ᶻ rest) → 0<divisor → (divisor ∣ᶻ Z.pow p maximum*rest) →
    ∃ exponent residual, (0≤exponent ∧ exponent≤maximum) ∧ 0<residual ∧ ¬(p ∣ᶻ residual) ∧
      (residual ∣ᶻ rest) ∧ divisor=Z.pow p exponent*residual := by
  intro hp hm hr hpr
  have hp2 := prime_ge_2 p hp
  have haux : ∀ n : Nat, ∀ divisor : Int, 0<divisor → (divisor ∣ᶻ p^n*rest) →
      ∃ exponent residual, (0≤exponent ∧ exponent≤(n:Int)) ∧ 0<residual ∧ ¬(p ∣ᶻ residual) ∧
        (residual ∣ᶻ rest) ∧ divisor=Z.pow p exponent*residual := by
    intro n
    induction n with
    | zero =>
      intro divisor hd hdiv
      have hdr : divisor ∣ᶻ rest := by simpa using hdiv
      refine ⟨0,divisor,⟨le_refl _,le_refl _⟩,hd,?_,hdr,?_⟩
      · intro hpd
        exact hpr ((Z.divide_iff_dvd _ _).mpr (dvd_trans ((Z.divide_iff_dvd _ _).mp hpd) ((Z.divide_iff_dvd _ _).mp hdr)))
      · simp [Z.pow]
    | succ n ih =>
      intro divisor hd hdiv
      have hdiv' : divisor ∣ p*(p^n*rest) := by
        have h := (Z.divide_iff_dvd _ _).mp hdiv
        convert h using 1 <;> ring
      by_cases hpd : p ∣ᶻ divisor
      · obtain ⟨q,hq⟩ := (Z.divide_iff_dvd _ _).mp hpd
        have hqpos : 0<q := by nlinarith
        obtain ⟨k,hk⟩ := hdiv'
        have hqd : q ∣ p^n*rest := by
          refine ⟨k,?_⟩
          apply mul_left_cancel₀ (by omega : p≠0)
          calc
            p*(p^n*rest)=divisor*k := hk
            _ = p*(q*k) := by rw [hq]; ring
        obtain ⟨e,r,he,hrp,hpn,hdr,hfactor⟩ := ih q hqpos ((Z.divide_iff_dvd _ _).mpr hqd)
        refine ⟨e+1,r,⟨by omega,by omega⟩,hrp,hpn,hdr,?_⟩
        rw [hq,hfactor,coq_pow_add p e 1 he.1 (by omega)]
        have hp1 : Z.pow p 1=p := by simp [Z.pow]
        rw [hp1]
        ring
      · have hg := coq_prime_gcd_one p divisor hp hpd
        have hgn : Int.gcd divisor p=1 := by simpa [Z.gcd] using hg
        have hlow : divisor ∣ p^n*rest := by
          have h := (Int.dvd_gcd_mul_iff_dvd_mul).mpr hdiv'
          simpa [hgn] using h
        obtain ⟨e,r,he,hrp,hpn,hdr,hfactor⟩ := ih divisor hd ((Z.divide_iff_dvd _ _).mpr hlow)
        exact ⟨e,r,⟨he.1,by omega⟩,hrp,hpn,hdr,hfactor⟩
  intro hd hdiv
  rw [coq_pow_nat p maximum hm] at hdiv
  obtain ⟨e,r,he,hrp,hpn,hdr,hfactor⟩ := haux maximum.toNat divisor hd hdiv
  exact ⟨e,r,⟨he.1,by omega⟩,hrp,hpn,hdr,hfactor⟩

theorem canonical_factor_product_positive (pr pe : List Int) : CanonicalFactorTable pr pe → 0<factor_product pr pe := by
  intro ht
  induction ht with
  | canonical_factor_table_nil => decide
  | canonical_factor_table_cons p pr e pe hp he ht hn ih =>
    exact mul_pos (coq_pow_pos p e (by have := prime_ge_2 p hp; omega) (by omega)) ih

theorem canonical_divisor_complete (pr pe : List Int) (divisor : Int) :
    CanonicalFactorTable pr pe → 0<divisor → (divisor ∣ᶻ factor_product pr pe) →
    ∃ exponents, ExponentTrace pr pe exponents divisor := by
  intro ht
  induction ht generalizing divisor with
  | canonical_factor_table_nil =>
    intro hp hd
    have hle := Int.le_of_dvd (by decide : (0:Int)<1) ((Z.divide_iff_dvd _ _).mp hd)
    have he : divisor=1 := by omega
    subst divisor
    exact ⟨[],.exponent_trace_nil⟩
  | canonical_factor_table_cons p pr e pe hp he ht hn ih =>
    intro hd hdiv
    obtain ⟨chosen,residual,hch,hrp,hpn,hrd,hfactor⟩ := extract_prime_power_from_divisor p e (factor_product pr pe) divisor
      hp (by omega) (canonical_factor_product_positive pr pe ht) hn hd hdiv
    obtain ⟨ex,htrace⟩ := ih residual hrp hrd
    rw [hfactor]
    exact ⟨chosen::ex,.exponent_trace_cons p pr e pe chosen ex residual hch htrace⟩

theorem valid_factor_table_divisor_complete (m : Int) (pr pe : List Int) (divisor : Int) :
    ValidFactorTable m pr pe → 0<divisor → (divisor ∣ᶻ m) → ∃ exponents, ExponentTrace pr pe exponents divisor := by
  intro ht hp hd
  exact canonical_divisor_complete pr pe divisor (valid_factor_table_canonical m pr pe ht) hp (by rw [← ht.2.2.1]; exact hd)

end P090_DivisorCompleteness
export P090_DivisorCompleteness (smaller_prime_not_divide_factor_product valid_factor_table_canonical extract_prime_power_from_divisor canonical_factor_product_positive canonical_divisor_complete valid_factor_table_divisor_complete)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
