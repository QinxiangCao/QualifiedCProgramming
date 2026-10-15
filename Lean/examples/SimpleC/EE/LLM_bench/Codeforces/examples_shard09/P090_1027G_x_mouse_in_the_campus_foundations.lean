import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_definitions

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infixr:80 " ^ᶻ " => Z.pow
local infix:50 " ∣ᶻ " => Z.divide

theorem order_input_phi (x modulus phi : Int) :
    OrderInput x modulus phi → phi = EulerPhi modulus := fun h => h.2.1

theorem order_input_positive (x modulus phi : Int) :
    OrderInput x modulus phi → 0 < phi ∧ 0 < Ord x modulus :=
  fun h => ⟨h.2.2.2.1.1, h.2.2.2.2.1⟩

theorem order_result_positive (x modulus result : Int) :
    OrderResult x modulus result → 0 < result := fun h => h.2.1

theorem order_result_divides_phi (x modulus result : Int) :
    OrderResult x modulus result → (result ∣ᶻ EulerPhi modulus) := fun h => h.2.2.1

theorem order_factor_completed (x modulus phi q t ord : Int) :
    OrderFactorState x modulus phi q t ord → t mod q ≠ 0 →
    OrderStripState x modulus phi q t ord := fun h hd => ⟨h, hd⟩

theorem order_strip_advance (x modulus phi q t ord : Int) :
    OrderStripState x modulus phi q t ord → OrderTrialState x modulus phi (q+1) t ord := by
  rintro ⟨⟨⟨hi, ht, htl, htd, ho, hol, hod, htrue, hp, hs⟩, hq⟩, hd⟩
  refine ⟨hi, ht, htl, htd, ho, hol, hod, htrue, hp, ?_⟩
  intro p hprime hlt
  by_cases hl : p < q
  · exact hs p hprime hl
  · have he : p = q := by omega
    simpa [he] using hd

theorem walk_global_coprime (m x : Int) : WalkGlobalBounds m x → Z.gcd x m = 1 := fun h => h.2.2

theorem walk_exponent_phi (m p exponent max_exponent pk ph : Int) :
    WalkExponentState m p exponent max_exponent pk ph → ph = EulerPhi pk := fun h => h.2.2.2.2.2

theorem factor_at_prime_is_prime (m p t0 t e : Int) (prs pes : List Int) :
    FactorAtPrime m p t0 t e prs pes → IsPrime p := fun h => h.2.1

theorem factor_at_prime_exit_positive (m p t0 t e : Int) (prs pes : List Int) :
    FactorAtPrime m p t0 t e prs pes → t mod p ≠ 0 → 1 ≤ e := by
  rintro ⟨_, _, hentry, he, hdecomp, _⟩ hexit
  have hne : e ≠ 0 := by
    intro heq
    subst e
    simp only [Z.pow, Int.pow_zero, Int.one_mul] at hdecomp
    exact hexit (hdecomp ▸ hentry)
  omega

theorem valid_factor_table_lengths (m : Int) (prs pes : List Int) :
    ValidFactorTable m prs pes → Zlength prs = Zlength pes := fun h => h.1

theorem prefix_choice_positive (prs pes : List Int) (x i d phi ord : Int) :
    PrefixChoice prs pes x i d phi ord → 0 < d ∧ 0 < phi ∧ 0 < ord :=
  fun h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem prefix_choice_selected (prs pes : List Int) (x i d phi ord : Int) :
    PrefixChoice prs pes x i d phi ord → PrefixSelected prs pes i d := fun h => h.2.2.1

theorem prefix_selected_extend (prs pes : List Int) (i d e : Int) :
    PrefixSelected prs pes i d → (0 ≤ i ∧ i < Zlength prs) → (0 ≤ e ∧ e ≤ Znth i pes 0) →
    PrefixSelected prs pes (i+1) (d * Z.pow (Znth i prs 0) e) :=
  PrefixSelected.prefix_selected_step i d e

theorem prime_power_transition_values (x d phi ord p e pk ph o g next_d next_phi next_ord : Int) :
    PrimePowerTransition x d phi ord p e pk ph o g next_d next_phi next_ord →
    next_d = d*pk ∧ next_phi = phi*ph ∧ next_ord = ord /ᶻ g * o := by
  rintro ⟨_, _, _, _, _, _, _, hd, hp, ho, _⟩
  exact ⟨hd, hp, ho⟩

theorem walk_exp_suffix_zero (pr pe : List Int) (x i d : Int) :
    Znth i pe 0 < 0 → WalkExpSuffix pr pe x i 0 d = 0 := by
  intro h
  unfold WalkExpSuffix
  dsimp only
  have he : (Znth i pe 0 - 0 + 1).toNat = 0 := by omega
  rw [he]
  rfl

theorem walk_exp_suffix_exhausted (pr pe : List Int) (x i d next_e : Int) :
    Znth i pe 0 < next_e → WalkExpSuffix pr pe x i next_e d = 0 := by
  intro h
  unfold WalkExpSuffix
  dsimp only
  have he : (Znth i pe 0 - next_e + 1).toNat = 0 := by omega
  rw [he]
  rfl

theorem walk_pending_terminal (pr pe : List Int) (m x i d before current next_e : Int) :
    WalkPendingState pr pe m x i d before current next_e → Znth i pe 0 < next_e →
    current = before + WalkSuffix pr pe x i d := by
  rintro ⟨hc, _⟩ he
  unfold WalkLoopState at hc
  rw [walk_exp_suffix_exhausted pr pe x i d next_e he] at hc
  omega

theorem cycle_answer_to_spec (m x total : Int) :
    CycleAnswer m x total → Spec m x (total+1) := fun h => h.2

theorem order_ex_prime_positive (p : Int) : IsPrime p → 1 < p := fun h => h.1


theorem order_ex_is_prime_iff_std (p : Int) : IsPrime p ↔ prime p := by
  rw [← prime_alt]
  unfold IsPrime prime'
  simp only [Z.divide_iff_dvd, Int.dvd_iff_fmod_eq_zero, Z.modulo]

theorem order_ex_std_prime_factor_exists (n : Int) :
    1 < n → ∃ p, prime p ∧ (p ∣ᶻ n) := by
  have haux : ∀ k : Nat, ∀ a : Int, a.toNat = k → 1 < a → ∃ p, prime p ∧ (p ∣ᶻ a) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a hak ha
      by_cases hp : prime a
      · exact ⟨a, hp, (Z.divide_iff_dvd _ _).mpr (dvd_refl a)⟩
      · obtain ⟨d, hd, hda⟩ := not_prime_divide a ha hp
        obtain ⟨p, hp, hpd⟩ := ih d.toNat (by omega) d rfl hd.1
        exact ⟨p, hp, (Z.divide_iff_dvd _ _).mpr (dvd_trans ((Z.divide_iff_dvd _ _).mp hpd) ((Z.divide_iff_dvd _ _).mp hda))⟩
  exact haux n.toNat n rfl

theorem order_ex_prime_factor_exists (n : Int) :
    1 < n → ∃ p, IsPrime p ∧ (p ∣ᶻ n) := by
  intro hn
  obtain ⟨p, hp, hd⟩ := order_ex_std_prime_factor_exists n hn
  exact ⟨p, (order_ex_is_prime_iff_std p).mpr hp, hd⟩

theorem order_ex_prime_divisor_product (p a b : Int) :
    IsPrime p → (p ∣ᶻ a * b) → (p ∣ᶻ a) ∨ (p ∣ᶻ b) := by
  intro hp hd
  exact prime_mult p ((order_ex_is_prime_iff_std p).mp hp) a b hd

theorem order_ex_prime_divisor_of_prime (p q : Int) :
    IsPrime p → IsPrime q → (p ∣ᶻ q) → p = q := by
  intro hp hq hd
  have hle := Int.le_of_dvd (by have := hq.1; omega : 0 < q) ((Z.divide_iff_dvd _ _).mp hd)
  by_contra hne
  exact hq.2 p ⟨hp.1, by omega⟩ ((Int.dvd_iff_fmod_eq_zero).mp ((Z.divide_iff_dvd _ _).mp hd))

theorem order_ex_no_prime_below_not_divides (candidate remainder p : Int) :
    NoPrimeBelow candidate remainder → IsPrime p → p < candidate → ¬(p ∣ᶻ remainder) := by
  intro hn hp hl hd
  exact hn p hp hl ((Int.dvd_iff_fmod_eq_zero).mp ((Z.divide_iff_dvd _ _).mp hd))

theorem order_ex_smallest_remaining_prime (candidate remainder : Int) :
    2 ≤ candidate → 0 < remainder → NoPrimeBelow candidate remainder →
    remainder mod candidate = 0 → IsPrime candidate := by
  intro hc hr hn hm
  refine ⟨by omega, ?_⟩
  intro q hq hqm
  have hqc : q ∣ candidate := (Int.dvd_iff_fmod_eq_zero).mpr hqm
  have hcr : candidate ∣ remainder := (Int.dvd_iff_fmod_eq_zero).mpr hm
  obtain ⟨p, hp, hpd⟩ := order_ex_prime_factor_exists q hq.1
  have hpd' := (Z.divide_iff_dvd _ _).mp hpd
  have hle := Int.le_of_dvd (by omega : 0 < q) hpd'
  exact order_ex_no_prime_below_not_divides candidate remainder p hn hp (by omega)
    ((Z.divide_iff_dvd _ _).mpr (dvd_trans hpd' (dvd_trans hqc hcr)))

theorem order_ex_residual_remainder_prime (candidate remainder : Int) :
    2 ≤ candidate → 1 < remainder → candidate * candidate > remainder →
    NoPrimeBelow candidate remainder → IsPrime remainder := by
  intro hc hr hg hn
  refine ⟨hr, ?_⟩
  intro q hq hqm
  obtain ⟨c, he⟩ := (Int.dvd_iff_fmod_eq_zero).mpr hqm
  have hcp : 1 < c := by nlinarith
  have hs : q < candidate ∨ c < candidate := by
    by_contra hh
    push_neg at hh
    nlinarith [mul_nonneg (by omega : 0 ≤ q-candidate) (by omega : 0 ≤ c-candidate)]
  rcases hs with hqs | hcs
  · obtain ⟨p, hp, hpd⟩ := order_ex_prime_factor_exists q hq.1
    have hpd' := (Z.divide_iff_dvd _ _).mp hpd
    have hle := Int.le_of_dvd (by omega : 0 < q) hpd'
    exact order_ex_no_prime_below_not_divides candidate remainder p hn hp (by omega)
      ((Z.divide_iff_dvd _ _).mpr (dvd_trans hpd' ⟨c, he⟩))
  · obtain ⟨p, hp, hpd⟩ := order_ex_prime_factor_exists c hcp
    have hpd' := (Z.divide_iff_dvd _ _).mp hpd
    have hle := Int.le_of_dvd (by omega : 0 < c) hpd'
    exact order_ex_no_prime_below_not_divides candidate remainder p hn hp (by omega)
      ((Z.divide_iff_dvd _ _).mpr (dvd_trans hpd' ⟨q, by nlinarith [he]⟩))


theorem coq_pow_nat (a e : Int) (he : 0 ≤ e) : Z.pow a e = a ^ e.toNat := by
  cases e <;> simp_all [Z.pow]

theorem coq_pow_add (a e f : Int) (he : 0 ≤ e) (hf : 0 ≤ f) :
    Z.pow a (e+f) = Z.pow a e * Z.pow a f := by
  rw [coq_pow_nat a (e+f) (by omega), coq_pow_nat a e he, coq_pow_nat a f hf]
  rw [Int.toNat_add he hf, pow_add]

theorem coq_pow_mul (a e f : Int) (he : 0 ≤ e) (hf : 0 ≤ f) :
    Z.pow a (e*f) = Z.pow (Z.pow a e) f := by
  rw [coq_pow_nat a (e*f) (mul_nonneg he hf), coq_pow_nat (Z.pow a e) f hf, coq_pow_nat a e he]
  rw [Int.toNat_mul he hf, pow_mul]

theorem coq_pow_pos (a e : Int) (ha : 0 < a) (he : 0 ≤ e) : 0 < Z.pow a e := by
  rw [coq_pow_nat a e he]
  exact pow_pos ha _

theorem order_ex_pow_mod_base_nat (a modulus : Int) (n : Nat) :
    modulus ≠ 0 → Z.pow (a mod modulus) (Int.ofNat n) mod modulus =
      Z.pow a (Int.ofNat n) mod modulus := by
  intro hm
  simp only [Z.pow, Z.modulo]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ]
    rw [Int.mul_fmod, Int.mul_fmod (a^n) a modulus, ih, Int.fmod_fmod]

theorem order_ex_pow_mod_base (a modulus exponent : Int) :
    modulus ≠ 0 → 0 ≤ exponent →
    Z.pow (a mod modulus) exponent mod modulus = Z.pow a exponent mod modulus := by
  intro hm he
  have hc : (Int.ofNat exponent.toNat) = exponent := by simpa using Int.toNat_of_nonneg he
  have h := order_ex_pow_mod_base_nat a modulus exponent.toNat hm
  rw [hc] at h
  exact h

theorem order_ex_pow_add_mod_left_one (a modulus left right : Int) :
    1 < modulus → 0 ≤ left → 0 ≤ right → Z.pow a left mod modulus = 1 →
    Z.pow a (left+right) mod modulus = Z.pow a right mod modulus := by
  intro hm hl hr hone
  rw [coq_pow_add a left right hl hr]
  change (Z.pow a left * Z.pow a right).fmod modulus = _
  rw [Int.mul_fmod]
  change (Z.pow a left mod modulus * (Z.pow a right mod modulus)).fmod modulus = _
  rw [hone, one_mul]
  exact Int.fmod_fmod _ _

theorem order_ex_pow_multiple_mod_one (a modulus period multiplier : Int) :
    1 < modulus → 0 ≤ period → 0 ≤ multiplier → Z.pow a period mod modulus = 1 →
    Z.pow a (period*multiplier) mod modulus = 1 := by
  intro hm hp hk hone
  rw [coq_pow_mul a period multiplier hp hk, ← order_ex_pow_mod_base (Z.pow a period) modulus multiplier (by omega) hk, hone]
  rw [coq_pow_nat 1 multiplier hk, one_pow]
  exact Int.fmod_eq_of_lt (by omega) hm

theorem order_ex_pow_divmod_remainder (a modulus period exponent : Int) :
    1 < modulus → 0 < period → 0 ≤ exponent → Z.pow a period mod modulus = 1 →
    Z.pow a exponent mod modulus = Z.pow a (exponent mod period) mod modulus := by
  intro hm hp he hone
  have hr : 0 ≤ exponent mod period := Int.fmod_nonneg_of_pos exponent hp
  have hq : 0 ≤ exponent /ᶻ period := by
    change 0 ≤ exponent.fdiv period
    rw [Int.fdiv_eq_ediv_of_nonneg exponent (by omega)]
    exact Int.ediv_nonneg he (by omega)
  have hde : exponent = period * (exponent /ᶻ period) + exponent mod period := by
    have h := Int.fmod_add_mul_fdiv exponent period
    dsimp [Z.div, Z.modulo]
    omega
  calc
    _ = Z.pow a (period * (exponent /ᶻ period) + exponent mod period) mod modulus := by rw [← hde]
    _ = _ := order_ex_pow_add_mod_left_one a modulus _ _ hm (mul_nonneg (by omega) hq) hr
      (order_ex_pow_multiple_mod_one a modulus period _ hm (by omega) hq hone)

theorem order_ex_search_minimal (base modulus start : Int) (fuel : Nat) (candidate : Int) :
    1 ≤ start → (start ≤ candidate ∧ candidate < order_search base modulus start fuel) →
    Z.pow base candidate mod modulus ≠ 1 := by
  induction fuel generalizing start with
  | zero => simp only [order_search]; omega
  | succ fuel ih =>
    intro hs hr
    simp only [order_search] at hr
    split at hr
    · omega
    · rename_i hcur
      have hn : Z.pow base start mod modulus ≠ 1 := by simpa using hcur
      by_cases he : candidate = start
      · simpa [he] using hn
      · exact ih (start+1) (by omega) ⟨by omega, hr.2⟩

theorem order_ex_search_terminal_spec (base modulus start : Int) (fuel : Nat) :
    1 ≤ start → Z.pow base (start + Int.ofNat fuel) mod modulus = 1 →
    let result := order_search base modulus start (Nat.succ fuel)
    (start ≤ result ∧ result ≤ start + Int.ofNat fuel) ∧ Z.pow base result mod modulus = 1 := by
  induction fuel generalizing start with
  | zero =>
    intro hs ht
    have hc : Z.pow base start mod modulus = 1 := by simpa using ht
    simp [order_search, hc]
  | succ fuel ih =>
    intro hs ht
    dsimp only
    rw [order_search]
    split
    · rename_i hc
      have he : Z.pow base start mod modulus = 1 := by simpa using hc
      exact ⟨⟨le_refl _, by simp only [Int.ofNat_eq_coe]; omega⟩, he⟩
    · have ht' : Z.pow base (start + 1 + Int.ofNat fuel) mod modulus = 1 := by
        have heq : start + 1 + Int.ofNat fuel = start + Int.ofNat (fuel+1) := by
          simp only [Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one]; omega
        rw [heq]
        exact ht
      have hi := ih (start+1) (by omega) ht'
      refine ⟨⟨?_, ?_⟩, hi.2⟩ <;> simp only [Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] at * <;> omega


theorem order_ex_ord_search_exact (x modulus phi : Int) :
    OrderInput x modulus phi → (1 ≤ Ord x modulus ∧ Ord x modulus ≤ phi) ∧
    Z.pow x (Ord x modulus) mod modulus = 1 ∧
    (∀ candidate, (1 ≤ candidate ∧ candidate < Ord x modulus) → Z.pow x candidate mod modulus ≠ 1) := by
  intro hi
  obtain ⟨hm, hphi, hgcd, hpb, hop, hod, hpp⟩ := hi
  have hcount : 0 < phi.toNat := by omega
  obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : phi.toNat ≠ 0)
  have hf : 1 + Int.ofNat fuel = phi := by
    simp only [Int.ofNat_eq_coe]
    omega
  have ht : Z.pow (x mod modulus) (1 + Int.ofNat fuel) mod modulus = 1 := by
    rw [hf, order_ex_pow_mod_base x modulus phi (by omega) (by omega)]
    exact hpp
  have hs := order_ex_search_terminal_spec (x mod modulus) modulus 1 fuel (by omega) ht
  have ho : Ord x modulus = order_search (x mod modulus) modulus 1 (Nat.succ fuel) := by
    unfold Ord
    dsimp only
    have hm1 : (modulus == 1) = false := by simp; omega
    rw [hm1]
    simp only [Bool.false_eq_true, if_false]
    rw [← hphi, hfuel]
  rw [ho]
  refine ⟨⟨hs.1.1, ?_⟩, ?_, ?_⟩
  · rw [← hf]; exact hs.1.2
  · rw [← order_ex_pow_mod_base x modulus _ (by omega) (by omega)]
    exact hs.2
  · intro c hc hcproof
    apply order_ex_search_minimal (x mod modulus) modulus 1 (Nat.succ fuel) c (by omega) hc
    rw [order_ex_pow_mod_base x modulus c (by omega) (by omega)]
    exact hcproof

theorem order_ex_minimal_success_divides (x modulus period exponent : Int) :
    1 < modulus → 0 < period → Z.pow x period mod modulus = 1 →
    (∀ candidate, (1 ≤ candidate ∧ candidate < period) → Z.pow x candidate mod modulus ≠ 1) →
    0 ≤ exponent → Z.pow x exponent mod modulus = 1 → (period ∣ᶻ exponent) := by
  intro hm hp hpow hmin he hepow
  have hrn : 0 ≤ exponent mod period := Int.fmod_nonneg_of_pos exponent hp
  have hrl : exponent mod period < period := Int.fmod_lt_of_pos exponent hp
  have hrp : Z.pow x (exponent mod period) mod modulus = 1 := by
    rw [← order_ex_pow_divmod_remainder x modulus period exponent hm hp he hpow]
    exact hepow
  have hr0 : exponent mod period = 0 := by
    by_contra hne
    exact hmin (exponent mod period) ⟨by omega, hrl⟩ hrp
  exact (Z.divide_iff_dvd _ _).mpr ((Int.dvd_iff_fmod_eq_zero).mpr hr0)

theorem order_ex_success_of_period_divides (x modulus period exponent : Int) :
    1 < modulus → 0 < period → Z.pow x period mod modulus = 1 →
    0 ≤ exponent → (period ∣ᶻ exponent) → Z.pow x exponent mod modulus = 1 := by
  rintro hm hp hpow he ⟨k, hk⟩
  have hkp : 0 ≤ k := by nlinarith
  rw [hk, mul_comm k period]
  exact order_ex_pow_multiple_mod_one x modulus period k hm (by omega) hkp hpow

theorem order_input_power_law (x modulus phi : Int) :
    OrderInput x modulus phi → OrderPowerLaw x modulus := by
  intro hi k hk
  obtain ⟨hb, hp, hmin⟩ := order_ex_ord_search_exact x modulus phi hi
  constructor
  · exact order_ex_minimal_success_divides x modulus _ k hi.1 (by omega) hp hmin hk
  · exact order_ex_success_of_period_divides x modulus _ k hi.1 (by omega) hp hk

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
