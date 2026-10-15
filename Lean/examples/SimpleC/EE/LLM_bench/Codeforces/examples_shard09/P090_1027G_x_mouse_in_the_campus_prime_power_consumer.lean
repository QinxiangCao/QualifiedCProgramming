import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_call_budget
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_PrimePowerConsumer

theorem valid_factor_table_entry (m : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → IsPrime (Znth i pr 0) ∧ 1 ≤ Znth i pe 0 := by
  intro h hi
  exact h.2.2.2.1 i hi

theorem table_power_at_divides_factor_product (pr pe : List Int) (i chosen : Int) :
    OrderedPrimeTable pr pe → (0 ≤ i ∧ i < Zlength pr) → (0 ≤ chosen ∧ chosen ≤ Znth i pe 0) →
    Z.pow (Znth i pr 0) chosen ∣ᶻ factor_product pr pe := by
  intro ht
  induction ht generalizing i chosen with
  | ordered_prime_table_nil => intro hi; simp [Zlength] at hi; omega
  | ordered_prime_table_cons p maximum pr pe hp hm hlt ht ih =>
    intro hi hc
    rw [Zlength_cons] at hi
    by_cases hz : i = 0
    · subst i
      rw [Znth0_cons] at hc ⊢
      have hd := coq_pow_divides_pow p chosen maximum hc.1 hc.2
      exact (Z.divide_iff_dvd _ _).mpr (dvd_mul_of_dvd_left ((Z.divide_iff_dvd _ _).mp hd) _)
    · rw [Znth_cons 0 i p pr (by omega)]
      rw [Znth_cons 0 i maximum pe (by omega)] at hc
      exact (Z.divide_iff_dvd _ _).mpr (dvd_mul_of_dvd_right
        ((Z.divide_iff_dvd _ _).mp (ih (i-1) chosen (by omega) hc)) _)

theorem valid_table_power_at_divides_m (m : Int) (pr pe : List Int) (i chosen : Int) :
    ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → (0 ≤ chosen ∧ chosen ≤ Znth i pe 0) →
    Z.pow (Znth i pr 0) chosen ∣ᶻ m := by
  intro hv hi hc
  rw [hv.2.2.1]
  exact table_power_at_divides_factor_product pr pe i chosen (valid_factor_table_ordered m pr pe hv) hi hc

theorem prefix_selected_coprime_later_prime (m : Int) (pr pe : List Int) (i d k : Int) :
    ValidFactorTable m pr pe → PrefixSelected pr pe i d → (i ≤ k ∧ k < Zlength pr) → Z.gcd d (Znth k pr 0) = 1 := by
  intro hv hs
  induction hs with
  | prefix_selected_zero => intro hk; simp [Z.gcd]
  | prefix_selected_step j previous exponent hs hj he ih =>
    intro hk
    have hprev := ih ⟨by omega,hk.2⟩
    have hpj := (valid_factor_table_entry m pr pe j hv hj).1
    have hpk := (valid_factor_table_entry m pr pe k hv ⟨by omega,hk.2⟩).1
    have hless := hv.2.2.2.2 j k ⟨hj.1,by omega,hk.2⟩
    have hg := smaller_distinct_primes_coprime _ _ hpj hpk hless
    have hgn : Int.gcd (Znth j pr 0) (Znth k pr 0) = 1 := by simpa [Z.gcd] using hg
    have hpn : Int.gcd previous (Znth k pr 0) = 1 := by simpa [Z.gcd] using hprev
    rw [coq_pow_nat _ _ he.1]
    have hpow := Int.gcd_pow_left_of_gcd_eq_one (k:=exponent.toNat) hgn
    unfold Z.gcd
    rw [Int.gcd_mul_right_left_of_gcd_eq_one hpn,hpow]
    rfl

theorem coprime_divisors_product_divides (a b whole : Int) :
    a ∣ᶻ whole → b ∣ᶻ whole → Z.gcd a b = 1 → (a*b) ∣ᶻ whole := by
  intro ha hb hg
  obtain ⟨k,hk⟩ := (Z.divide_iff_dvd _ _).mp ha
  have hd : b ∣ a*k := by rw [← hk]; exact (Z.divide_iff_dvd _ _).mp hb
  have hgn : Int.gcd b a = 1 := by simpa [Z.gcd,Int.gcd_comm] using hg
  have hbk := Int.dvd_of_dvd_mul_right_of_gcd_one hd hgn
  obtain ⟨l,hl⟩ := hbk
  apply (Z.divide_iff_dvd _ _).mpr
  exact ⟨l,by rw [hk,hl]; ring⟩

theorem prefix_selected_divides_m (m : Int) (pr pe : List Int) (i d : Int) :
    ValidFactorTable m pr pe → PrefixSelected pr pe i d → d ∣ᶻ m := by
  intro hv hs
  induction hs with
  | prefix_selected_zero => exact (Z.divide_iff_dvd _ _).mpr (one_dvd _)
  | prefix_selected_step j previous exponent hs hj he ih =>
    exact coprime_divisors_product_divides _ _ _ ih (valid_table_power_at_divides_m m pr pe j exponent hv hj he)
      (gcd_prime_power_one previous (Znth j pr 0) exponent he.1
        (prefix_selected_coprime_later_prime m pr pe j previous j hv hs ⟨le_refl _,hj.2⟩))

theorem gcd_with_divisor_of_coprime_modulus (x divisor modulus : Int) :
    Z.gcd x modulus = 1 → divisor ∣ᶻ modulus → Z.gcd x divisor = 1 := by
  intro hg hd
  have hgn : Int.gcd x modulus = 1 := by simpa [Z.gcd] using hg
  have hd' := (Z.divide_iff_dvd _ _).mp hd
  have h : Int.gcd x divisor = 1 := Int.gcd_eq_one_iff.mpr (by
    intro k hkx hkd
    exact Int.gcd_eq_one_iff.mp hgn k hkx (dvd_trans hkd hd'))
  simpa [Z.gcd] using congrArg Int.ofNat h

theorem gcd_coprime_product (x a b : Int) :
    Z.gcd x a = 1 → Z.gcd x b = 1 → Z.gcd x (a*b) = 1 := by
  intro ha hb
  have han : Int.gcd x a = 1 := by simpa [Z.gcd] using ha
  have hbn : Int.gcd x b = 1 := by simpa [Z.gcd] using hb
  simp [Z.gcd,Int.gcd_mul_right_right_of_gcd_eq_one han,hbn]

theorem prime_power_consumer_basic (m x p exponent pk d : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → PrefixSelected pr pe i d → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    (1 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkGlobalBounds m x → pk = Z.pow p exponent →
    (2 ≤ pk ∧ pk ≤ m) ∧ pk ∣ᶻ m ∧ Z.gcd d p = 1 ∧ Z.gcd d pk = 1 ∧ Z.gcd x pk = 1 := by
  intro hv hs hi hp he hg hpk
  subst p
  subst pk
  have hprime := (valid_factor_table_entry m pr pe i hv hi).1
  have hdiv := valid_table_power_at_divides_m m pr pe i exponent hv hi ⟨by omega,he.2⟩
  have hdp := prefix_selected_coprime_later_prime m pr pe i d i hv hs ⟨le_refl _,hi.2⟩
  have hpow := coq_pow_pos (Znth i pr 0) exponent (by have := hprime.1; omega) (by omega)
  have hmono := coq_pow_mono (Znth i pr 0) 1 exponent (by have := hprime.1; omega) (by omega) he.1
  have hp1 : Z.pow (Znth i pr 0) 1 = Znth i pr 0 := by simp [Z.pow]
  rw [hp1] at hmono
  have hm := hg.1.1
  exact ⟨⟨by have := hprime.1; omega,Int.le_of_dvd (by omega) ((Z.divide_iff_dvd _ _).mp hdiv)⟩,
    hdiv,hdp,gcd_prime_power_one _ _ _ (by omega) hdp,gcd_with_divisor_of_coprime_modulus x _ m hg.2.2 hdiv⟩

theorem prime_power_consumer_order_input (m x p exponent pk ph d : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → PrefixSelected pr pe i d → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    (1 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkGlobalBounds m x → pk = Z.pow p exponent → ph = EulerPhi pk →
    OrderInput (x mod pk) pk ph := by
  intro hv hs hi hp he hg hpk hph
  have hb := prime_power_consumer_basic m x p exponent pk d pr pe i hv hs hi hp he hg hpk
  subst ph
  exact coprime_implies_reduced_order_input x pk (by have := hb.1.1; omega) hb.2.2.2.2

theorem prime_power_consumer_euler (m p exponent pk d : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → PrefixSelected pr pe i d → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    (1 ≤ exponent ∧ exponent ≤ Znth i pe 0) → pk = Z.pow p exponent →
    EulerPhi (d*pk) = EulerPhi d*EulerPhi pk := by
  intro hv hs hi hp he hpk
  subst p
  subst pk
  have hd := prefix_selected_positive_from_valid_table m pr pe i d hv hs
  exact euler_phi_coprime_prime_power_all d _ exponent (by omega)
    (valid_factor_table_entry m pr pe i hv hi).1 (by omega)
    (prefix_selected_coprime_later_prime m pr pe i d i hv hs ⟨le_refl _,hi.2⟩)

theorem prime_power_consumer_order_product (m x p exponent pk d phi ord o g : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → PrefixChoice pr pe x i d phi ord → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    (1 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkGlobalBounds m x → pk = Z.pow p exponent →
    o = Ord (x mod pk) pk → g = Z.gcd ord o → Ord x (d*pk) = ord /ᶻ g*o ∧ 0 < ord /ᶻ g*o := by
  intro hv hc hi hp he hg hpk ho hgg
  obtain ⟨hl,hci,hs,hd,hphi,hord,hphiv,hordv,hxd⟩ := hc
  obtain ⟨hpkb,hpkd,hdp,hdpk,hxpk⟩ := prime_power_consumer_basic m x p exponent pk d pr pe i hv hs hi hp he hg hpk
  have hopos : 0 < o := by have hh := ord_positive (x mod pk) pk; omega
  obtain ⟨hruntime,hrpos⟩ := order_lcm_runtime_formula ord o g hord hopos hgg
  refine ⟨?_,hrpos⟩
  have hou : o = Ord x pk := by rw [ho,ord_reduced_base x pk (by omega)]
  by_cases hd1 : d = 1
  · subst d
    have hord1 : ord = 1 := by simpa [Ord] using hordv
    rw [hord1] at hgg ⊢
    have hg1 : g = 1 := by simpa [Z.gcd] using hgg
    rw [hg1]
    simpa [Z.div] using hou.symm
  · have hcd := coprime_implies_exact_order_criterion x d (by omega) hxd
    have hcpk := coprime_implies_exact_order_criterion x pk (by omega) hxpk
    rw [← hordv] at hcd
    rw [← hou] at hcpk
    have hcp := exact_order_coprime_product_lcm d pk x ord o (by omega) hpkb.1 hdpk hcd hcpk
    rw [hruntime]
    exact (exact_order_criterion_is_ord x (d*pk) (Z.lcm ord o) (by nlinarith)
      (gcd_coprime_product x d pk hxd hxpk) hcp).symm

theorem prime_power_consumer_transition (m x p exponent pk ph o g d phi ord : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → PrefixChoice pr pe x i d phi ord → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    (1 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkGlobalBounds m x → pk = Z.pow p exponent →
    ph = EulerPhi pk → o = Ord (x mod pk) pk → g = Z.gcd ord o →
    OrderInput (x mod pk) pk ph ∧
    PrimePowerTransition x d phi ord p exponent pk ph o g (d*pk) (phi*ph) (ord /ᶻ g*o) ∧
    PrefixChoice pr pe x (i+1) (d*pk) (phi*ph) (ord /ᶻ g*o) ∧
    WalkMachineBounds m (d*pk) (phi*ph) (ord /ᶻ g*o) := by
  intro hv hc hi hp he hg hpk hph ho hgg
  have hc0 := hc
  obtain ⟨hl,hci,hs,hd,hphi,hord,hphiv,hordv,hxd⟩ := hc
  obtain ⟨hpkb,hpkd,hdp,hdpk,hxpk⟩ := prime_power_consumer_basic m x p exponent pk d pr pe i hv hs hi hp he hg hpk
  have hinput := prime_power_consumer_order_input m x p exponent pk ph d pr pe i hv hs hi hp he hg hpk hph
  have heuler := prime_power_consumer_euler m p exponent pk d pr pe i hv hs hi hp he hpk
  obtain ⟨horder,horderpos⟩ := prime_power_consumer_order_product m x p exponent pk d phi ord o g pr pe i hv hc0 hi hp he hg hpk ho hgg
  have hndpos : 0 < d*pk := mul_pos hd (by omega)
  have hphib := euler_phi_positive_bounded pk (by omega)
  have hnphipos : 0 < phi*ph := by rw [hph]; exact mul_pos hphi hphib.1
  have hxprod := gcd_coprime_product x d pk hxd hxpk
  have hnextsel : PrefixSelected pr pe (i+1) (d*pk) := by
    rw [hpk,hp]
    exact prefix_selected_step_product pr pe i d exponent hs hi ⟨by omega,he.2⟩
  have hnextphi : phi*ph = EulerPhi (d*pk) := by rw [heuler,hphiv,hph]
  have hnextchoice : PrefixChoice pr pe x (i+1) (d*pk) (phi*ph) (ord /ᶻ g*o) :=
    ⟨hl,by omega,hnextsel,hndpos,hnphipos,horderpos,hnextphi,horder.symm,hxprod⟩
  have hpprime : 1 < p := by rw [hp]; exact (valid_factor_table_entry m pr pe i hv hi).1.1
  have htransition := prime_power_transition_build x d phi ord p exponent pk ph o g (d*pk) (phi*ph) (ord /ᶻ g*o)
    hd hpprime he.1 hpk hph ho hgg rfl rfl rfl hdpk heuler horder hndpos hnphipos horderpos
  have hnextdiv := prefix_selected_divides_m m pr pe (i+1) (d*pk) hv hnextsel
  have hndle : d*pk ≤ m := Int.le_of_dvd (by have := hg.1.1; omega) ((Z.divide_iff_dvd _ _).mp hnextdiv)
  have hnphib := euler_phi_positive_bounded (d*pk) (by omega)
  have hprodinput := coprime_implies_order_input x (d*pk) (by nlinarith) hxprod
  have horddiv := hprodinput.2.2.2.2.2.1
  rw [horder] at horddiv
  have hordle : ord /ᶻ g*o ≤ EulerPhi (d*pk) :=
    Int.le_of_dvd hnphib.1 ((Z.divide_iff_dvd _ _).mp horddiv)
  exact ⟨hinput,htransition,hnextchoice,⟨hndpos,hndle⟩,
    ⟨hnphipos,by rw [hnextphi]; omega⟩,⟨horderpos,by omega⟩⟩

end P090_PrimePowerConsumer
export P090_PrimePowerConsumer (valid_factor_table_entry table_power_at_divides_factor_product valid_table_power_at_divides_m
  prefix_selected_coprime_later_prime coprime_divisors_product_divides prefix_selected_divides_m
  gcd_with_divisor_of_coprime_modulus gcd_coprime_product prime_power_consumer_basic prime_power_consumer_order_input
  prime_power_consumer_euler prime_power_consumer_order_product prime_power_consumer_transition)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
