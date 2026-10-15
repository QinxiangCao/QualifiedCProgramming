import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_bridge

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_TableBudget

theorem valid_factor_table_ordered_aux (pr pe : List Int) :
    Zlength pr=Zlength pe →
    (∀ k, (0≤k ∧ k<Zlength pr) → IsPrime (Znth k pr 0) ∧ 1≤Znth k pe 0) →
    (∀ j k, (0≤j ∧ j<k ∧ k<Zlength pr) → Znth j pr 0<Znth k pr 0) → OrderedPrimeTable pr pe := by
  induction pr generalizing pe with
  | nil =>
    intro hl he ho
    cases pe with
    | nil => exact .ordered_prime_table_nil
    | cons p pe => simp [Zlength] at hl; omega
  | cons p pr ih =>
    intro hl he ho
    cases pe with
    | nil => simp [Zlength] at hl; omega
    | cons e pe =>
      have hhead : IsPrime p ∧ 1≤e := he 0 (by simp [Zlength])
      refine .ordered_prime_table_cons p e pr pe hhead.1 hhead.2 ?_ ?_
      · apply Forall.iff_forall_mem.mpr
        intro q hq
        obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hq
        have hz : Znth (k:Int) pr 0=q := by
          unfold Znth
          simp only [Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]
          exact hget
        have hr : 0≤(0:Int) ∧ 0<(k:Int)+1 ∧ (k:Int)+1<Zlength (p::pr) := by simp [Zlength]; omega
        have hh := ho 0 ((k:Int)+1) hr
        rw [Znth0_cons,Znth_cons 0 ((k:Int)+1) p pr (by omega)] at hh
        simpa [hz] using hh
      · apply ih pe
        · rw [Zlength_cons,Zlength_cons] at hl; omega
        · intro k hk
          have hh := he (k+1) (by rw [Zlength_cons]; omega)
          rw [Znth_cons 0 (k+1) p pr (by omega),Znth_cons 0 (k+1) e pe (by omega)] at hh
          simpa using hh
        · intro j k hjk
          have hh := ho (j+1) (k+1) (by rw [Zlength_cons]; omega)
          rw [Znth_cons 0 (j+1) p pr (by omega),Znth_cons 0 (k+1) p pr (by omega)] at hh
          simpa using hh

theorem valid_factor_table_ordered (m : Int) (pr pe : List Int) : ValidFactorTable m pr pe → OrderedPrimeTable pr pe := by
  intro h
  exact valid_factor_table_ordered_aux pr pe h.1 h.2.2.2.1 h.2.2.2.2

theorem sum_nat_range_mul_l (first count : Nat) (c : Int) (f : Nat→Int) :
    sum_nat_range first count (fun k=>c*f k)=c*sum_nat_range first count f := by
  induction count generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih => rw [sum_nat_range,sum_nat_range,ih]; ring

theorem sum_nat_range_mul_r (first count : Nat) (c : Int) (f : Nat→Int) :
    sum_nat_range first count (fun k=>f k*c)=sum_nat_range first count f*c := by
  induction count generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih => rw [sum_nat_range,sum_nat_range,ih]; ring

theorem euler_phi_one : EulerPhi 1=1 := rfl

theorem euler_phi_coprime_prime_power_all (d p exponent : Int) :
    1≤d → IsPrime p → 0≤exponent → Z.gcd d p=1 →
    EulerPhi (d*Z.pow p exponent)=EulerPhi d*EulerPhi (Z.pow p exponent) := by
  intro hd hp he hg
  by_cases hz : exponent=0
  · subst exponent
    simp [Z.pow,euler_phi_one]
  · have hmod : d mod p≠0 := by
      intro hzero
      have hgm := coq_gcd_mod d p
      rw [hzero,hg] at hgm
      have hpp := hp.1
      have hh : Z.gcd 0 p=p := by simp [Z.gcd,Int.natAbs_of_nonneg (show 0≤p by omega)]
      rw [hh] at hgm
      omega
    rw [euler_phi_coprime_prime_power d p exponent hd hp (by omega) hmod,euler_phi_prime_power p exponent hp (by omega)]

theorem euler_phi_coprime_prime_power_sum (d p exponent : Int) :
    1≤d → IsPrime p → 0≤exponent → Z.gcd d p=1 →
    sum_nat_range 0 (Nat.succ exponent.toNat) (fun k=>EulerPhi (d*Z.pow p (Int.ofNat k)))=EulerPhi d*Z.pow p exponent := by
  intro hd hp he hg
  calc
    _ = sum_nat_range 0 (Nat.succ exponent.toNat) (fun k=>EulerPhi d*EulerPhi (Z.pow p (Int.ofNat k))) := by
      apply sum_nat_range_ext
      intro k hk
      exact euler_phi_coprime_prime_power_all d p _ hd hp (Int.ofNat_zero_le k) hg
    _ = _ := by rw [sum_nat_range_mul_l,euler_phi_prime_power_sum p exponent hp he]

theorem smaller_distinct_primes_coprime (p q : Int) : IsPrime p → IsPrime q → p<q → Z.gcd p q=1 := by
  intro hp hq hpq
  have hgpos := Int.gcd_pos_of_ne_zero_left q (by have := hp.1; omega : p≠0)
  have hgle := Int.gcd_le_left q (by have := hp.1; omega : 0<p)
  have hdiv := Int.gcd_dvd_right p q
  have hgn : Int.gcd p q=1 := by
    by_contra hn
    exact hq.2 (Int.gcd p q) ⟨by omega,by omega⟩ (Int.fmod_eq_zero_of_dvd hdiv)
  simp [Z.gcd,hgn]

theorem coprime_to_table_extend (d p : Int) (pr : List Int) (k : Nat) :
    CoprimeToTable d pr → IsPrime p → Forall IsPrime pr → Forall (fun q=>p<q) pr →
    CoprimeToTable (d*Z.pow p (Int.ofNat k)) pr := by
  intro hd hp hpr hl
  apply Forall.iff_forall_mem.mpr
  intro q hq
  have hdq := hd.mem hq
  have hpq := smaller_distinct_primes_coprime p q hp (hpr.mem hq) (hl.mem hq)
  have hdqn : Int.gcd d q=1 := by simpa [Z.gcd] using hdq
  have hpqn : Int.gcd p q=1 := by simpa [Z.gcd] using hpq
  have hpow := Int.gcd_pow_left_of_gcd_eq_one (k:=k) hpqn
  have hmul := Int.gcd_mul_right_left_of_gcd_eq_one (k:=p^k) hdqn
  change Int.ofNat (Int.gcd (d*Z.pow p (Int.ofNat k)) q)=1
  simp only [Z.pow]
  rw [hmul,hpow]
  rfl

theorem ordered_prime_table_all_primes (pr pe : List Int) : OrderedPrimeTable pr pe → Forall IsPrime pr := by
  intro h
  induction h with
  | ordered_prime_table_nil => exact .nil
  | ordered_prime_table_cons p e pr pe hp he hl ht ih => exact .cons hp ih

theorem enumerated_phi_sum_factor_product (pr pe : List Int) (d : Int) :
    OrderedPrimeTable pr pe → 1≤d → CoprimeToTable d pr →
    enumerated_phi_sum pr pe d=EulerPhi d*factor_product pr pe := by
  intro ht
  induction ht generalizing d with
  | ordered_prime_table_nil => intro hd hc; simp [enumerated_phi_sum,factor_product]
  | ordered_prime_table_cons p e pr pe hp he hl ht ih =>
    intro hd hc
    cases hc with
    | cons hg hct =>
      change sum_nat_range 0 (Nat.succ e.toNat) (fun k=>enumerated_phi_sum pr pe (d*Z.pow p (Int.ofNat k))) =
        EulerPhi d*(Z.pow p e*factor_product pr pe)
      calc
        _ = sum_nat_range 0 (Nat.succ e.toNat) (fun k=>EulerPhi (d*Z.pow p (Int.ofNat k))*factor_product pr pe) := by
          apply sum_nat_range_ext
          intro k hk
          apply ih
          · have hpow := coq_pow_pos p (Int.ofNat k) (by have := hp.1; omega) (Int.ofNat_zero_le k)
            nlinarith
          · exact coprime_to_table_extend d p pr k hct hp (ordered_prime_table_all_primes pr pe ht) hl
        _ = _ := by
          rw [sum_nat_range_mul_r,euler_phi_coprime_prime_power_sum d p e hd hp (by omega) hg]
          ring

theorem coprime_one_table (pr : List Int) : CoprimeToTable 1 pr := by
  apply Forall.iff_forall_mem.mpr
  intro p hp
  simp [Z.gcd]

theorem valid_factor_table_enumerated_phi_exact (m : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → enumerated_phi_sum pr pe 1=m := by
  intro h
  rw [enumerated_phi_sum_factor_product pr pe 1 (valid_factor_table_ordered m pr pe h) (by omega) (coprime_one_table pr),euler_phi_one,one_mul]
  exact h.2.2.1.symm

theorem walk_suffix_lists_le_enumerated_phi (pr pe : List Int) (x d : Int) :
    walk_suffix_lists pr pe x d≤enumerated_phi_sum pr pe d := by
  induction pr generalizing pe d with
  | nil => cases pe <;> exact cycle_term_le_euler_phi x d
  | cons p pr ih =>
    cases pe with
    | nil => exact cycle_term_le_euler_phi x d
    | cons e pe =>
      apply sum_nat_range_mono
      intro k hk
      exact ih pe _

theorem nonunit_cycle_term_exact_bounds (x d : Int) : d≠1 →
    CycleTerm x d=EulerPhi d /ᶻ Ord (x mod d) d ∧ (0≤CycleTerm x d ∧ CycleTerm x d≤EulerPhi d) := by
  intro hd
  refine ⟨?_,cycle_term_nonnegative x d,cycle_term_le_euler_phi x d⟩
  simp [CycleTerm,hd]

theorem ordered_table_walk_bounds (pr pe : List Int) (x d : Int) :
    OrderedPrimeTable pr pe → 1≤d → CoprimeToTable d pr →
    (0≤walk_suffix_lists pr pe x d ∧ walk_suffix_lists pr pe x d≤EulerPhi d*factor_product pr pe) := by
  intro ht hd hc
  refine ⟨walk_suffix_lists_nonnegative pr pe x d,?_⟩
  rw [← enumerated_phi_sum_factor_product pr pe d ht hd hc]
  exact walk_suffix_lists_le_enumerated_phi pr pe x d

theorem walk_suffix_recursive_budget (m before : Int) (pr pe : List Int) (x i d : Int) :
    OrderedPrimeTable (pr.drop i.toNat) (pe.drop i.toNat) → 1≤d → CoprimeToTable d (pr.drop i.toNat) →
    0≤before → before+EulerPhi d*factor_product (pr.drop i.toNat) (pe.drop i.toNat)≤m →
    WalkBudget m before (WalkSuffix pr pe x i d) := by
  intro ht hd hc hb hm
  have hw := ordered_table_walk_bounds (pr.drop i.toNat) (pe.drop i.toNat) x d ht hd hc
  exact ⟨hb,hw.1,by change before+walk_suffix_lists (pr.drop i.toNat) (pe.drop i.toNat) x d≤m; omega⟩

theorem valid_factor_table_walk_bounds (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → (0≤WalkSuffix pr pe x 0 1 ∧ WalkSuffix pr pe x 0 1≤m) := by
  intro ht
  refine ⟨walk_suffix_nonnegative pr pe x 0 1,?_⟩
  rw [walk_suffix_zero_index,← valid_factor_table_enumerated_phi_exact m pr pe ht]
  exact walk_suffix_lists_le_enumerated_phi pr pe x 1

theorem valid_factor_table_initial_walk_budget (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → WalkBudget m 0 (WalkSuffix pr pe x 0 1) := by
  intro ht
  have hw := valid_factor_table_walk_bounds m x pr pe ht
  exact ⟨le_refl _,hw.1,by omega⟩

theorem walk_budget_from_cumulative_bound (m before work : Int) :
    0≤before → 0≤work → before+work≤m → WalkBudget m before work := fun hb hw hm=>⟨hb,hw,hm⟩

theorem walk_suffix_cumulative_budget (m before : Int) (pr pe : List Int) (x i d : Int) :
    0≤before → before+WalkSuffix pr pe x i d≤m → WalkBudget m before (WalkSuffix pr pe x i d) := by
  intro hb hm
  exact ⟨hb,walk_suffix_nonnegative pr pe x i d,hm⟩

end P090_TableBudget
export P090_TableBudget (valid_factor_table_ordered_aux valid_factor_table_ordered sum_nat_range_mul_l sum_nat_range_mul_r euler_phi_one euler_phi_coprime_prime_power_all euler_phi_coprime_prime_power_sum smaller_distinct_primes_coprime coprime_to_table_extend ordered_prime_table_all_primes enumerated_phi_sum_factor_product coprime_one_table valid_factor_table_enumerated_phi_exact walk_suffix_lists_le_enumerated_phi nonunit_cycle_term_exact_bounds ordered_table_walk_bounds walk_suffix_recursive_budget valid_factor_table_walk_bounds valid_factor_table_initial_walk_budget walk_budget_from_cumulative_bound walk_suffix_cumulative_budget)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
