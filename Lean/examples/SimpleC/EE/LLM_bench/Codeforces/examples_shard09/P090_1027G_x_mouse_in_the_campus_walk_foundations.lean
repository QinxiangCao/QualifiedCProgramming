import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_factor_foundations
import AUXLib.NumberTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

theorem coq_gcd_mod (a n : Int) : Z.gcd (a mod n) n = Z.gcd a n := by
  have h := Int.fmod_add_mul_fdiv a n
  have hg : Int.gcd (a.fmod n) n = Int.gcd a n := by
    calc
      _ = Int.gcd (a.fmod n+n*a.fdiv n) n := (Int.gcd_add_mul_left_left n (a.fmod n) (a.fdiv n)).symm
      _ = _ := by rw [h]
  exact congrArg Int.ofNat hg

theorem coq_mod_one_iff (a n : Int) (hn : 1<n) : a mod n = 1 ↔ (n ∣ᶻ a-1) := by
  have h1 : (1:Int).fmod n=1 := Int.fmod_eq_of_lt (by omega) hn
  rw [Z.divide_iff_dvd, Int.dvd_iff_fmod_eq_zero]
  change a.fmod n=1 ↔ (a-1).fmod n=0
  rw [← Int.fmod_eq_fmod_iff_fmod_sub_eq_zero, h1]

theorem coq_lcm_native (a b : Int) : Z.lcm a b = (Int.lcm a b : Int) := by
  unfold Z.lcm Z.abs Z.div Z.gcd
  simp only [Int.ofNat_eq_coe]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  rw [Int.natAbs_mul, Int.natAbs_ediv_of_dvd (Int.gcd_dvd_right a b)]
  simp only [Int.natAbs_natCast]
  rw [Int.lcm_eq_mul_div, Nat.mul_div_assoc a.natAbs (by
    simpa [Int.gcd_eq_natAbs_gcd_natAbs] using Nat.gcd_dvd_right a.natAbs b.natAbs)]

namespace P090_WalkFoundations

theorem coprime_count_filter (n : Int) (fuel : Nat) :
    coprime_count n fuel = Int.ofNat (((List.range' 1 fuel).filter (fun k : Nat => Z.gcd (Int.ofNat k) n == 1)).length) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [coprime_count, List.range'_1_concat, List.filter_append, List.length_append]
    simp only [Int.ofNat_eq_coe, Nat.cast_add] at *
    rw [ih]
    have hs : 1+fuel=fuel+1 := by omega
    simp only [hs, List.filter_cons, List.filter_nil]
    split <;> simp_all

theorem euler_phi_bridge (n : Int) : EulerPhi n = ETI.EulerTotientValue n :=
  coprime_count_filter n n.toNat

theorem coprime_count_nonnegative (n : Int) (fuel : Nat) : 0 ≤ coprime_count n fuel := by
  rw [coprime_count_filter]
  exact Int.ofNat_zero_le _

theorem euler_phi_nonnegative (n : Int) : 0 ≤ EulerPhi n := coprime_count_nonnegative n n.toNat

theorem euler_phi_positive_bounded (n : Int) : 1 ≤ n → (1 ≤ EulerPhi n ∧ EulerPhi n ≤ n) := by
  intro hn
  rw [euler_phi_bridge]
  let rs := (List.range' 1 n.toNat).filter (fun k : Nat => Z.gcd (Int.ofNat k) n == 1)
  have hone : 1 ∈ rs := by
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply List.mem_range'.mpr
      exact ⟨0, by omega, rfl⟩
    · simp [Z.gcd]
  have hpos : 0 < rs.length := List.length_pos_of_mem hone
  have hle : rs.length ≤ n.toNat := by
    exact (List.length_filter_le _ _).trans (by simp)
  change 1 ≤ Int.ofNat rs.length ∧ Int.ofNat rs.length ≤ n
  simp only [Int.ofNat_eq_coe]
  omega

theorem euler_phi_zero_counterexample : EulerPhi 0=0 := rfl

theorem is_prime_to_coq_prime (p : Int) : IsPrime p → prime p := (order_ex_is_prime_iff_std p).mp

theorem euler_phi_prime_power (p exponent : Int) :
    IsPrime p → 1 ≤ exponent → EulerPhi (Z.pow p exponent) = Z.pow p (exponent-1)*(p-1) := by
  intro hp he
  rw [euler_phi_bridge]
  exact ETI.euler_totient_prime_power__euler_phi_setup_removal p exponent (is_prime_to_coq_prime p hp) he

theorem euler_phi_coprime_multiplicative (a b : Int) :
    2 ≤ a → 2 ≤ b → Z.gcd a b=1 → EulerPhi (a*b)=EulerPhi a*EulerPhi b := by
  intro ha hb hg
  rw [euler_phi_bridge, euler_phi_bridge, euler_phi_bridge]
  exact ETI.euler_totient_multiplicative__euler_phi_setup_removal a b ha hb ((Zgcd_1_rel_prime a b).mp hg)

theorem euler_phi_coprime_prime_power (d p exponent : Int) :
    1 ≤ d → IsPrime p → 1 ≤ exponent → d mod p ≠ 0 →
    EulerPhi (d*Z.pow p exponent)=EulerPhi d*(Z.pow p (exponent-1)*(p-1)) := by
  intro hd hp he hm
  rw [euler_phi_bridge, euler_phi_bridge]
  exact ETI.euler_totient_coprime_prime_power__euler_phi_setup_removal d p exponent hd (is_prime_to_coq_prime p hp) he
    (by intro hdiv; exact hm ((Int.dvd_iff_fmod_eq_zero).mp ((Z.divide_iff_dvd _ _).mp hdiv)))

theorem gcd_prime_power_one (d p exponent : Int) :
    0 ≤ exponent → Z.gcd d p=1 → Z.gcd d (Z.pow p exponent)=1 := by
  intro he hg
  have hgn : Int.gcd d p=1 := by simpa [Z.gcd] using hg
  rw [coq_pow_nat p exponent he]
  have hp := Int.gcd_pow_right_of_gcd_eq_one (k:=exponent.toNat) hgn
  simpa [Z.gcd] using congrArg Int.ofNat hp

theorem pow_mod_coprime_product_one_iff (a b x exponent : Int) :
    2 ≤ a → 2 ≤ b → Z.gcd a b=1 →
    (Z.pow x exponent mod (a*b)=1 ↔ Z.pow x exponent mod a=1 ∧ Z.pow x exponent mod b=1) := by
  intro ha hb hg
  rw [coq_mod_one_iff _ (a*b) (by nlinarith), coq_mod_one_iff _ a (by omega), coq_mod_one_iff _ b (by omega)]
  constructor
  · intro h
    simp only [Z.divide_iff_dvd] at *
    exact ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩
  · rintro ⟨ha',hb'⟩
    exact ETI.euler_relprime_product_divide__euler_phi_setup_removal a b _ ((Zgcd_1_rel_prime a b).mp hg) ha' hb'

theorem lcm_as_gcd_quotient_product (a b : Int) :
    0<a → 0<b → Z.lcm a b = a /ᶻ Z.gcd a b * b := by
  intro ha hb
  have hgp : 0<Z.gcd a b := by
    have h := Int.gcd_pos_of_ne_zero_left b (by omega : a≠0)
    simpa [Z.gcd] using h
  have hdiv : a mod Z.gcd a b=0 := Int.fmod_eq_zero_of_dvd (Int.gcd_dvd_left a b)
  have hde := coq_div_factor a (Z.gcd a b) hdiv
  have hprod : Z.gcd a b * Z.lcm a b = a*b := by
    rw [coq_lcm_native]
    have hn := Int.gcd_mul_lcm a b
    have ha' := (Int.eq_natAbs_of_nonneg (by omega : 0≤a)).symm
    have hb' := (Int.eq_natAbs_of_nonneg (by omega : 0≤b)).symm
    unfold Z.gcd
    simp only [Int.ofNat_eq_coe]
    exact_mod_cast (by simpa [ha',hb'] using congrArg (fun z : Nat => (z:Int)) hn)
  nlinarith

theorem exact_order_coprime_product_lcm (a b x order_a order_b : Int) :
    2≤a → 2≤b → Z.gcd a b=1 → ExactOrderCriterion x a order_a → ExactOrderCriterion x b order_b →
    ExactOrderCriterion x (a*b) (Z.lcm order_a order_b) := by
  rintro ha hb hg ⟨hoa,hca⟩ ⟨hob,hcb⟩
  refine ⟨?_, ?_⟩
  · rw [coq_lcm_native]
    have h := Int.lcm_pos (by omega : order_a≠0) (by omega : order_b≠0)
    exact_mod_cast h
  · intro e he
    rw [pow_mod_coprime_product_one_iff a b x e ha hb hg, hca e he, hcb e he]
    rw [coq_lcm_native]
    simp only [Z.divide_iff_dvd]
    exact Int.coe_lcm_dvd_iff.symm

theorem order_lcm_runtime_formula (order_a order_b g : Int) :
    0<order_a → 0<order_b → g=Z.gcd order_a order_b →
    order_a /ᶻ g * order_b=Z.lcm order_a order_b ∧ 0<order_a /ᶻ g * order_b := by
  rintro ha hb rfl
  rw [← lcm_as_gcd_quotient_product order_a order_b ha hb]
  refine ⟨rfl, ?_⟩
  rw [coq_lcm_native]
  exact_mod_cast (Int.lcm_pos (by omega : order_a≠0) (by omega : order_b≠0))

theorem order_search_positive (x n k : Int) (fuel : Nat) : 1≤k → 1≤order_search x n k fuel := by
  induction fuel generalizing k with
  | zero => simp [order_search]
  | succ f ih =>
    intro hk
    rw [order_search]
    split
    · exact hk
    · exact ih (k+1) (by omega)

theorem ord_positive (x n : Int) : 1≤Ord x n := by
  unfold Ord
  split
  · omega
  · exact order_search_positive _ _ _ _ (by omega)

theorem ord_non_coprime_counterexample : Ord 2 4=1 ∧ Z.pow 2 (Ord 2 4) mod 4≠1 := by decide

theorem cycle_term_nonnegative (x d : Int) : 0≤CycleTerm x d := by
  unfold CycleTerm
  split
  · omega
  · have hp := ord_positive (x mod d) d
    have he := euler_phi_nonnegative d
    change 0 ≤ (EulerPhi d).fdiv (Ord (x mod d) d)
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    exact Int.ediv_nonneg he (by omega)

theorem sum_nat_range_nonnegative_local (first count : Nat) (f : Nat→Int) :
    (∀ k, 0≤f k) → 0≤sum_nat_range first count f := by
  induction count generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih =>
    intro hf
    rw [sum_nat_range]
    exact add_nonneg (hf first) (ih (first+1) hf)

theorem walk_suffix_lists_nonnegative (pr pe : List Int) (x d : Int) : 0≤walk_suffix_lists pr pe x d := by
  induction pr generalizing pe d with
  | nil => cases pe <;> exact cycle_term_nonnegative x d
  | cons p pr ih =>
    cases pe with
    | nil => exact cycle_term_nonnegative x d
    | cons e pe =>
      apply sum_nat_range_nonnegative_local
      intro k
      exact ih pe _

theorem walk_suffix_nonnegative (pr pe : List Int) (x i d : Int) : 0≤WalkSuffix pr pe x i d :=
  walk_suffix_lists_nonnegative _ _ _ _

theorem walk_suffix_lists_cons (p exponent : Int) (pr pe : List Int) (x d : Int) :
    walk_suffix_lists (p::pr) (exponent::pe) x d =
    sum_nat_range 0 (Nat.succ exponent.toNat) (fun e => walk_suffix_lists pr pe x (d*Z.pow p (Int.ofNat e))) := rfl

theorem walk_suffix_zero_index (pr pe : List Int) (x d : Int) : WalkSuffix pr pe x 0 d=walk_suffix_lists pr pe x d := rfl

theorem walk_suffix_mismatched_left (pe : List Int) (x d : Int) : walk_suffix_lists [] pe x d=CycleTerm x d := by cases pe <;> rfl

theorem walk_suffix_mismatched_right (pr : List Int) (x d : Int) : walk_suffix_lists pr [] x d=CycleTerm x d := by cases pr <;> rfl

theorem gcd_stratum_preserved (m x start exponent : Int) :
    0<m → 0≤exponent → Z.gcd x m=1 → Z.gcd ((start*Z.pow x exponent) mod m) m=Z.gcd start m := by
  intro hm he hg
  rw [coq_gcd_mod, coq_pow_nat x exponent he]
  have hgn : Int.gcd x m=1 := by simpa [Z.gcd] using hg
  have hgp := Int.gcd_pow_left_of_gcd_eq_one (k:=exponent.toNat) hgn
  exact congrArg Int.ofNat (Int.gcd_mul_left_left_of_gcd_eq_one (k:=start) hgp)

theorem catches_all_contains_zero (m x : Int) (traps : List Int) : 0<m → CatchesAll m x traps → 0∈traps := by
  rintro hm ⟨_,_,hc⟩
  obtain ⟨t,r,ht,hr,hin⟩ := hc 0 ⟨le_refl _,hm⟩
  subst r
  simpa [Z.modulo] using hin

theorem catches_all_hits_same_gcd_stratum (m x : Int) (traps : List Int) :
    0<m → Z.gcd x m=1 → CatchesAll m x traps →
    ∀ start, (0≤start ∧ start<m) → ∃ room, room∈traps ∧ Z.gcd room m=Z.gcd start m := by
  rintro hm hg ⟨_,_,hc⟩ start hs
  obtain ⟨t,r,ht,hr,hin⟩ := hc start hs
  refine ⟨r,hin,?_⟩
  rw [hr]
  exact gcd_stratum_preserved m x start t hm ht hg

end P090_WalkFoundations
export P090_WalkFoundations (coprime_count_filter euler_phi_bridge coprime_count_nonnegative euler_phi_nonnegative euler_phi_positive_bounded euler_phi_zero_counterexample is_prime_to_coq_prime euler_phi_prime_power euler_phi_coprime_multiplicative euler_phi_coprime_prime_power gcd_prime_power_one pow_mod_coprime_product_one_iff lcm_as_gcd_quotient_product exact_order_coprime_product_lcm order_lcm_runtime_formula order_search_positive ord_positive ord_non_coprime_counterexample cycle_term_nonnegative sum_nat_range_nonnegative_local walk_suffix_lists_nonnegative walk_suffix_nonnegative walk_suffix_lists_cons walk_suffix_zero_index walk_suffix_mismatched_left walk_suffix_mismatched_right gcd_stratum_preserved catches_all_contains_zero catches_all_hits_same_gcd_stratum)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
