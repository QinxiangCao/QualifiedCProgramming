import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_foundations

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

theorem coq_mod_eq_iff (a b n : Int) (hb : 0≤b ∧ b<n) : a mod n=b ↔ (n ∣ᶻ a-b) := by
  have h : b.fmod n=b := Int.fmod_eq_of_lt hb.1 hb.2
  rw [Z.divide_iff_dvd, Int.dvd_iff_fmod_eq_zero]
  change a.fmod n=b ↔ (a-b).fmod n=0
  rw [← Int.fmod_eq_fmod_iff_fmod_sub_eq_zero, h]

namespace P090_OrbitOptimality

theorem sum_nat_range_ext (first count : Nat) (f g : Nat→Int) :
    (∀ k, (first≤k ∧ k<first+count) → f k=g k) → sum_nat_range first count f=sum_nat_range first count g := by
  induction count generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih =>
    intro h
    rw [sum_nat_range, sum_nat_range, h first ⟨le_refl _, by omega⟩, ih (first+1) (by intro k hk; exact h k ⟨by omega,by omega⟩)]

theorem sum_nat_range_mono (first count : Nat) (f g : Nat→Int) :
    (∀ k, (first≤k ∧ k<first+count) → f k≤g k) → sum_nat_range first count f≤sum_nat_range first count g := by
  induction count generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih =>
    intro h
    rw [sum_nat_range, sum_nat_range]
    exact add_le_add (h first ⟨le_refl _,by omega⟩) (ih (first+1) (by intro k hk; exact h k ⟨by omega,by omega⟩))

theorem sum_nat_range_app (first left right : Nat) (f : Nat→Int) :
    sum_nat_range first (left+right) f=sum_nat_range first left f+sum_nat_range (first+left) right f := by
  induction left generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih =>
    rw [Nat.succ_add, sum_nat_range, sum_nat_range, ih]
    have h : first+1+n=first+(n+1) := by omega
    simp only [Nat.succ_eq_add_one, h]
    omega

theorem euler_phi_prime_power_sum_nat (p : Int) (n : Nat) :
    IsPrime p → sum_nat_range 0 (Nat.succ n) (fun k=>EulerPhi (Z.pow p (Int.ofNat k)))=Z.pow p (Int.ofNat n) := by
  intro hp
  induction n with
  | zero => simp [sum_nat_range, Z.pow, EulerPhi, coprime_count, Z.gcd]
  | succ n ih =>
    change sum_nat_range 0 (Nat.succ n+1) (fun k=>EulerPhi (Z.pow p (Int.ofNat k)))=Z.pow p (Int.ofNat (n+1))
    rw [sum_nat_range_app, ih, Nat.zero_add]
    change Z.pow p (Int.ofNat n)+(EulerPhi (Z.pow p (Int.ofNat (n+1)))+0)=Z.pow p (Int.ofNat (n+1))
    have hne : 1≤Int.ofNat (n+1) := by simp only [Int.ofNat_eq_coe]; omega
    rw [euler_phi_prime_power p (Int.ofNat (n+1)) hp hne]
    have hs : Int.ofNat (n+1)-1=Int.ofNat n := by simp only [Int.ofNat_eq_coe,Nat.cast_add,Nat.cast_one]; omega
    rw [hs]
    simp only [Z.pow, pow_succ]
    ring

theorem euler_phi_prime_power_sum (p exponent : Int) :
    IsPrime p → 0≤exponent → sum_nat_range 0 (Nat.succ exponent.toNat) (fun k=>EulerPhi (Z.pow p (Int.ofNat k)))=Z.pow p exponent := by
  intro hp he
  have h := euler_phi_prime_power_sum_nat p exponent.toNat hp
  have hn : Int.ofNat exponent.toNat=exponent := by simpa using Int.toNat_of_nonneg he
  rw [hn] at h
  exact h

theorem cycle_term_le_euler_phi (x d : Int) : CycleTerm x d≤EulerPhi d := by
  unfold CycleTerm
  split
  · exact euler_phi_nonnegative d
  · have ho := ord_positive (x mod d) d
    change (EulerPhi d).fdiv (Ord (x mod d) d)≤EulerPhi d
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    exact Int.ediv_le_self _ (euler_phi_nonnegative d)

theorem walk_prime_power_budget (p exponent x : Int) :
    IsPrime p → 0≤exponent → (0≤walk_suffix_lists [p] [exponent] x 1 ∧ walk_suffix_lists [p] [exponent] x 1≤Z.pow p exponent) := by
  intro hp he
  refine ⟨walk_suffix_lists_nonnegative _ _ _ _,?_⟩
  change sum_nat_range 0 (Nat.succ exponent.toNat) (fun k=>CycleTerm x (1*Z.pow p (Int.ofNat k)))≤_
  rw [← euler_phi_prime_power_sum p exponent hp he]
  apply sum_nat_range_mono
  intro k hk
  simpa using cycle_term_le_euler_phi x (Z.pow p (Int.ofNat k))

theorem unit_orbit_return_iff (m x unit order exponent : Int) :
    2≤m → (0≤unit ∧ unit<m) → Z.gcd unit m=1 → 0≤exponent → ExactOrderCriterion x m order →
    ((unit*Z.pow x exponent) mod m=unit ↔ (order ∣ᶻ exponent)) := by
  rintro hm hu hg he ⟨ho,hc⟩
  rw [← hc exponent he, coq_mod_one_iff _ m (by omega), coq_mod_eq_iff _ unit m hu]
  simp only [Z.divide_iff_dvd]
  have hmul : unit*Z.pow x exponent-unit=unit*(Z.pow x exponent-1) := by ring
  rw [hmul]
  constructor
  · intro hd
    have hgn : Int.gcd m unit=1 := by simpa [Z.gcd,Int.gcd_comm] using hg
    have hh := (Int.dvd_gcd_mul_iff_dvd_mul).mpr hd
    simpa [hgn] using hh
  · exact fun hd=>dvd_mul_of_dvd_right hd unit

theorem unit_orbit_period (m x unit order time : Int) :
    2≤m → (0≤unit ∧ unit<m) → Z.gcd unit m=1 → 0≤time → ExactOrderCriterion x m order →
    (unit*Z.pow x (time+order)) mod m=(unit*Z.pow x time) mod m := by
  rintro hm hu hg ht ⟨ho,hc⟩
  have hp := (hc order (by omega)).mpr (show order ∣ᶻ order from ⟨1,by ring⟩)
  rw [coq_pow_add x time order ht (by omega), ← mul_assoc]
  change ((unit*Z.pow x time)*Z.pow x order).fmod m=(unit*Z.pow x time).fmod m
  rw [Int.mul_fmod]
  change ((unit*Z.pow x time).fmod m*(Z.pow x order mod m)).fmod m=_
  rw [hp,mul_one,Int.fmod_fmod]

theorem unit_orbit_no_early_return (m x unit order exponent : Int) :
    2≤m → (0≤unit ∧ unit<m) → Z.gcd unit m=1 → (0<exponent ∧ exponent<order) →
    ExactOrderCriterion x m order → (unit*Z.pow x exponent) mod m≠unit := by
  intro hm hu hg he hc hr
  have hd := (unit_orbit_return_iff m x unit order exponent hm hu hg (by omega) hc).mp hr
  have hle := Int.le_of_dvd he.1 ((Z.divide_iff_dvd _ _).mp hd)
  omega

theorem catches_all_hits_unit_orbit (m x : Int) (traps : List Int) (start : Int) :
    2≤m → Z.gcd x m=1 → CatchesAll m x traps → (0≤start ∧ start<m) → Z.gcd start m=1 →
    ∃ time room, 0≤time ∧ room=(start*Z.pow x time) mod m ∧ room∈traps ∧ Z.gcd room m=1 := by
  rintro hm hx ⟨_,_,hcatch⟩ hs hsg
  obtain ⟨t,r,ht,hr,hin⟩ := hcatch start hs
  refine ⟨t,r,ht,hr,hin,?_⟩
  rw [hr,gcd_stratum_preserved m x start t (by omega) ht hx,hsg]

end P090_OrbitOptimality
export P090_OrbitOptimality (sum_nat_range_ext sum_nat_range_mono sum_nat_range_app euler_phi_prime_power_sum_nat euler_phi_prime_power_sum cycle_term_le_euler_phi walk_prime_power_budget unit_orbit_return_iff unit_orbit_period unit_orbit_no_early_return catches_all_hits_unit_orbit)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
