import AUXLib.Arithmetic

/- Reached Coq ZLcm slice for extended CRT. Keep the defining expression,
   including the absolute value and the zero/negative input behavior. -/
namespace Z

def Bezout (a b p : Int) : Prop := ∃ u v : Int, u*a + v*b = p

def lcm (a b : Int) : Int := abs (a * div b (gcd a b))

private theorem lcm_eq_native (a b : Int) : lcm a b = (Int.lcm a b : Int) := by
  unfold lcm abs div gcd
  simp only [Int.ofNat_eq_coe]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  rw [Int.natAbs_mul, Int.natAbs_ediv_of_dvd (Int.gcd_dvd_right a b)]
  simp only [Int.natAbs_natCast]
  rw [Int.lcm_eq_mul_div, Nat.mul_div_assoc a.natAbs (by
    simpa [Int.gcd_eq_natAbs_gcd_natAbs] using Nat.gcd_dvd_right a.natAbs b.natAbs)]

theorem divide_lcm_l (a b : Int) : divide a (lcm a b) := by
  rw [divide_iff_dvd, lcm_eq_native]
  exact Int.dvd_lcm_left a b

theorem divide_lcm_r (a b : Int) : divide b (lcm a b) := by
  rw [divide_iff_dvd, lcm_eq_native]
  exact Int.dvd_lcm_right a b

theorem lcm_least (a b c : Int) (ha : divide a c) (hb : divide b c) : divide (lcm a b) c := by
  rw [divide_iff_dvd, lcm_eq_native]
  exact Int.coe_lcm_dvd ((divide_iff_dvd _ _).mp ha) ((divide_iff_dvd _ _).mp hb)

theorem lcm_1_l_nonneg (n : Int) (hn : 0 ≤ n) : lcm 1 n = n := by
  rw [lcm_eq_native, Int.one_lcm]
  exact (Int.eq_natAbs_of_nonneg hn).symm

end Z
