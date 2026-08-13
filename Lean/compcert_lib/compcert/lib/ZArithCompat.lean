import compcert.lib.Coqlib

namespace Z

theorem divide_iff_dvd (a b : Int) : divide a b ↔ a ∣ b := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, Int.mul_comm q a⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, Int.mul_comm a q⟩

theorem abs_nonneg (a : Int) : 0 <= abs a := by
  exact Int.ofNat_zero_le _

theorem abs_eq_iff (a : Int) : abs a = a ↔ 0 <= a := by
  unfold abs
  constructor
  · intro h
    rw [← h]
    exact Int.ofNat_zero_le _
  · exact Int.ofNat_natAbs_of_nonneg

theorem abs_idemp (a : Int) : abs (abs a) = abs a := by
  exact (abs_eq_iff _).2 (abs_nonneg _)

theorem abs_neg (a : Int) : abs (-a) = abs a := by
  unfold abs
  rw [Int.natAbs_neg]

theorem abs_mul (a b : Int) : abs (a * b) = abs a * abs b := by
  unfold abs
  rw [Int.natAbs_mul]
  exact Int.natCast_mul _ _

theorem abs_sub_le (a b : Int) : abs (a - b) <= abs a + abs b := by
  unfold abs
  change Int.ofNat (a - b).natAbs <= Int.ofNat (a.natAbs + b.natAbs)
  exact Int.ofNat_le.mpr (Int.natAbs_sub_le a b)

theorem abs_le_iff (a bound : Int) :
    abs a <= bound ↔ -bound <= a ∧ a <= bound := by
  by_cases ha : 0 <= a
  · rw [abs_eq_iff a |>.2 ha]
    omega
  · have habs : abs a = -a := by
      unfold abs
      exact Int.ofNat_natAbs_of_nonpos (by omega)
    rw [habs]
    omega

theorem abs_lt_iff (a bound : Int) :
    abs a < bound ↔ -bound < a ∧ a < bound := by
  by_cases ha : 0 <= a
  · rw [abs_eq_iff a |>.2 ha]
    omega
  · have habs : abs a = -a := by
      unfold abs
      exact Int.ofNat_natAbs_of_nonpos (by omega)
    rw [habs]
    omega

theorem quot_0_l (a : Int) (_ha : a ≠ 0) : quot 0 a = 0 := by
  exact Int.zero_tdiv a

theorem quot_small_iff (a b : Int) (hb : b ≠ 0) :
    quot a b = 0 ↔ abs a < abs b := by
  unfold quot abs
  rw [← Int.natAbs_eq_zero, Int.natAbs_tdiv]
  constructor
  · intro h
    exact Int.ofNat_lt.mpr
      ((Nat.div_eq_zero_iff_lt (Int.natAbs_pos.mpr hb)).mp h)
  · intro h
    exact (Nat.div_eq_zero_iff_lt (Int.natAbs_pos.mpr hb)).mpr
      (Int.ofNat_lt.mp h)

theorem quot_le_lower_bound (a b q : Int) (hb : 0 < b)
    (h : b * q <= a) : q <= quot a b := by
  unfold quot
  have hmono := Int.tdiv_le_tdiv hb h
  rw [Int.mul_comm b q, Int.mul_tdiv_cancel q (Int.ne_of_gt hb)] at hmono
  exact hmono

theorem quot_lt_upper_bound (a b q : Int) (ha : 0 <= a) (hb : 0 < b)
    (h : a < b * q) : quot a b < q := by
  unfold quot
  apply Int.lt_of_not_ge
  intro hn
  have hmul : q * b <= a.tdiv b * b :=
    Int.mul_le_mul_of_nonneg_right hn (Int.le_of_lt hb)
  have hfloor : a.tdiv b * b <= a := by
    simpa [Int.mul_comm] using Int.mul_tdiv_self_le (k := b) ha
  have : b * q <= a := by simpa [Int.mul_comm] using Int.le_trans hmul hfloor
  exact (Int.not_le_of_gt h) this

theorem quot_le_upper_bound (a b q : Int) (hb : 0 < b)
    (h : a <= b * q) : quot a b <= q := by
  unfold quot
  have hmono := Int.tdiv_le_tdiv hb h
  rw [Int.mul_comm b q, Int.mul_tdiv_cancel q (Int.ne_of_gt hb)] at hmono
  exact hmono

theorem quot_pos (a b : Int) (ha : 0 <= a) (hb : 0 < b) :
    0 <= quot a b := by
  exact Int.tdiv_nonneg ha (Int.le_of_lt hb)

theorem quot_rem (a b : Int) (_hb : b ≠ 0) :
    a = b * quot a b + rem a b := by
  unfold quot rem
  exact (Int.mul_tdiv_add_tmod a b).symm

theorem quot_mul (a b : Int) (hb : b ≠ 0) : quot (a * b) b = a := by
  exact Int.mul_tdiv_cancel a hb

theorem quot_same (a : Int) (ha : a ≠ 0) : quot a a = 1 := by
  exact Int.tdiv_self ha

theorem quot_abs (a b : Int) (_hb : b ≠ 0) :
    quot (abs a) (abs b) = abs (quot a b) := by
  unfold quot abs
  change Int.ofNat (a.natAbs / b.natAbs) =
    Int.ofNat (Int.tdiv a b).natAbs
  exact Int.ofNat_inj.mpr (Int.natAbs_tdiv a b).symm

theorem rem_abs (a b : Int) (_hb : b ≠ 0) :
    rem (abs a) (abs b) = abs (rem a b) := by
  unfold rem abs
  change Int.ofNat (a.natAbs % b.natAbs) =
    Int.ofNat (Int.tmod a b).natAbs
  exact Int.ofNat_inj.mpr (Int.natAbs_tmod a b).symm

theorem rem_bound_abs (a b : Int) (hb : b ≠ 0) :
    abs (rem a b) < abs b := by
  unfold abs rem
  rw [Int.natAbs_tmod]
  exact Int.ofNat_lt.mpr (Nat.mod_lt _ (Int.natAbs_pos.mpr hb))

theorem rem_divide (a b : Int) (_hb : b ≠ 0) :
    rem a b = 0 ↔ divide b a := by
  unfold rem
  rw [divide_iff_dvd]
  exact Int.dvd_iff_tmod_eq_zero.symm

theorem divide_quot_mul_exact (a b c : Int) (_hb : b ≠ 0)
    (hdiv : divide b a) : quot (c * a) b = c * quot a b := by
  unfold quot
  rw [divide_iff_dvd] at hdiv
  exact Int.mul_tdiv_assoc c hdiv

theorem gcd_0_r (n : Int) : gcd n 0 = abs n := by
  unfold gcd abs
  rw [Int.gcd_zero]

theorem gcd_0_l (n : Int) : gcd 0 n = abs n := by
  unfold gcd abs
  rw [Int.gcd_zero_left]

theorem gcd_nonneg (a b : Int) : 0 <= gcd a b := by
  exact Int.ofNat_zero_le _

theorem gcd_divide_l (a b : Int) : divide (gcd a b) a := by
  rw [divide_iff_dvd]
  exact Int.gcd_dvd_left a b

theorem gcd_divide_r (a b : Int) : divide (gcd a b) b := by
  rw [divide_iff_dvd]
  exact Int.gcd_dvd_right a b

theorem gcd_eq_0_l (a b : Int) : gcd a b = 0 -> a = 0 := by
  intro h
  unfold gcd at h
  have hgcd : Int.gcd a b = 0 := Int.ofNat_inj.mp h
  exact (Int.gcd_eq_zero_iff.mp hgcd).1

theorem gcd_eq_0_r (a b : Int) : gcd a b = 0 -> b = 0 := by
  intro h
  unfold gcd at h
  have hgcd : Int.gcd a b = 0 := Int.ofNat_inj.mp h
  exact (Int.gcd_eq_zero_iff.mp hgcd).2

theorem gcd_rem (a b : Int) (_hb : b ≠ 0) :
    gcd (rem a b) b = gcd b a := by
  unfold gcd rem
  congr 1
  rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.gcd_eq_natAbs_gcd_natAbs,
    Int.natAbs_tmod]
  exact (Nat.gcd_rec b.natAbs a.natAbs).symm

theorem gcd_comm (n m : Int) : gcd n m = gcd m n := by
  unfold gcd
  rw [Int.gcd_comm]

theorem quot_le_compat_l (p q r : Int) (hp : 0 <= p)
    (hq : 0 < q) (hqr : q <= r) : quot p r <= quot p q := by
  unfold quot
  obtain ⟨pn, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨qn, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hq)
  obtain ⟨rn, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_trans (Int.le_of_lt hq) hqr)
  change Int.ofNat (pn / rn) <= Int.ofNat (pn / qn)
  exact Int.ofNat_le.mpr
    (Nat.div_le_div_left (Int.ofNat_le.mp hqr) (Int.natCast_pos.mp hq))

theorem rem_bound_pos_pos (x y : Int) (hy : 0 < y) (hx : 0 <= x) :
    0 <= rem x y ∧ rem x y < y := by
  unfold rem
  exact ⟨Int.tmod_nonneg y hx, Int.tmod_lt_of_pos x hy⟩

theorem rem_bound_neg_pos (x y : Int) (hy : y < 0) (hx : 0 <= x) :
    0 <= rem x y ∧ rem x y < -y := by
  unfold rem
  constructor
  · exact Int.tmod_nonneg y hx
  · have hlt := Int.tmod_lt_of_pos x (b := -y) (by omega)
    simpa using hlt

theorem rem_bound_pos_neg (x y : Int) (hy : 0 < y) (hx : x <= 0) :
    -y < rem x y ∧ rem x y <= 0 := by
  unfold rem
  constructor
  · exact Int.lt_tmod_of_pos x hy
  · have hnonneg := Int.tmod_nonneg y (show 0 <= -x by omega)
    have hneg := Int.neg_tmod x y
    omega

theorem rem_bound_neg_neg (x y : Int) (hy : y < 0) (hx : x <= 0) :
    y < rem x y ∧ rem x y <= 0 := by
  unfold rem
  constructor
  · have hlt := Int.lt_tmod_of_pos x (b := -y) (by omega)
    simpa using hlt
  · have hnonneg := Int.tmod_nonneg y (show 0 <= -x by omega)
    have hneg := Int.neg_tmod x y
    omega

end Z

namespace Zquot

theorem Zmult_rem_distr_r (a b c : Int) :
    Z.rem (a * c) (b * c) = Z.rem a b * c := by
  by_cases hcpos : 0 < c
  · simpa [Int.mul_comm] using Int.mul_tmod_mul_of_pos a b hcpos
  by_cases hcneg : c < 0
  · have hdiv : (a * c).tdiv (b * c) = a.tdiv b := by
      have h := Int.mul_tdiv_mul_of_pos_left a b (show 0 < -c by omega)
      simpa [Int.mul_neg] using h
    unfold Z.rem
    rw [Int.tmod_def, Int.tmod_def, hdiv, Int.sub_mul]
    ac_rfl
  · have hc : c = 0 := by omega
    simp [hc, Z.rem]

theorem Zquot_mult_cancel_r (a b c : Int) (hc : c ≠ 0) :
    Z.quot (a * c) (b * c) = Z.quot a b := by
  by_cases hcpos : 0 < c
  · exact Int.mul_tdiv_mul_of_pos_left a b hcpos
  · have hcneg : 0 < -c := by omega
    have h := Int.mul_tdiv_mul_of_pos_left a b hcneg
    simpa [Int.mul_neg] using h

theorem Z_quot_plus (a b c : Int) (_hsign : 0 <= (a + b * c) * a)
    (hc : c ≠ 0) : Z.quot (a + b * c) c = Z.quot a c + b := by
  unfold Z.quot
  by_cases ha0 : a = 0
  · subst a
    simpa using Int.mul_tdiv_cancel b hc
  by_cases ha : 0 < a
  · have hsum : 0 <= a + b * c := by
      by_cases hnonneg : 0 <= a + b * c
      · exact hnonneg
      · have hneg : a + b * c < 0 := by omega
        exact False.elim ((Int.not_le_of_gt
          (Int.mul_neg_of_neg_of_pos hneg ha)) _hsign)
    rw [Int.tdiv_eq_ediv_of_nonneg hsum, Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt ha)]
    exact Int.add_mul_ediv_right a b hc
  · have hale : a <= 0 := by omega
    have hsum : a + b * c <= 0 := by
      by_cases hnonpos : a + b * c <= 0
      · exact hnonpos
      · have hpos : 0 < a + b * c := by omega
        exact False.elim ((Int.not_le_of_gt
          (Int.mul_neg_of_pos_of_neg hpos (by omega))) _hsign)
    have hneg :
        (-a + (-b) * c).tdiv c = (-a).tdiv c + (-b) := by
      have hleft : 0 <= -a + (-b) * c := by
        have : -a + (-b) * c = -(a + b * c) := by
          simp [Int.neg_add, Int.neg_mul]
        omega
      rw [Int.tdiv_eq_ediv_of_nonneg hleft,
        Int.tdiv_eq_ediv_of_nonneg (Int.neg_nonneg_of_nonpos hale)]
      exact Int.add_mul_ediv_right (-a) (-b) hc
    rw [show -a + (-b) * c = -(a + b * c) by
          simp [Int.neg_add, Int.neg_mul],
      Int.neg_tdiv, Int.neg_tdiv] at hneg
    omega

end Zquot
