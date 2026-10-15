import compcert.lib.ZArithCompat

namespace AUXLib

theorem rem_bounds (x m : Int) (hm : 0 < m) :
    -m < Z.rem x m ∧ Z.rem x m < m := by
  have h := Z.rem_bound_abs x m (by omega)
  rw [(Z.abs_eq_iff m).2 (by omega)] at h
  exact (Z.abs_lt_iff _ _).1 h

theorem rem_nonneg_bounds (x m : Int) (hx : 0 ≤ x) (hm : 0 < m) :
    0 ≤ Z.rem x m ∧ Z.rem x m < m :=
  Z.rem_bound_pos_pos x m hm hx

theorem rem_eq_mod (x m : Int) (hx : 0 ≤ x) (hm : 0 < m) :
    Z.rem x m = Z.modulo x m := by
  exact (Int.fmod_eq_tmod_of_nonneg hx (by omega)).symm

theorem bounded_product (a b m : Int) (hm : m ≤ 46341)
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m) :
    0 ≤ a*b ∧ a*b ≤ 2147483647 := by
  have h1 := Int.mul_le_mul_of_nonneg_right (show a ≤ 46340 by omega) hb.1
  have h2 := Int.mul_le_mul_of_nonneg_left (show b ≤ 46340 by omega) (show (0 : Int) ≤ 46340 by decide)
  exact ⟨Int.mul_nonneg ha.1 hb.1, by omega⟩

end AUXLib
